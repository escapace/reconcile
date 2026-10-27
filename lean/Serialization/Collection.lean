import Mathlib.Data.List.Nodup
import Types.MapEntries

/-! Finite ordered collection reconstruction. Keys here are already canonical resolved
identities: native SameValueZero and fresh object handles are correspondence premises.
No source traversal or token validation is skipped when a key repeats.

Folding pairs into a Map keeps each key at its first position with its last value
(`first_insertion_order`, `last_value`), and folding members into a Set keeps each at its first
position. The decoders `decodeMap` and `decodeSet` are those folds of the resolved tokens when
every read succeeds (`decodeMap_rows`, `decodeSet_keys`), and the runtime's decoders, which
resolve every token before the first insertion, leave the target untouched on a failed read
(`resolved_map_rows`, `resolved_set_keys`) and read every occurrence (`resolved_map_trace`,
`resolved_set_trace`). -/
namespace SerializationCollection

variable {K V : Type} [DecidableEq K]

def remember (key : K) : List K → List K
  | [] => [key]
  | first :: rest => if key = first then first :: rest else first :: remember key rest

-- Inserting a pair is the built-in `Map.prototype.set`, `Types.MapEntries.put`.
export Reconcile.Types.MapEntries (put)

theorem keys_put (key : K) (value : V) (rows : List (K × V)) :
    (put key value rows).map Prod.fst = remember key (rows.map Prod.fst) := by
  induction rows with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨first, old⟩
    by_cases h : key = first <;> simp [put, remember, h, ih]

private theorem lookup_cons (query first : K) (value : V) (rest : List (K × V)) :
    ((first, value) :: rest).lookup query = if query = first then some value else rest.lookup query := by
  rw [List.lookup_cons]
  by_cases h : query = first
  · simp [h]
  · simp [h, beq_eq_false_iff_ne.mpr h]

theorem lookup_put (key query : K) (value : V) (rows : List (K × V)) :
    (put key value rows).lookup query = if query = key then some value else rows.lookup query := by
  induction rows with
  | nil => simp [put, lookup_cons]
  | cons pair rest ih =>
    rcases pair with ⟨first, old⟩
    by_cases h : key = first
    · subst key; by_cases q : query = first <;> simp [put, lookup_cons, q]
    · by_cases q : query = first
      · subst query; simp [put, h, Ne.symm h]
      · simp [put, lookup_cons, h, q, ih]

def foldMap (rows : List (K × V)) (entries : List (K × V)) : List (K × V) :=
  entries.foldl (fun result pair => put pair.1 pair.2 result) rows

def firstOrder (keys : List K) (incoming : List K) : List K :=
  incoming.foldl (fun result key => remember key result) keys

def lastValue (query : K) (initial : Option V) (entries : List (K × V)) : Option V :=
  entries.foldl (fun old pair => if query = pair.1 then some pair.2 else old) initial

theorem first_insertion_order (rows entries : List (K × V)) :
    (foldMap rows entries).map Prod.fst = firstOrder (rows.map Prod.fst) (entries.map Prod.fst) := by
  induction entries generalizing rows with
  | nil => rfl
  | cons pair rest ih =>
    simp only [foldMap, List.foldl_cons, List.map_cons, firstOrder] at *
    rw [ih, keys_put]

theorem last_value (query : K) (rows entries : List (K × V)) :
    (foldMap rows entries).lookup query = lastValue query (rows.lookup query) entries := by
  induction entries generalizing rows with
  | nil => rfl
  | cons pair rest ih =>
    simp only [foldMap, List.foldl_cons, lastValue] at *
    rw [ih, lookup_put]

-- The finite reader is deterministic over private transport tokens. Its failures
-- carry their identity code. The separate trace records every attempted read.
structure ReadTrace where
  reads : List Nat
  error : Option Nat
  deriving DecidableEq, Repr

structure MapResult where
  rows : List (Nat × Nat)
  trace : ReadTrace
  deriving DecidableEq, Repr

structure SetResult where
  keys : List Nat
  trace : ReadTrace
  deriving DecidableEq, Repr

def prepend (tokens : List Nat) (trace : ReadTrace) : ReadTrace :=
  ⟨tokens ++ trace.reads, trace.error⟩

def validate (read : Nat → Except Nat Nat) : List Nat → ReadTrace
  | [] => ⟨[], none⟩
  | token :: rest => match read token with
    | .error error => ⟨[token], some error⟩
    | .ok _ => prepend [token] (validate read rest)

def decodeMap (canonical : Nat → Nat) (read : Nat → Except Nat Nat)
    (rows : List (Nat × Nat)) : List (Nat × Nat) → MapResult
  | [] => ⟨rows, ⟨[], none⟩⟩
  | (keyToken, valueToken) :: rest => match read keyToken with
    | .error error => ⟨rows, ⟨[keyToken], some error⟩⟩
    | .ok key => match read valueToken with
      | .error error => ⟨rows, ⟨[keyToken, valueToken], some error⟩⟩
      | .ok value =>
        let result := decodeMap canonical read (put (canonical key) value rows) rest
        ⟨result.rows, prepend [keyToken, valueToken] result.trace⟩

def flatten (entries : List (Nat × Nat)) : List Nat :=
  entries.flatMap fun pair => [pair.1, pair.2]

/-- What a token resolves to when its read succeeds. -/
def resolved (read : Nat → Except Nat Nat) (token : Nat) : Nat :=
  match read token with
  | .ok value => value
  | .error _ => 0

theorem map_reads_every_occurrence (canonical : Nat → Nat) (read : Nat → Except Nat Nat)
    (rows entries : List (Nat × Nat)) :
    (decodeMap canonical read rows entries).trace = validate read (flatten entries) := by
  induction entries generalizing rows with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨key, value⟩
    cases hk : read key with
    | error error => simp [decodeMap, flatten, validate, hk]
    | ok decodedKey =>
      cases hv : read value with
      | error error => simp [decodeMap, flatten, validate, hk, hv, prepend]
      | ok decodedValue =>
        simp [decodeMap, flatten, validate, hk, hv, ih, prepend]

/-- When every read succeeds, the decoded rows are `foldMap` of the resolved pairs, so
`first_insertion_order` and `last_value` describe the decoded Map. -/
theorem decodeMap_rows (canonical : Nat → Nat) (read : Nat → Except Nat Nat) :
    ∀ (rows entries : List (Nat × Nat)), (validate read (flatten entries)).error = none →
      (decodeMap canonical read rows entries).rows =
        foldMap rows (entries.map fun pair => (canonical (resolved read pair.1), resolved read pair.2))
  | _, [], _ => rfl
  | rows, (key, value) :: rest, h => by
    cases hk : read key with
    | error error => simp [flatten, validate, hk] at h
    | ok decodedKey =>
      cases hv : read value with
      | error error => simp [flatten, validate, hk, hv, prepend] at h
      | ok decodedValue =>
        have hrest : (validate read (flatten rest)).error = none := by
          simpa [flatten, validate, hk, hv, prepend] using h
        simp only [decodeMap, hk, hv, List.map_cons, foldMap, List.foldl_cons, resolved]
        exact decodeMap_rows canonical read _ rest hrest

def decodeSet (canonical : Nat → Nat) (read : Nat → Except Nat Nat)
    (keys : List Nat) : List Nat → SetResult
  | [] => ⟨keys, ⟨[], none⟩⟩
  | token :: rest => match read token with
    | .error error => ⟨keys, ⟨[token], some error⟩⟩
    | .ok key =>
      let result := decodeSet canonical read (remember (canonical key) keys) rest
      ⟨result.keys, prepend [token] result.trace⟩

theorem set_reads_every_occurrence (canonical : Nat → Nat) (read : Nat → Except Nat Nat)
    (keys tokens : List Nat) :
    (decodeSet canonical read keys tokens).trace = validate read tokens := by
  induction tokens generalizing keys with
  | nil => rfl
  | cons token rest ih =>
    cases h : read token <;> simp [decodeSet, validate, h, ih]

/-- When every read succeeds, the decoded members are `firstOrder` of the resolved tokens, so
`firstOrder` describes the decoded Set. -/
theorem decodeSet_keys (canonical : Nat → Nat) (read : Nat → Except Nat Nat) :
    ∀ (keys tokens : List Nat), (validate read tokens).error = none →
      (decodeSet canonical read keys tokens).keys =
        firstOrder keys (tokens.map fun token => canonical (resolved read token))
  | _, [], _ => rfl
  | keys, token :: rest, h => by
    cases ht : read token with
    | error error => simp [validate, ht] at h
    | ok key =>
      have hrest : (validate read rest).error = none := by simpa [validate, ht, prepend] using h
      simp only [decodeSet, ht, List.map_cons, firstOrder, List.foldl_cons, resolved]
      exact decodeSet_keys canonical read _ rest hrest

-- The positional decoder resolves every slot of a collection before its first insertion, so
-- a failed occurrence leaves the destination untouched; on success it is the same fold.
def resolvedMap (canonical : Nat → Nat) (read : Nat → Except Nat Nat)
    (rows entries : List (Nat × Nat)) : MapResult :=
  match (validate read (flatten entries)).error with
  | some _ => ⟨rows, validate read (flatten entries)⟩
  | none => decodeMap canonical read rows entries

def resolvedSet (canonical : Nat → Nat) (read : Nat → Except Nat Nat)
    (keys tokens : List Nat) : SetResult :=
  match (validate read tokens).error with
  | some _ => ⟨keys, validate read tokens⟩
  | none => decodeSet canonical read keys tokens

theorem resolved_map_trace (canonical : Nat → Nat) (read : Nat → Except Nat Nat)
    (rows entries : List (Nat × Nat)) :
    (resolvedMap canonical read rows entries).trace = validate read (flatten entries) := by
  unfold resolvedMap
  split
  · rfl
  · exact map_reads_every_occurrence canonical read rows entries

/-- A failed read leaves the Map's rows untouched; otherwise they are `foldMap` of the resolved
pairs, with each key's first position and last value (`first_insertion_order`, `last_value`). -/
theorem resolved_map_rows (canonical : Nat → Nat) (read : Nat → Except Nat Nat)
    (rows entries : List (Nat × Nat)) :
    (resolvedMap canonical read rows entries).rows =
      match (validate read (flatten entries)).error with
      | some _ => rows
      | none => foldMap rows
          (entries.map fun pair => (canonical (resolved read pair.1), resolved read pair.2)) := by
  unfold resolvedMap
  split
  · rfl
  · rename_i h
    exact decodeMap_rows canonical read rows entries h

theorem resolved_set_trace (canonical : Nat → Nat) (read : Nat → Except Nat Nat)
    (keys tokens : List Nat) :
    (resolvedSet canonical read keys tokens).trace = validate read tokens := by
  unfold resolvedSet
  split
  · rfl
  · exact set_reads_every_occurrence canonical read keys tokens

/-- A failed read leaves the Set's members untouched; otherwise they are `firstOrder` of the
resolved tokens, each member at its first position. -/
theorem resolved_set_keys (canonical : Nat → Nat) (read : Nat → Except Nat Nat)
    (keys tokens : List Nat) :
    (resolvedSet canonical read keys tokens).keys =
      match (validate read tokens).error with
      | some _ => keys
      | none => firstOrder keys (tokens.map fun token => canonical (resolved read token)) := by
  unfold resolvedSet
  split
  · rfl
  · rename_i h
    exact decodeSet_keys canonical read keys tokens h

-- These inhabited witnesses reject duplicate rejection, first-value retention,
-- last-position movement, raw signed-zero equality, and skipping invalid values.
example : foldMap ([] : List (Nat × Nat)) [(1, 10), (2, 20), (1, 30)] =
    [(1, 30), (2, 20)] := by decide
example : firstOrder ([] : List Nat) [1, 2, 1] = [1, 2] := by decide
example : (decodeMap id (fun token => if token = 3 then .error 99 else .ok (token % 2))
    [] [(0, 1), (2, 3), (4, 5)]).trace = ⟨[0, 1, 2, 3], some 99⟩ := by decide
example : (decodeMap id (fun token => if token = 1 then .error 99 else .ok 0)
    [] [(0, 1), (2, 3)]).rows = [] := by decide
example : (resolvedMap id (fun token => if token = 3 then .error 99 else .ok (token % 2))
    [] [(0, 1), (2, 3), (4, 5)]) = ⟨[], ⟨[0, 1, 2, 3], some 99⟩⟩ := by decide
example : firstOrder ([] : List Nat) ([5, 6, 5].map fun key => if key = 5 then 6 else key) =
    [6] := by decide

end SerializationCollection
