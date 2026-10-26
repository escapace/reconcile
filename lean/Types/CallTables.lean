/-!
# Per-call tables

Three per-call tables hold their entries in a cheaper form than a map or one list per field. Each
section models the earlier form as the reference and proves that the new one answers every lookup
the runtime makes as the reference does, over any sequence of the operations the runtime performs.

- The snapshot walk's reference memo (`SnapshotWalk.memoized` in `src/snapshot.ts`) holds the
  first observed object's reference in two fields, which the root's visit fills without a lookup,
  and makes its map, holding that reference, at the first lookup after it (`lazy_run_eq`).
- serialize's scalar and plain-layout tables (`scalar` and `layout` in
  `src/serialization/emit.ts`) hold -1 at an index without an id instead of leaving it absent, and
  grow to the index they read (`filled_run_eq`).
- deserialize's shape table (`checkShape` in `src/serialization/decode.ts`) holds each shape's
  offset, inheritance flag and key words as three consecutive entries of one list instead of one
  entry in each of three lists (`interleave_length`, `interleave_get`).
- serialize's payload rows (`push` in `src/serialization/emit.ts`) take each value at the row's
  count, in a row made at its final length or grown as values arrive, instead of by `push`
  (`fill_row`, `fill_empty`).
-/

namespace Reconcile.Types.CallTables

/-! ## The snapshot walk's reference memo -/

section Memo

variable {K : Type} [DecidableEq K]

/-- The memo the walk keeps: the first observed object's reference, and the map made at the first
lookup after it, holding that reference and every later one, newest first. -/
structure Lazy (K : Type) where
  first : Option (K × Nat)
  rest : Option (List (K × Nat))

def Lazy.empty : Lazy K := ⟨none, none⟩

/-- The map a lookup reads: the map, or one made holding the first object's reference. -/
def Lazy.table (m : Lazy K) : List (K × Nat) := m.rest.getD m.first.toList

/-- One visit of a source. The first, the root, takes no lookup: nothing is memoized yet. Every
other looks the source up in the map, made if absent, and returns its reference or a new one
numbered by the count. -/
def Lazy.visit (m : Lazy K) (count : Nat) (k : K) : Nat × Lazy K × Nat :=
  if count = 0 then (0, { m with first := some (k, 0) }, 1)
  else
    match m.table.lookup k with
    | some v => (v, { m with rest := some m.table }, count)
    | none => (count, { m with rest := some ((k, count) :: m.table) }, count + 1)

/-- The same visit with the earlier memo, one map for every object. -/
def plainVisit (m : List (K × Nat)) (count : Nat) (k : K) : Nat × List (K × Nat) × Nat :=
  match m.lookup k with
  | some v => (v, m, count)
  | none => (count, (k, count) :: m, count + 1)

/-- The references a sequence of visits returns. -/
def Lazy.run : Lazy K → Nat → List K → List Nat
  | _, _, [] => []
  | m, count, k :: ks =>
    (m.visit count k).1 :: Lazy.run (m.visit count k).2.1 (m.visit count k).2.2 ks

def plainRun : List (K × Nat) → Nat → List K → List Nat
  | _, _, [] => []
  | m, count, k :: ks =>
    (plainVisit m count k).1 :: plainRun (plainVisit m count k).2.1 (plainVisit m count k).2.2 ks

/-- Before the root both memos are empty; after it, every lookup reads the earlier memo's map. -/
def MemoAgree (m : Lazy K) (p : List (K × Nat)) (count : Nat) : Prop :=
  (count = 0 → m = Lazy.empty ∧ p = []) ∧ (count ≠ 0 → m.table = p)

theorem memoAgree_visit {m : Lazy K} {p : List (K × Nat)} {count : Nat} (k : K)
    (h : MemoAgree m p count) :
    (m.visit count k).1 = (plainVisit p count k).1 ∧
    (m.visit count k).2.2 = (plainVisit p count k).2.2 ∧
    MemoAgree (m.visit count k).2.1 (plainVisit p count k).2.1 (m.visit count k).2.2 := by
  obtain ⟨hz, hs⟩ := h
  unfold Lazy.visit plainVisit
  by_cases hc : count = 0
  · obtain ⟨rfl, rfl⟩ := hz hc
    subst hc
    simp [MemoAgree, Lazy.table, Lazy.empty]
  · simp only [hc, if_false]
    rw [hs hc]
    cases hl : p.lookup k with
    | some v => exact ⟨rfl, rfl, fun h => absurd h hc, fun _ => by simp [Lazy.table]⟩
    | none => exact ⟨rfl, rfl, fun h => absurd h (Nat.succ_ne_zero _), fun _ => by simp [Lazy.table]⟩

theorem memoAgree_run : ∀ (ks : List K) (m : Lazy K) (p : List (K × Nat)) (count : Nat),
    MemoAgree m p count → Lazy.run m count ks = plainRun p count ks
  | [], _, _, _, _ => rfl
  | k :: ks, m, p, count, h => by
    obtain ⟨hv, hc, hagree⟩ := memoAgree_visit k h
    simp only [Lazy.run, plainRun]
    rw [hv, memoAgree_run ks _ _ _ hagree, hc]

/-- The walk's memo returns the reference the earlier memo returned at every visit. -/
theorem lazy_run_eq (ks : List K) : Lazy.run Lazy.empty 0 ks = plainRun [] 0 ks :=
  memoAgree_run ks _ _ _ ⟨fun _ => ⟨rfl, rfl⟩, fun h => absurd rfl h⟩

-- A root that holds itself: the first lookup makes the map from the root's reference and finds it.
example : Lazy.run (K := Nat) Lazy.empty 0 [7, 7, 8, 7] = [0, 0, 1, 0] := by decide

end Memo

/-! ## serialize's sentinel-filled tables -/

section Filled

/-- The table before: the id at each index, if one was assigned. -/
abbrev Sparse := Nat → Option Nat

/-- `table[k] ??= fresh`: the id at `k`, assigning `fresh` when there is none. -/
def sparseIntern (t : Sparse) (k fresh : Nat) : Nat × Sparse :=
  match t k with
  | some id => (id, t)
  | none => (fresh, fun i => if i = k then some fresh else t i)

/-- The id a filled table holds at an index: none for -1 or an index past its end. -/
def decode (t : List Int) (i : Nat) : Option Nat :=
  match t[i]? with
  | some x => if x < 0 then none else some x.toNat
  | none => none

/-- The table grown with -1 up to index `k`. -/
def pad (t : List Int) (k : Nat) : List Int := t ++ List.replicate (k + 1 - t.length) (-1)

/-- The table now: grown to `k`, then the id at `k`, assigning `fresh` where it holds -1. -/
def filledIntern (t : List Int) (k fresh : Nat) : Nat × List Int :=
  let t' := pad t k
  match t'[k]? with
  | some x => if x < 0 then (fresh, t'.set k fresh) else (x.toNat, t')
  | none => (fresh, t')

theorem decode_pad (t : List Int) (k : Nat) : decode (pad t k) = decode t := by
  funext i
  unfold decode pad
  rcases Nat.lt_or_ge i t.length with h | h
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_append_right h, List.getElem?_eq_none h, List.getElem?_replicate]
    by_cases hi : i - t.length < k + 1 - t.length <;> simp [hi]

theorem pad_length (t : List Int) (k : Nat) : k < (pad t k).length := by
  simp [pad]
  omega

theorem filledIntern_eq (t : List Int) (s : Sparse) (h : decode t = s) (k fresh : Nat) :
    (filledIntern t k fresh).1 = (sparseIntern s k fresh).1 ∧
    decode (filledIntern t k fresh).2 = (sparseIntern s k fresh).2 := by
  have hpad := decode_pad t k
  have hlen := pad_length t k
  have hk : decode (pad t k) k = s k := by rw [hpad, h]
  unfold filledIntern sparseIntern
  simp only
  rw [List.getElem?_eq_getElem hlen] at ⊢
  unfold decode at hk
  rw [List.getElem?_eq_getElem hlen] at hk
  by_cases hneg : (pad t k)[k] < 0
  · simp only [hneg, if_true] at hk ⊢
    rw [← hk]
    refine ⟨rfl, ?_⟩
    funext i
    by_cases hik : i = k
    · subst hik
      simp [decode, hlen]
    · have := congrFun hpad i
      rw [h] at this
      simp only [decode, List.getElem?_set, Ne.symm hik, if_false, hik] at this ⊢
      exact this
  · simp only [hneg, if_false] at hk ⊢
    rw [← hk]
    exact ⟨rfl, by rw [hpad, h]⟩

/-- The ids a sequence of lookups returns, each with the id it would assign. -/
def filledRun : List Int → List (Nat × Nat) → List Nat
  | _, [] => []
  | t, (k, fresh) :: rest => (filledIntern t k fresh).1 :: filledRun (filledIntern t k fresh).2 rest

def sparseRun : Sparse → List (Nat × Nat) → List Nat
  | _, [] => []
  | s, (k, fresh) :: rest => (sparseIntern s k fresh).1 :: sparseRun (sparseIntern s k fresh).2 rest

theorem filledRun_eq : ∀ (steps : List (Nat × Nat)) (t : List Int) (s : Sparse), decode t = s →
    filledRun t steps = sparseRun s steps
  | [], _, _, _ => rfl
  | (k, fresh) :: rest, t, s, h => by
    obtain ⟨h1, h2⟩ := filledIntern_eq t s h k fresh
    simp only [filledRun, sparseRun]
    rw [h1, filledRun_eq rest _ _ h2]

/-- A table filled with -1, as the scalar table starts, or empty, as a key table starts, answers
every lookup as an empty sparse table. -/
theorem filled_run_eq (n : Nat) (steps : List (Nat × Nat)) :
    filledRun (List.replicate n (-1)) steps = sparseRun (fun _ => none) steps := by
  apply filledRun_eq
  funext i
  unfold decode
  rw [List.getElem?_replicate]
  by_cases hi : i < n <;> simp [hi]

end Filled

/-! ## deserialize's shape table -/

section Shapes

/-- The shapes' offset, inheritance flag and key words, three consecutive entries per shape. -/
def interleave (shapes : List (Nat × Bool × Nat)) : List Nat :=
  shapes.flatMap fun (offset, inherits, words) => [offset, if inherits then 1 else 0, words]

theorem interleave_length (shapes : List (Nat × Bool × Nat)) :
    (interleave shapes).length = 3 * shapes.length := by
  induction shapes with
  | nil => rfl
  | cons s ss ih =>
    simp only [interleave, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    rw [ih]
    omega

/-- Shape `j`'s entries sit at `3 * j`, `3 * j + 1` and `3 * j + 2`, the second 1 exactly when a
key of the shape is one `Object.prototype` holds. -/
theorem interleave_get : ∀ (shapes : List (Nat × Bool × Nat)) (j : Nat) (h : j < shapes.length),
    (interleave shapes)[3 * j]? = some shapes[j].1 ∧
    (interleave shapes)[3 * j + 1]? = some (if shapes[j].2.1 then 1 else 0) ∧
    (interleave shapes)[3 * j + 2]? = some shapes[j].2.2
  | [], _, h => absurd h (by simp)
  | s :: ss, 0, _ => by simp [interleave]
  | s :: ss, j + 1, h => by
    have ih := interleave_get ss j (by simpa using h)
    have e : ∀ r, 3 * (j + 1) + r = 3 + (3 * j + r) := fun r => by omega
    simp only [interleave, List.flatMap_cons] at ih ⊢
    refine ⟨?_, ?_, ?_⟩
    · rw [show 3 * (j + 1) = 3 + 3 * j by omega, List.getElem?_append_right (by simp)]
      simpa using ih.1
    · rw [e 1, List.getElem?_append_right (by simp)]
      simpa using ih.2.1
    · rw [e 2, List.getElem?_append_right (by simp)]
      simpa using ih.2.2

end Shapes

/-! ## serialize's payload rows -/

section Rows

variable {α : Type}

/-- `push`'s write: the value at the row's count, which a row made at its final length holds as a
placeholder, or appended when the row has no slot there. -/
def write (row : List α) (count : Nat) (v : α) : List α :=
  if count < row.length then row.set count v else row ++ [v]

/-- The row and count after writing `vs` in order. -/
def fill (row : List α) (count : Nat) : List α → List α × Nat
  | [] => (row, count)
  | v :: vs => fill (write row count v) (count + 1) vs

/-- Writing after the values `p` already written, into a row made with `n` placeholders, leaves
the values written so far followed by the placeholders not yet reached. -/
theorem fill_prefix (d : α) (n : Nat) : ∀ (vs p : List α),
    fill (p ++ List.replicate (n - p.length) d) p.length vs =
      (p ++ vs ++ List.replicate (n - p.length - vs.length) d, p.length + vs.length)
  | [], p => by simp [fill]
  | v :: vs, p => by
    have step : write (p ++ List.replicate (n - p.length) d) p.length v =
        (p ++ [v]) ++ List.replicate (n - (p ++ [v]).length) d := by
      unfold write
      by_cases h : p.length < n
      · have hn : n - p.length = (n - (p.length + 1)) + 1 := by omega
        rw [if_pos (by simp; omega), hn, List.replicate_succ, List.set_append_right _ _ (by omega)]
        simp
      · rw [if_neg (by simp; omega), show n - p.length = 0 by omega,
          show n - (p ++ [v]).length = 0 by simp; omega]
        simp
    simp only [fill]
    rw [step, show p.length + 1 = (p ++ [v]).length by simp, fill_prefix d n vs (p ++ [v])]
    have hk : n - (p ++ [v]).length - vs.length = n - p.length - (v :: vs).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [hk]
    refine Prod.ext ?_ ?_
    · simp
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-- A row made at its final length, as a short record's is, ends holding exactly its values, and
its count is the length a pushed row would have. -/
theorem fill_row (d : α) (vs : List α) :
    fill (List.replicate vs.length d) 0 vs = (vs, vs.length) := by
  simpa using fill_prefix d vs.length vs []

/-- A row that starts empty grows by the same writes into the pushed row. -/
theorem fill_empty : ∀ vs : List α, fill [] 0 vs = (vs, vs.length)
  | [] => rfl
  | v :: vs => by simpa using fill_prefix v 0 (v :: vs) []

end Rows

end Reconcile.Types.CallTables
