/-!
# Path-compressed per-call shape trie

The active encoder interns record shapes in a path-compressed trie. A node's incoming edge
is a label `k :: rest` taken from the keys array of the shape that created it; children are
keyed by the label's first key. An unmatched suffix becomes one leaf, and a shape that
diverges or ends inside an edge splits that edge. Lookups that succeed change nothing.

This file proves the trie denotes exactly the finite map from key sequences to ids that the
signature memo maintains, so both assign identical first-occurrence ids. Keys have any type
with decidable equality (JavaScript property names are UTF-16 code-unit sequences).

Runtime premises, not proved here: trie nodes are fresh per call and reachable by one path,
so the in-place `Map.set` and edge split agree with the functional `setR` below; label slices
(`from`/`to` over a shared keys array) are never mutated; the next id is `shapes.length`;
`JSON.stringify` is injective on string arrays (for the previous signature memo).
-/

namespace SerializationShapeRadix

variable {κ : Type} [DecidableEq κ]

inductive Radix (κ : Type) where
  | node (id : Option Nat) (children : List (κ × List κ × Radix κ))

/-- The remainder of `query` after the prefix `label`, if `label` is a prefix. -/
def strip : List κ → List κ → Option (List κ)
  | [], query => some query
  | _ :: _, [] => none
  | l :: ls, k :: ks => if l = k then strip ls ks else none

theorem strip_some_iff (label query rest : List κ) :
    strip label query = some rest ↔ query = label ++ rest := by
  induction label generalizing query with
  | nil => simp [strip, eq_comm]
  | cons l ls ih =>
    cases query with
    | nil => simp [strip]
    | cons k ks =>
      by_cases h : l = k
      · subst h; simp [strip, ih]
      · simp [strip, h, Ne.symm h]

theorem strip_self_append (label rest : List κ) : strip label (label ++ rest) = some rest :=
  (strip_some_iff label (label ++ rest) rest).mpr rfl

theorem strip_length {label query rest : List κ} (h : strip label query = some rest) :
    rest.length ≤ query.length := by
  rw [strip_some_iff] at h
  subst h
  simp

def findR (k : κ) : List (κ × List κ × Radix κ) → Option (List κ × Radix κ)
  | [] => none
  | (k', ls, t) :: rest => if k' = k then some (ls, t) else findR k rest

def updateR (k : κ) (ls : List κ) (t : Radix κ) :
    List (κ × List κ × Radix κ) → List (κ × List κ × Radix κ)
  | [] => [(k, ls, t)]
  | (k', ls', t') :: rest =>
    if k' = k then (k, ls, t) :: rest else (k', ls', t') :: updateR k ls t rest

theorem findR_updateR_same (k : κ) (ls : List κ) (t : Radix κ) (cs : List (κ × List κ × Radix κ)) :
    findR k (updateR k ls t cs) = some (ls, t) := by
  induction cs with
  | nil => simp [updateR, findR]
  | cons head rest ih =>
    rcases head with ⟨k', ls', t'⟩
    by_cases h : k' = k <;> simp [updateR, findR, h, ih]

theorem findR_updateR_other {k other : κ} (ls : List κ) (t : Radix κ)
    (cs : List (κ × List κ × Radix κ)) (h : other ≠ k) :
    findR other (updateR k ls t cs) = findR other cs := by
  induction cs with
  | nil => simp [updateR, findR, Ne.symm h]
  | cons head rest ih =>
    rcases head with ⟨k', ls', t'⟩
    by_cases hk : k' = k
    · subst hk; simp [updateR, findR, Ne.symm h]
    · simp [updateR, findR, hk, ih]

def getR : Radix κ → List κ → Option Nat
  | .node id _, [] => id
  | .node _ cs, k :: ks =>
    match findR k cs with
    | none => none
    | some (ls, t) =>
      match h : strip ls ks with
      | none => none
      | some rest =>
        have : rest.length < (k :: ks).length := Nat.lt_succ_of_le (strip_length h)
        getR t rest
termination_by _ q => q.length

/-- The denotation of following an edge: strip its label, then look up in its subtree. -/
theorem getR_cons (id : Option Nat) (cs : List (κ × List κ × Radix κ)) (k : κ) (ks : List κ) :
    getR (.node id cs) (k :: ks) =
      match findR k cs with
      | none => none
      | some (ls, t) => (strip ls ks).bind (getR t) := by
  rw [getR]
  cases findR k cs with
  | none => rfl
  | some e =>
    rcases e with ⟨ls, t⟩
    simp only
    split <;> simp_all

/-- Length of the common prefix of a label and a query. -/
def common : List κ → List κ → Nat
  | l :: ls, k :: ks => if l = k then common ls ks + 1 else 0
  | _, _ => 0

theorem common_le (ls ks : List κ) : common ls ks ≤ ls.length := by
  induction ls generalizing ks with
  | nil => simp [common]
  | cons l ls ih => cases ks with
    | nil => simp [common]
    | cons k ks => by_cases h : l = k <;> simp [common, h, ih]

theorem take_common (ls ks : List κ) : ks.take (common ls ks) = ls.take (common ls ks) := by
  induction ls generalizing ks with
  | nil => simp [common]
  | cons l ls ih => cases ks with
    | nil => simp [common]
    | cons k ks => by_cases h : l = k <;> simp [common, h, ih]

theorem common_lt_of_strip_none {ls ks : List κ} (h : strip ls ks = none) :
    common ls ks < ls.length := by
  induction ls generalizing ks with
  | nil => simp [strip] at h
  | cons l ls ih => cases ks with
    | nil => simp [common]
    | cons k ks =>
      by_cases hl : l = k
      · subst hl; simp [strip] at h; simp [common, ih h]
      · simp [common, hl]

theorem strip_append (a m q : List κ) : strip (a ++ m) q = (strip a q).bind (strip m) := by
  induction a generalizing q with
  | nil => simp [strip]
  | cons l ls ih =>
    cases q with
    | nil => simp [strip]
    | cons k ks => by_cases h : l = k <;> simp [strip, h, ih]

/-- A node with one child edge `b :: c` denotes following that edge. -/
theorem getR_single (b : κ) (c : List κ) (t : Radix κ) (q : List κ) :
    getR (.node none [(b, c, t)]) q = (strip (b :: c) q).bind (getR t) := by
  cases q with
  | nil => simp [getR, strip]
  | cons x xs => by_cases h : b = x <;> simp [getR_cons, findR, strip, h]

/-- Splitting an edge `a ++ b :: c` into `a` and a middle node with edge `b :: c` preserves
the denotation of every query. -/
theorem getR_split (a : List κ) (b : κ) (c : List κ) (t : Radix κ) (q : List κ) :
    (strip a q).bind (getR (.node none [(b, c, t)])) = (strip (a ++ b :: c) q).bind (getR t) := by
  rw [strip_append]
  cases strip a q <;> simp [getR_single]

/-- Functional model of the runtime store: set the id for `keys`, creating a leaf for an
unmatched suffix and splitting an edge where `keys` diverges or ends inside it. -/
def setR : Radix κ → List κ → Nat → Radix κ
  | .node _ cs, [], v => .node (some v) cs
  | .node id cs, k :: ks, v =>
    match findR k cs with
    | none => .node id (updateR k ks (.node (some v) []) cs)
    | some (ls, t) =>
      match h : strip ls ks with
      | some rest =>
        have : rest.length < (k :: ks).length := Nat.lt_succ_of_le (strip_length h)
        .node id (updateR k ls (setR t rest v) cs)
      | none =>
        match ls.drop (common ls ks) with
        | [] => .node id cs
        | b :: c =>
          have : (ks.drop (common ls ks)).length < (k :: ks).length := by simp; omega
          .node id (updateR k (ls.take (common ls ks))
            (setR (.node none [(b, c, t)]) (ks.drop (common ls ks)) v) cs)
termination_by _ q => q.length

theorem getR_leaf (v : Nat) (q : List κ) :
    getR (.node (some v) [] : Radix κ) q = if q = [] then some v else none := by
  cases q <;> simp [getR_cons, findR, getR]

/-- Storing an id changes the denotation only at the stored key sequence. -/
theorem getR_setR (n : Nat) : ∀ (r : Radix κ) (p q : List κ) (v : Nat), p.length ≤ n →
    getR (setR r p v) q = if q = p then some v else getR r q := by
  induction n with
  | zero =>
    intro r p q v hn
    have : p = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rcases r with ⟨id, cs⟩
    cases q <;> simp [setR, getR, getR_cons]
  | succ n ih =>
    intro r p q v hn
    rcases r with ⟨id, cs⟩
    cases p with
    | nil => cases q <;> simp [setR, getR, getR_cons]
    | cons k ks =>
      have hks : ks.length ≤ n := by simp at hn; omega
      cases hf : findR k cs with
      | none =>
        cases q with
        | nil => simp [setR, hf, getR]
        | cons x xs =>
          by_cases hx : x = k
          · subst hx
            simp only [setR, hf, getR_cons, findR_updateR_same]
            cases hs : strip ks xs with
            | none =>
              have : xs ≠ ks := by
                intro e; subst e
                have h0 : strip xs xs = some [] := by simpa using strip_self_append xs []
                rw [h0] at hs; cases hs
              simp [this]
            | some rest =>
              rw [strip_some_iff] at hs
              subst hs
              by_cases hr : rest = [] <;> simp [hr, getR_leaf]
          · simp [setR, hf, getR_cons, findR_updateR_other _ _ _ hx, hx]
      | some e =>
        rcases e with ⟨ls, t⟩
        cases hs : strip ls ks with
        | some rest =>
          have hrest : rest.length ≤ n := Nat.le_trans (strip_length hs) hks
          rw [strip_some_iff] at hs
          subst hs
          have hset : setR (.node id cs) (k :: (ls ++ rest)) v =
              .node id (updateR k ls (setR t rest v) cs) := by
            rw [setR]; simp only [hf]; split
            · rename_i rest' heq; rw [strip_self_append] at heq; cases heq; rfl
            · rename_i heq; rw [strip_self_append] at heq; cases heq
          rw [hset]
          cases q with
          | nil => simp [getR]
          | cons x xs =>
            by_cases hx : x = k
            · subst hx
              rw [getR_cons, getR_cons, findR_updateR_same, hf]
              cases hq : strip ls xs with
              | none =>
                have : xs ≠ ls ++ rest := by
                  intro e; subst e; rw [strip_self_append] at hq; cases hq
                simp [hq, this]
              | some r' =>
                rw [strip_some_iff] at hq
                subst hq
                simp [strip_self_append, ih t rest r' v hrest]
            · simp [getR_cons, findR_updateR_other _ _ _ hx, hx]
        | none =>
          have hlt := common_lt_of_strip_none hs
          have htake := take_common ls ks
          obtain ⟨b, c, hbc⟩ : ∃ b c, ls.drop (common ls ks) = b :: c := by
            cases h : ls.drop (common ls ks) with
            | nil => simp at h; omega
            | cons b c => exact ⟨b, c, rfl⟩
          have hdrop : (ks.drop (common ls ks)).length ≤ n := by simp; omega
          have hset : setR (.node id cs) (k :: ks) v =
              .node id (updateR k (ls.take (common ls ks))
                (setR (.node none [(b, c, t)]) (ks.drop (common ls ks)) v) cs) := by
            rw [setR]; simp only [hf]; split
            · rename_i _ heq; rw [hs] at heq; cases heq
            · simp only [hbc]
          rw [hset]
          have hls : ls = ls.take (common ls ks) ++ b :: c := by
            rw [← hbc, List.take_append_drop]
          have hk : ks = ls.take (common ls ks) ++ ks.drop (common ls ks) := by
            rw [← htake, List.take_append_drop]
          generalize ls.take (common ls ks) = a at hls hk ⊢
          generalize ks.drop (common ls ks) = d at hdrop hk ⊢
          subst hk
          subst hls
          cases q with
          | nil => simp [getR]
          | cons x xs =>
            by_cases hx : x = k
            · subst hx
              rw [getR_cons, getR_cons, findR_updateR_same, hf]
              simp only
              cases hq : strip a xs with
              | none =>
                have hne : xs ≠ a ++ d := by
                  intro e; subst e; rw [strip_self_append] at hq; cases hq
                simp [hne, strip_append, hq]
              | some r =>
                rw [strip_some_iff] at hq
                subst hq
                rw [Option.bind_some, ih _ _ r v hdrop, strip_append, strip_self_append,
                  Option.bind_some, ← getR_single]
                by_cases hr : r = d
                · subst hr; simp
                · have : ¬(a ++ r = a ++ d) := fun e => hr (List.append_cancel_left e)
                  simp [hr, this]
            · simp [getR_cons, findR_updateR_other _ _ _ hx, hx]

/-- One runtime interning step: reuse the stored id or store the next table index. -/
def internR (r : Radix κ) (next : Nat) (keys : List κ) : Nat × Radix κ × Nat :=
  match getR r keys with
  | some id => (id, r, next)
  | none => (next, setR r keys next, next + 1)

def internMemo (m : List κ → Option Nat) (next : Nat) (keys : List κ) :
    Nat × (List κ → Option Nat) × Nat :=
  match m keys with
  | some id => (id, m, next)
  | none => (next, fun q => if q = keys then some next else m q, next + 1)

def runRadix : Radix κ → Nat → List (List κ) → List Nat
  | _, _, [] => []
  | r, next, keys :: rest =>
    let x := internR r next keys
    x.1 :: runRadix x.2.1 x.2.2 rest

def runMemo : (List κ → Option Nat) → Nat → List (List κ) → List Nat
  | _, _, [] => []
  | m, next, keys :: rest =>
    let x := internMemo m next keys
    x.1 :: runMemo x.2.1 x.2.2 rest

theorem radix_matches_memo (shapes : List (List κ)) :
    ∀ (r : Radix κ) (m : List κ → Option Nat) (next : Nat), (∀ q, getR r q = m q) →
      runRadix r next shapes = runMemo m next shapes := by
  induction shapes with
  | nil => intro _ _ _ _; rfl
  | cons keys rest ih =>
    intro r m next h
    simp only [runRadix, runMemo, internR, internMemo, h keys]
    cases hm : m keys with
    | some id => simp [ih r m next h]
    | none =>
      simp only
      congr 1
      apply ih
      intro q
      rw [getR_setR keys.length r keys q next (Nat.le_refl _), h]

def empty : Radix κ := .node none []

theorem getR_empty (q : List κ) : getR (empty : Radix κ) q = none := by
  cases q <;> simp [empty, getR, getR_cons, findR]

/-- The path-compressed trie assigns exactly the signature memo's first-occurrence ids. -/
theorem radix_matches_signature (shapes : List (List κ)) :
    runRadix (empty : Radix κ) 0 shapes = runMemo (fun _ => none) 0 shapes :=
  radix_matches_memo shapes empty _ 0 getR_empty

unseal getR setR in
example : runRadix (empty : Radix String) 0
    [["a", "b", "c"], ["a", "b"], ["a", "x"], ["a", "b", "c"], [], ["a"], ["a", "b"]] =
    [0, 1, 2, 0, 3, 4, 1] := by decide
unseal getR setR in
example : runRadix (empty : Radix (List UInt16)) 0 [[[0xD800]], [[0xD800], [0x61]], [[0xD800]]] =
    [0, 1, 0] := by decide

#print axioms strip_some_iff
#print axioms getR_split
#print axioms getR_setR
#print axioms radix_matches_memo
#print axioms radix_matches_signature

end SerializationShapeRadix
