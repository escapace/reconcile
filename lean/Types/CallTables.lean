/-!
# Per-call tables

Three per-call tables hold their entries in a cheaper form than a map or one list per field. Each
section models the earlier form as the reference and proves that the new one answers every lookup
the runtime makes as the reference does, over any sequence of the operations the runtime performs.

- The snapshot walk's reference memo (`SnapshotWalk.memoized` in `src/snapshot.ts`) holds the
  first observed object's reference in two fields and every later one in a map made when a second
  object is observed (`lazy_run_eq`).
- serialize's scalar and plain-layout tables (`scalar` and `layout` in
  `src/serialization/emit.ts`) hold -1 at an index without an id instead of leaving it absent, and
  grow to the index they read (`filled_run_eq`).
- deserialize's shape table (`checkShape` in `src/serialization/decode.ts`) holds each shape's
  offset, inheritance flag and key words as three consecutive entries of one list instead of one
  entry in each of three lists (`interleave_length`, `interleave_get`).
-/

namespace Reconcile.Types.CallTables

/-! ## The snapshot walk's reference memo -/

section Memo

variable {K : Type} [DecidableEq K]

/-- The memo the walk keeps: the first observed object's reference, and every later one in a map
made on the second, newest first. -/
structure Lazy (K : Type) where
  first : Option (K × Nat)
  rest : Option (List (K × Nat))

def Lazy.empty : Lazy K := ⟨none, none⟩

/-- `memoized`: the first object's reference, else the map's, if the map exists. -/
def Lazy.lookup (m : Lazy K) (k : K) : Option Nat :=
  match m.first with
  | some (k', v) => if k = k' then some v else (m.rest.getD []).lookup k
  | none => (m.rest.getD []).lookup k

/-- `observe`'s memo write: the reference numbered 0 goes to the two fields, every other to the
map. -/
def Lazy.insert (m : Lazy K) (k : K) (v : Nat) : Lazy K :=
  if v = 0 then { m with first := some (k, v) } else { m with rest := some ((k, v) :: m.rest.getD []) }

/-- One visit of a source: its memoized reference, or a new one numbered by the count. -/
def Lazy.visit (m : Lazy K) (count : Nat) (k : K) : Nat × Lazy K × Nat :=
  match m.lookup k with
  | some v => (v, m, count)
  | none => (count, m.insert k count, count + 1)

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

omit [DecidableEq K] in
theorem lookup_cons_ne [BEq K] [LawfulBEq K] {k k' : K} (v : Nat) (l : List (K × Nat))
    (h : k' ≠ k) : ((k, v) :: l).lookup k' = l.lookup k' := by
  simp [List.lookup, beq_eq_false_iff_ne.2 h]

/-- The two memos agree on every object, and the two fields stay free until the first insertion. -/
def MemoAgree (m : Lazy K) (p : List (K × Nat)) (count : Nat) : Prop :=
  (∀ k, m.lookup k = p.lookup k) ∧ (count = 0 → m.first = none)

theorem memoAgree_visit {m : Lazy K} {p : List (K × Nat)} {count : Nat} (k : K)
    (h : MemoAgree m p count) :
    (m.visit count k).1 = (plainVisit p count k).1 ∧
    (m.visit count k).2.2 = (plainVisit p count k).2.2 ∧
    MemoAgree (m.visit count k).2.1 (plainVisit p count k).2.1 (m.visit count k).2.2 := by
  obtain ⟨hl, hf⟩ := h
  unfold Lazy.visit plainVisit
  rw [hl k]
  cases hp : p.lookup k with
  | some v => exact ⟨rfl, rfl, hl, hf⟩
  | none =>
    refine ⟨rfl, rfl, ?_, by simp⟩
    intro k'
    have hk' := hl k'
    unfold Lazy.insert
    unfold Lazy.lookup at hk' ⊢
    by_cases hc : count = 0
    · subst hc
      rw [hf rfl] at hk'
      simp only [if_true]
      by_cases hkk : k' = k
      · subst hkk
        simp
      · simp only [hkk, if_false] at ⊢
        rw [lookup_cons_ne _ _ hkk, ← hk']
    · simp only [hc, if_false]
      by_cases hkk : k' = k
      · subst hkk
        have hm : ∀ e, m.first = some e → e.1 ≠ k' := by
          intro e he hek
          have := hl k'
          unfold Lazy.lookup at this
          rw [he, hp] at this
          obtain ⟨k1, v1⟩ := e
          simp only at hek
          subst hek
          simp at this
        cases hfirst : m.first with
        | none => simp
        | some e =>
          obtain ⟨k1, v1⟩ := e
          have hne : k' ≠ k1 := fun h => hm _ hfirst h.symm
          simp [hne]
      · rw [lookup_cons_ne _ _ hkk]
        cases hfirst : m.first with
        | none =>
          rw [hfirst] at hk'
          simp only [Option.getD_some]
          rw [lookup_cons_ne _ _ hkk]
          exact hk'
        | some e =>
          obtain ⟨k1, v1⟩ := e
          rw [hfirst] at hk'
          simp only [Option.getD_some]
          rw [lookup_cons_ne _ _ hkk]
          exact hk'

theorem memoAgree_run : ∀ (ks : List K) (m : Lazy K) (p : List (K × Nat)) (count : Nat),
    MemoAgree m p count → Lazy.run m count ks = plainRun p count ks
  | [], _, _, _, _ => rfl
  | k :: ks, m, p, count, h => by
    obtain ⟨hv, hc, hagree⟩ := memoAgree_visit k h
    simp only [Lazy.run, plainRun]
    rw [hv, memoAgree_run ks _ _ _ hagree, hc]

/-- The walk's memo returns the reference the earlier memo returned at every visit. -/
theorem lazy_run_eq (ks : List K) : Lazy.run Lazy.empty 0 ks = plainRun [] 0 ks :=
  memoAgree_run ks _ _ _ ⟨fun _ => rfl, fun _ => rfl⟩

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

end Reconcile.Types.CallTables
