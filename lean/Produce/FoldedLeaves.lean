import Mathlib.Logic.Relation

/-!
# Folded leaves

Identity restoration (`compileImmutable` in `src/restore-identities.ts`) registers each object
the result keeps. An unchanged subtree the result keeps whole is a fixed leaf; registering every
object inside it as its own fixed node costs a record, a storage and edges per object. Those
descendants are registered last, after every other node, and the result keeps each of them. This
module proves that, when no storage of theirs clashes with a node the result could keep, folding
them away gives the selector the same choices.

The original problem `p` has the registered nodes `0, …, n - 1` followed by the descendants
`n, …, n + m - 1` (`Folded`). The folded problem `q` keeps the registered nodes; each edge from a
descendant to a registered node moves to some registered fixed node, and each edge into a
descendant is dropped. A record, a node with a payload, never points at a descendant.

A node is unavailable when it reaches a record that cannot be reused. The two problems agree on
whether some fixed node is unavailable (`dead_iff`), and otherwise on each record (`record_iff`),
although a single fixed node can differ: the runtime moves a descendant's edges to the fixed node
that met it first. A mask keeps every fixed node, no unavailable node, the children of each kept
node and distinct storages (`Feasible`). The folded problem's masks are exactly the original's
with every descendant kept (`feasible_iff`), they keep `m` fewer nodes (`score_extend`), and they
agree with it on the registered nodes (`extend_lt`), so the ranked streams correspond.
-/

namespace Reconcile.FoldedLeaves

/-- An immutable selection problem: fixed nodes have no payload and are always kept; seeds are
the records that cannot be reused. -/
structure Problem where
  size : Nat
  fixed : Nat → Bool
  storage : Nat → Nat
  edges : Nat → List Nat
  seed : Nat → Bool

/-- A node reaches a seed through edges, so the result cannot keep it. -/
def Unavailable (p : Problem) (i : Nat) : Prop :=
  ∃ s, p.seed s = true ∧ Relation.ReflTransGen (fun a b => b ∈ p.edges a) i s

/-- Some fixed node is unavailable, so no mask keeps every fixed node. -/
def Dead (p : Problem) : Prop := ∃ i < p.size, p.fixed i = true ∧ Unavailable p i

/-- A mask the selector may choose. -/
def Feasible (p : Problem) (k : Nat → Bool) : Prop :=
  (∀ i < p.size, p.fixed i = true → k i = true) ∧
    (∀ i < p.size, k i = true → ¬ Unavailable p i) ∧
    (∀ i < p.size, k i = true → ∀ j ∈ p.edges i, k j = true) ∧
    ∀ i < p.size, ∀ j < p.size, i ≠ j → k i = true → k j = true → p.storage i ≠ p.storage j

/-- The original problem `p`, its folded problem `q`, and the `m` descendants after the `n`
registered nodes. -/
structure Folded (p q : Problem) (n m : Nat) : Prop where
  sizes : p.size = n + m ∧ q.size = n
  same : q.fixed = p.fixed ∧ q.storage = p.storage ∧ q.seed = p.seed
  /-- Seeds are records, among the registered nodes. -/
  seeds : ∀ s, p.seed s = true → s < n ∧ p.fixed s = false
  /-- Descendants are fixed. -/
  descendants : ∀ f, n ≤ f → f < n + m → p.fixed f = true
  /-- No edge leaves the problems' nodes. -/
  bounded : (∀ i, n + m ≤ i → p.edges i = []) ∧ (∀ i, n ≤ i → q.edges i = []) ∧
    ∀ i j, j ∈ p.edges i → j < n + m
  /-- A record keeps its edges, all to registered nodes. -/
  records : ∀ i < n, p.fixed i = false → q.edges i = p.edges i ∧ ∀ j ∈ p.edges i, j < n
  /-- A registered fixed node keeps its edges to registered nodes. -/
  kept : ∀ i < n, p.fixed i = true → ∀ j ∈ p.edges i, j < n → j ∈ q.edges i
  /-- Each edge of a registered fixed node in `q` is its own or a descendant's. -/
  moved : ∀ i < n, p.fixed i = true → ∀ j ∈ q.edges i,
    j < n ∧ (j ∈ p.edges i ∨ ∃ f, n ≤ f ∧ f < n + m ∧ j ∈ p.edges f)
  /-- Each edge from a descendant to a registered node is some registered fixed node's in `q`. -/
  owned : ∀ f, n ≤ f → f < n + m → ∀ j ∈ p.edges f, j < n →
    ∃ i < n, p.fixed i = true ∧ j ∈ q.edges i
  /-- A descendant's storage is distinct from every node the result could keep. -/
  storage : ∀ f, n ≤ f → f < n + m → ∀ j < n + m, j ≠ f →
    (p.fixed j = true ∨ ¬ Unavailable q j) → p.storage f ≠ p.storage j

variable {p q : Problem} {n m : Nat}

/-- A node unavailable in `p` makes some fixed node unavailable in `q`, or is a record that is
unavailable in `q` too. -/
theorem unavailable_p (h : Folded p q n m) {x : Nat} (hx : Unavailable p x) :
    Dead q ∨ (x < n ∧ p.fixed x = false ∧ Unavailable q x) := by
  obtain ⟨s, hs, hpath⟩ := hx
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl =>
    obtain ⟨hsn, hsf⟩ := h.seeds s hs
    exact Or.inr ⟨hsn, hsf, s, by rw [h.same.2.2]; exact hs, Relation.ReflTransGen.refl⟩
  | @head x y hxy _ ih =>
    rcases ih with hd | ⟨hyn, hyf, ⟨t, ht, hyt⟩⟩
    · exact Or.inl hd
    · have hreach : ∀ i, y ∈ q.edges i → Unavailable q i := fun i hi =>
        ⟨t, ht, Relation.ReflTransGen.head hi hyt⟩
      by_cases hxn : x < n
      · cases hxf : p.fixed x
        · exact Or.inr ⟨hxn, rfl, hreach x (by rw [(h.records x hxn hxf).1]; exact hxy)⟩
        · refine Or.inl ⟨x, by rw [h.sizes.2]; exact hxn, by rw [h.same.1]; exact hxf, ?_⟩
          exact hreach x (h.kept x hxn hxf y hxy hyn)
      · have hxm : x < n + m := by
          rcases Nat.lt_or_ge x (n + m) with hlt | hge
          · exact hlt
          · rw [h.bounded.1 x hge] at hxy
            simp at hxy
        obtain ⟨i, hin, hif, hyi⟩ := h.owned x (by omega) hxm y hxy hyn
        exact Or.inl ⟨i, by rw [h.sizes.2]; exact hin, by rw [h.same.1]; exact hif, hreach i hyi⟩

/-- A node unavailable in `q` makes some fixed node unavailable in `p`, or is a record that is
unavailable in `p` too. -/
theorem unavailable_q (h : Folded p q n m) {x : Nat} (hx : Unavailable q x) :
    Dead p ∨ (p.fixed x = false ∧ Unavailable p x) := by
  obtain ⟨s, hs, hpath⟩ := hx
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl =>
    rw [h.same.2.2] at hs
    exact Or.inr ⟨(h.seeds s hs).2, s, hs, Relation.ReflTransGen.refl⟩
  | @head x y hxy _ ih =>
    rcases ih with hd | ⟨_, ⟨t, ht, hyt⟩⟩
    · exact Or.inl hd
    · have hreach : ∀ i, y ∈ p.edges i → Unavailable p i := fun i hi =>
        ⟨t, ht, Relation.ReflTransGen.head hi hyt⟩
      have hxn : x < n := by
        rcases Nat.lt_or_ge x n with hlt | hge
        · exact hlt
        · rw [h.bounded.2.1 x hge] at hxy
          simp at hxy
      cases hxf : p.fixed x
      · exact Or.inr ⟨rfl, hreach x (by rw [← (h.records x hxn hxf).1]; exact hxy)⟩
      · rcases (h.moved x hxn hxf y hxy).2 with hy | ⟨f, hfn, hfm, hyf⟩
        · exact Or.inl ⟨x, by rw [h.sizes.1]; omega, hxf, hreach x hy⟩
        · exact Or.inl ⟨f, by rw [h.sizes.1]; exact hfm, h.descendants f hfn hfm, hreach f hyf⟩

/-- Some fixed node is unavailable in one problem exactly when in the other. -/
theorem dead_iff (h : Folded p q n m) : Dead p ↔ Dead q := by
  constructor
  · rintro ⟨x, -, hxf, hx⟩
    rcases unavailable_p h hx with hd | ⟨-, hf, -⟩
    · exact hd
    · simp [hxf] at hf
  · rintro ⟨x, -, hxf, hx⟩
    rcases unavailable_q h hx with hd | ⟨hf, -⟩
    · exact hd
    · rw [h.same.1] at hxf; simp [hxf] at hf

/-- Without an unavailable fixed node, a record is unavailable in one problem exactly when in
the other. -/
theorem record_iff (h : Folded p q n m) (hd : ¬ Dead p) {x : Nat} :
    Unavailable p x ↔ Unavailable q x := by
  constructor
  · intro hx
    rcases unavailable_p h hx with hq | ⟨-, -, hx'⟩
    · exact absurd ((dead_iff h).2 hq) hd
    · exact hx'
  · intro hx
    rcases unavailable_q h hx with hp | ⟨-, hx'⟩
    · exact absurd hp hd
    · exact hx'

/-- A folded mask keeps every descendant. -/
def extend (n : Nat) (k : Nat → Bool) (i : Nat) : Bool := if i < n then k i else true

theorem extend_lt (k : Nat → Bool) {i : Nat} (hi : i < n) : extend n k i = k i := by
  simp [extend, hi]

theorem extend_ge (k : Nat → Bool) {i : Nat} (hi : n ≤ i) : extend n k i = true := by
  simp [extend, Nat.not_lt.mpr hi]

/-- A feasible mask keeps every fixed node, so no fixed node is unavailable. -/
theorem Feasible.not_dead {p : Problem} {k : Nat → Bool} (hk : Feasible p k) : ¬ Dead p :=
  fun ⟨i, hi, hif, hu⟩ => hk.2.1 i hi (hk.1 i hi hif) hu

/-- The folded problem's masks are exactly the original's with every descendant kept. -/
theorem feasible_iff (h : Folded p q n m) (k : Nat → Bool) :
    Feasible q k ↔ Feasible p (extend n k) := by
  have hp := h.sizes.1
  have hq := h.sizes.2
  constructor
  · intro hk
    have hdq := hk.not_dead
    have hdp : ¬ Dead p := fun hd => hdq ((dead_iff h).1 hd)
    -- A kept node of `p` is not unavailable in `q`, nor in `p`.
    have havail : ∀ j < n + m, extend n k j = true → ¬ Unavailable p j := by
      intro j hj hkj hu
      by_cases hjn : j < n
      · exact hk.2.1 j (by omega) (by rwa [extend_lt k hjn] at hkj) ((record_iff h hdp).1 hu)
      · exact hdp ⟨j, by omega, h.descendants j (by omega) hj, hu⟩
    refine ⟨fun i hi hif => ?_, fun i hi hki => havail i (by omega) hki, fun i hi hki j hj => ?_,
      fun i hi j hj hij hki hkj => ?_⟩
    · by_cases hin : i < n
      · rw [extend_lt k hin]; exact hk.1 i (by omega) (by rw [h.same.1]; exact hif)
      · exact extend_ge k (by omega)
    · have hjm := h.bounded.2.2 i j hj
      by_cases hjn : j < n
      · rw [extend_lt k hjn]
        by_cases hin : i < n
        · rw [extend_lt k hin] at hki
          cases hif : p.fixed i
          · exact hk.2.2.1 i (by omega) hki j (by rw [(h.records i hin hif).1]; exact hj)
          · exact hk.2.2.1 i (by omega) hki j (h.kept i hin hif j hj hjn)
        · obtain ⟨i', hi'n, hi'f, hji'⟩ := h.owned i (by omega) (by omega) j hj hjn
          exact hk.2.2.1 i' (by omega) (hk.1 i' (by omega) (by rw [h.same.1]; exact hi'f)) j hji'
      · exact extend_ge k (by omega)
    · by_cases hin : i < n
      · by_cases hjn : j < n
        · rw [extend_lt k hin] at hki; rw [extend_lt k hjn] at hkj
          have := hk.2.2.2 i (by omega) j (by omega) hij hki hkj
          rwa [h.same.2.1] at this
        · intro heq
          refine h.storage j (by omega) (by omega) i (by omega) hij ?_ heq.symm
          rw [extend_lt k hin] at hki
          exact Or.inr (hk.2.1 i (by omega) hki)
      · refine h.storage i (by omega) (by omega) j (by omega) hij.symm ?_
        by_cases hjn : j < n
        · rw [extend_lt k hjn] at hkj
          exact Or.inr (hk.2.1 j (by omega) hkj)
        · exact Or.inl (h.descendants j (by omega) (by omega))
  · intro hk
    have hdp := hk.not_dead
    refine ⟨fun i hi hif => ?_, fun i hi hki hu => ?_, fun i hi hki j hj => ?_,
      fun i hi j hj hij hki hkj => ?_⟩
    · have := hk.1 i (by omega) (by rw [← h.same.1]; exact hif)
      rwa [extend_lt k (by omega)] at this
    · exact hk.2.1 i (by omega) (by rwa [extend_lt k (by omega)]) ((record_iff h hdp).2 hu)
    · have hin : i < n := by omega
      have hki' : extend n k i = true := by rwa [extend_lt k hin]
      cases hif : p.fixed i
      · rw [(h.records i hin hif).1] at hj
        have := hk.2.2.1 i (by omega) hki' j hj
        rwa [extend_lt k ((h.records i hin hif).2 j hj)] at this
      · obtain ⟨hjn, hj'⟩ := h.moved i hin hif j hj
        rcases hj' with hj' | ⟨f, hfn, hfm, hjf⟩
        · have := hk.2.2.1 i (by omega) hki' j hj'
          rwa [extend_lt k hjn] at this
        · have := hk.2.2.1 f (by omega) (extend_ge k hfn) j hjf
          rwa [extend_lt k hjn] at this
    · have := hk.2.2.2 i (by omega) j (by omega) hij (by rwa [extend_lt k (by omega)])
        (by rwa [extend_lt k (by omega)])
      rwa [← h.same.2.1] at this

/-- The number of nodes a mask keeps among the first `size`. -/
def score (size : Nat) (k : Nat → Bool) : Nat := ((List.range size).filter (k ·)).length

/-- A folded mask keeps the `m` descendants besides its own nodes, so ranking by score is
unchanged. -/
theorem score_extend (n m : Nat) (k : Nat → Bool) :
    score (n + m) (extend n k) = score n k + m := by
  induction m with
  | zero =>
    simp only [score, Nat.add_zero]
    congr 1
    apply List.filter_congr
    intro i hi
    rw [extend_lt k (List.mem_range.mp hi)]
  | succ m ih =>
    simp only [score] at ih ⊢
    rw [← Nat.add_assoc, List.range_succ, List.filter_append, List.length_append, ih]
    simp [extend_ge k (Nat.le_add_right n m)]
    omega

/-- A descendant sharing storage 0 with the record 0. -/
def clash : Problem :=
  { size := 2, fixed := fun i => i == 1, storage := fun _ => 0, edges := fun _ => [],
    seed := fun _ => false }

/-- Keeping the record and the descendant that shares its storage is not a choice the selector
may make, which is why the runtime rejects a folded problem whose descendant's storage clashes
with a node it could keep. -/
example : ¬ Feasible clash (extend 1 (fun _ => true)) := fun hf =>
  hf.2.2.2 0 (by decide) 1 (by decide) (by decide) rfl rfl rfl

end Reconcile.FoldedLeaves
