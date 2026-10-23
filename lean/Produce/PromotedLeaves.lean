import Produce.FoldedLeaves

/-!
# Promoted leaves

Discovery keeps an unchanged object that the probe settled as a fixed leaf. Before, only an
object backed by `current` was kept this way; an object the recipe inserted unchanged became a
record, read and checked again, though its check could only pass. This module, in
`FoldedLeaves`' problem, promotes such a record `r` to a fixed node. `r` is no seed and reaches
none (`available`), and every node it reaches has a storage of its own (`storage`), which the
runtime's conflict check enforces before it trusts the promoted problem.

The promoted problem's masks are exactly the original's that keep `r` (`feasible_iff`), and every
mask of the original with the highest score keeps `r` (`best_keeps`), so the selector's best
choices are unchanged. The fallback after a mask that cannot be built is the sealed pass, which
promotes nothing.
-/

namespace Reconcile.PromotedLeaves

open Reconcile.FoldedLeaves

/-- `q` is `p` with the record `r` promoted to a fixed node. -/
structure Promoted (p q : Problem) (r : Nat) : Prop where
  bound : r < p.size
  same : q.size = p.size ∧ q.storage = p.storage ∧ q.edges = p.edges ∧ q.seed = p.seed
  fixed : q.fixed r = true ∧ ∀ i, i ≠ r → q.fixed i = p.fixed i
  record : p.fixed r = false
  available : ¬ Unavailable p r
  edges : ∀ i j, j ∈ p.edges i → j < p.size
  storage : ∀ j, Relation.ReflTransGen (fun a b => b ∈ p.edges a) r j →
    ∀ i < p.size, i ≠ j → p.storage i ≠ p.storage j

variable {p q : Problem} {r : Nat}

theorem unavailable_iff (h : Promoted p q r) (i : Nat) : Unavailable q i ↔ Unavailable p i := by
  unfold Unavailable
  rw [h.same.2.2.1, h.same.2.2.2]

/-- The promoted problem's masks are the original's that keep `r`. -/
theorem feasible_iff (h : Promoted p q r) (k : Nat → Bool) :
    Feasible q k ↔ Feasible p k ∧ k r = true := by
  have hs := h.same.1
  have hb := h.bound
  constructor
  · rintro ⟨hf, hu, hc, hd⟩
    refine ⟨⟨fun i hi hpf => ?_, fun i hi hk => ?_, fun i hi hk j hj => ?_,
      fun i hi j hj hij hki hkj => ?_⟩, hf r (by omega) h.fixed.1⟩
    · by_cases hir : i = r
      · subst hir; simp [h.record] at hpf
      · exact hf i (by omega) (by rw [h.fixed.2 i hir]; exact hpf)
    · rw [← unavailable_iff h]; exact hu i (by omega) hk
    · exact hc i (by omega) hk j (by rw [h.same.2.2.1]; exact hj)
    · rw [← h.same.2.1]; exact hd i (by omega) j (by omega) hij hki hkj
  · rintro ⟨⟨hf, hu, hc, hd⟩, hr⟩
    refine ⟨fun i hi hqf => ?_, fun i hi hk => ?_, fun i hi hk j hj => ?_,
      fun i hi j hj hij hki hkj => ?_⟩
    · by_cases hir : i = r
      · subst hir; exact hr
      · exact hf i (by omega) (by rw [← h.fixed.2 i hir]; exact hqf)
    · rw [unavailable_iff h]; exact hu i (by omega) hk
    · exact hc i (by omega) hk j (by rw [← h.same.2.2.1]; exact hj)
    · rw [h.same.2.1]; exact hd i (by omega) j (by omega) hij hki hkj

theorem score_succ (n : Nat) (k : Nat → Bool) :
    score (n + 1) k = score n k + (if k n then 1 else 0) := by
  simp only [score, List.range_succ, List.filter_append, List.length_append, List.filter_cons,
    List.filter_nil]
  cases k n <;> simp

theorem score_mono {k k' : Nat → Bool} (hle : ∀ i, k i = true → k' i = true) (size : Nat) :
    score size k ≤ score size k' := by
  induction size with
  | zero => simp [score]
  | succ n ih =>
    rw [score_succ, score_succ]
    cases hk : k n
    · cases k' n <;> simp <;> omega
    · simp [hle n hk]; omega

theorem score_lt {k k' : Nat → Bool} (hle : ∀ i, k i = true → k' i = true)
    (hkr : k r = false) (hkr' : k' r = true) : ∀ size, r < size → score size k < score size k' := by
  intro size
  induction size with
  | zero => intro hr; omega
  | succ n ih =>
    intro hr
    rw [score_succ, score_succ]
    by_cases hrn : r = n
    · subst hrn
      have := score_mono hle r
      simp [hkr, hkr']
      omega
    · have := ih (by omega)
      cases hk : k n
      · cases k' n <;> simp <;> omega
      · simp [hle n hk]; omega

/-- Every highest-scoring mask of the original keeps `r`: adding `r` and every node it reaches
to a mask without it stays feasible and keeps more nodes. -/
theorem best_keeps (h : Promoted p q r) {k : Nat → Bool} (hk : Feasible p k)
    (best : ∀ k', Feasible p k' → score p.size k' ≤ score p.size k) : k r = true := by
  classical
  let reach : Nat → Prop := fun j => Relation.ReflTransGen (fun a b => b ∈ p.edges a) r j
  let k' : Nat → Bool := fun i => k i || decide (reach i)
  have hle : ∀ i, k i = true → k' i = true := fun i hi => by simp [k', hi]
  have hor : ∀ i, k' i = true → k i = true ∨ reach i := fun i hi => by
    simpa [k'] using hi
  obtain ⟨hf, hu, hc, hd⟩ := hk
  have feasible : Feasible p k' := by
    refine ⟨fun i hi hpf => hle i (hf i hi hpf), fun i hi hki => ?_, fun i hi hki j hj => ?_,
      fun i hi j hj hij hki hkj => ?_⟩
    · rcases hor i hki with hki | hri
      · exact hu i hi hki
      · rintro ⟨s, hs, hpath⟩
        exact h.available ⟨s, hs, hri.trans hpath⟩
    · rcases hor i hki with hki | hri
      · exact hle j (hc i hi hki j hj)
      · simp [k', show reach j from hri.tail hj]
    · rcases hor j hkj with hkj' | hrj
      · rcases hor i hki with hki' | hri
        · exact hd i hi j hj hij hki' hkj'
        · exact (h.storage i hri j hj (Ne.symm hij)).symm
      · exact h.storage j hrj i hi hij
  cases hkr : k r with
  | true => rfl
  | false =>
    have hkr' : k' r = true := by simp [k', show reach r from Relation.ReflTransGen.refl]
    have := score_lt hle hkr hkr' p.size h.bound
    have := best k' feasible
    omega

/-- A problem whose nodes are all fixed and which has no seed, the result kept whole, has one
choice: keep everything, feasible exactly when the storages are distinct. The runtime answers it
with the storage claims alone (`keptWhole` in `src/restore-identities.ts`). -/
theorem kept_whole {p : Problem} (hfix : ∀ i < p.size, p.fixed i = true)
    (hseed : ∀ s, p.seed s = false) (k : Nat → Bool) :
    Feasible p k ↔ (∀ i < p.size, k i = true) ∧
      (∀ i < p.size, k i = true → ∀ j ∈ p.edges i, k j = true) ∧
      ∀ i < p.size, ∀ j < p.size, i ≠ j → p.storage i ≠ p.storage j := by
  have hnone : ∀ i, ¬ Unavailable p i := by
    rintro i ⟨s, hs, -⟩
    simp [hseed s] at hs
  constructor
  · rintro ⟨hf, -, hc, hd⟩
    have hall : ∀ i < p.size, k i = true := fun i hi => hf i hi (hfix i hi)
    exact ⟨hall, hc, fun i hi j hj hij => hd i hi j hj hij (hall i hi) (hall j hj)⟩
  · rintro ⟨hall, hc, hd⟩
    exact ⟨fun i hi _ => hall i hi, fun i _ _ => hnone i, hc,
      fun i hi j hj hij _ _ => hd i hi j hj hij⟩

end Reconcile.PromotedLeaves
