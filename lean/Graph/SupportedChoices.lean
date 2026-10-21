import Graph.ForcedGroupsReference

/-! Supported-choice pruning (`src/graph/supported-choices.ts` `unsupportedChoices`): repeatedly
removing choices with an unsupported requirement keeps every feasible selection and reaches a
fixed point within one round per literal. -/

namespace Reconcile.SupportedChoices

open ForcedGroups

/-- Self requirements need this same choice, not another position with the same owner. -/
def supported (p : Problem) (live : Finset Nat) (id : Nat) : Prop :=
  ∀ edge ∈ (p.choice id).required, ∃ target ∈ live,
    target ∈ supports p edge ∧ (edge.node = p.owner id → target = id)

instance (p : Problem) (live : Finset Nat) (id : Nat) : Decidable (supported p live id) := by
  unfold supported
  infer_instance

def step (p : Problem) (live : Finset Nat) : Finset Nat :=
  live.filter (supported p live)

theorem step_subset (p : Problem) (live : Finset Nat) : step p live ⊆ live :=
  Finset.filter_subset _ _

theorem supported_mono (p : Problem) {small large : Finset Nat} (h : small ⊆ large)
    {id : Nat} (hs : supported p small id) : supported p large id := by
  intro edge he
  obtain ⟨target, ht, hm⟩ := hs edge he
  exact ⟨target, h ht, hm⟩

theorem feasible_supported (p : Problem) (selected : Finset Nat)
    (hf : feasible p selected) {live : Finset Nat} (hl : selected ⊆ live)
    {id : Nat} (hi : id ∈ selected) : supported p live id := by
  intro edge he
  obtain ⟨target, ht, hm⟩ := hf.2.2.2.2 id hi edge he
  refine ⟨target, hl ht, hm, ?_⟩
  intro hself
  exact hf.2.2.1 target ht id hi ((Finset.mem_filter.mp hm).2.1.trans hself)

theorem step_preserves (p : Problem) (selected : Finset Nat)
    (hf : feasible p selected) {live : Finset Nat} (hl : selected ⊆ live) :
    selected ⊆ step p live := by
  intro id hi
  exact Finset.mem_filter.mpr ⟨hl hi, feasible_supported p selected hf hl hi⟩

/-- Independent exhaustive fixed-point reference, with at most one round per literal. -/
def rounds (p : Problem) : Nat → Finset Nat → Finset Nat
  | 0, live => live
  | fuel + 1, live => rounds p fuel (step p live)

theorem rounds_subset (p : Problem) (fuel : Nat) (live : Finset Nat) :
    rounds p fuel live ⊆ live := by
  induction fuel generalizing live with
  | zero => exact Finset.Subset.refl _
  | succ fuel ih => exact (ih _).trans (step_subset p live)

theorem rounds_preserves (p : Problem) (selected : Finset Nat) (hf : feasible p selected)
    (fuel : Nat) {live : Finset Nat} (hl : selected ⊆ live) :
    selected ⊆ rounds p fuel live := by
  induction fuel generalizing live with
  | zero => exact hl
  | succ fuel ih => exact ih (step_preserves p selected hf hl)

theorem strict_descent (p : Problem) (live : Finset Nat) (h : step p live ≠ live) :
    (step p live).card < live.card :=
  Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨step_subset p live, h⟩)

theorem rounds_stable (p : Problem) (fuel : Nat) (live : Finset Nat)
    (h : step p live = live) : rounds p fuel live = live := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [rounds, h] using ih

theorem rounds_fixed (p : Problem) (fuel : Nat) (live : Finset Nat)
    (h : live.card ≤ fuel) : step p (rounds p fuel live) = rounds p fuel live := by
  induction fuel generalizing live with
  | zero =>
    have he : live = ∅ := Finset.card_eq_zero.mp (by omega)
    simp [rounds, he, step]
  | succ fuel ih =>
    by_cases he : step p live = live
    · simpa only [rounds_stable p _ _ he] using he
    · exact ih (step p live) (by have := strict_descent p live he; omega)

def survivors (p : Problem) : Finset Nat := rounds p p.literals.card p.literals

theorem survivors_preserve (p : Problem) (selected : Finset Nat) (hf : feasible p selected) :
    selected ⊆ survivors p := rounds_preserves p selected hf _ hf.1

theorem survivors_fixed (p : Problem) : step p (survivors p) = survivors p :=
  rounds_fixed p _ _ (Nat.le_refl _)

/-- Any already-supported subdomain survives every deletion round. -/
theorem fixed_survives (p : Problem) (fixed : Finset Nat) (hs : step p fixed = fixed)
    (fuel : Nat) {live : Finset Nat} (hl : fixed ⊆ live) : fixed ⊆ rounds p fuel live := by
  induction fuel generalizing live with
  | zero => exact hl
  | succ fuel ih =>
    apply ih
    intro id hi
    have hm : id ∈ step p fixed := hs.symm ▸ hi
    exact Finset.mem_filter.mpr ⟨hl hi, supported_mono p hl (Finset.mem_filter.mp hm).2⟩

/-- An event engine may delete unsupported positions in any order. -/
theorem erase_preserves_fixed (p : Problem) (fixed live : Finset Nat)
    (hs : step p fixed = fixed) (hl : fixed ⊆ live) {id : Nat}
    (hu : ¬ supported p live id) : fixed ⊆ live.erase id := by
  intro target ht
  refine Finset.mem_erase.mpr ⟨?_, hl ht⟩
  intro he
  subst target
  have hm : id ∈ step p fixed := hs.symm ▸ ht
  exact hu (supported_mono p hl (Finset.mem_filter.mp hm).2)

/-- A completed event run equals the independent rounds reference once its invariants hold. -/
theorem completed_exact (p : Problem) (live : Finset Nat)
    (hl : live ⊆ p.literals) (hs : step p live = live)
    (hp : survivors p ⊆ live) : live = survivors p :=
  Finset.Subset.antisymm (fixed_survives p live hs _ hl) hp

/-- Removing an unrelated position leaves a support bucket's count unchanged. -/
theorem unrelated_count (bucket live : Finset Nat) {id : Nat} (hi : id ∉ bucket) :
    bucket ∩ live.erase id = bucket ∩ live := by
  ext target
  simp only [Finset.mem_inter, Finset.mem_erase]
  aesop

/-- Removing one live support decrements exactly once, regardless of equal identity labels. -/
theorem support_count_progress (bucket live : Finset Nat) {id : Nat}
    (hb : id ∈ bucket) (hl : id ∈ live) :
    (bucket ∩ live.erase id).card + 1 = (bucket ∩ live).card := by
  have he : bucket ∩ live.erase id = (bucket ∩ live).erase id := by
    ext target
    simp only [Finset.mem_inter, Finset.mem_erase]
    tauto
  rw [he]
  exact Finset.card_erase_add_one (Finset.mem_inter.mpr ⟨hb, hl⟩)

/-- Filtering a list retains its relative order; no choice-position renumbering is needed. -/
theorem survivor_order (p : Problem) (order : List Nat) :
    (order.filter fun id => id ∈ survivors p).Sublist order := List.filter_sublist

/-- A bucket count reaches zero exactly when its live support set is empty. -/
theorem support_count_zero (bucket live : Finset Nat) :
    (bucket ∩ live).card = 0 ↔ ∀ id ∈ bucket, id ∉ live := by
  simp [Finset.card_eq_zero, Finset.ext_iff]

/-- Each admitted deletion removes one live position, including duplicate-identity choices. -/
theorem deletion_progress (live : Finset Nat) {id : Nat} (hi : id ∈ live) :
    (live.erase id).card + 1 = live.card := Finset.card_erase_add_one hi

example : survivors twoCycle = {0, 1} := by decide
example : survivors alternatives = alternatives.literals := by decide

end Reconcile.SupportedChoices
