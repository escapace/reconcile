import Spec.Promises
import Graph.Requirements

/-! `produce`'s maximal reuse is stated once, over the reference model: `Spec.Produce.kept` holds
every unchanged subtree and no changed object (`kept_greatest`, `kept_closed`). The runtime
computes the same set of current objects as the complement of a requirement closure: identity
restoration seeds `closeRequirements` with the records that cannot be reused and closes them over
their parents, and the eligibility mask (`immutableHead` in `src/graph/immutable-selection.ts`)
keeps the rest. `kept_iff` proves that, over the reference graph, the current nodes `kept` holds
are exactly those the closure of the changed nodes over the parent relation leaves out. That the
runtime's records, seeds and parents are these nodes, changed nodes and references remains the
runtime's obligation. -/

namespace Reconcile.KeptClosure

open Reconcile.Spec Reconcile.Spec.Produce Reconcile.Requirements

/-- The current nodes that refer to `child`: the closure's rules run from a child to its
parents. -/
def parents (cur : Graph) (child : Nat) : List Nat :=
  (List.range cur.nodes.size).filter fun i => (cur.node i).refs.contains child

/-- The current nodes the recipe changed: the closure's seeds. -/
def changed (cur : Graph) (heap : Array Obj) : List Nat :=
  (List.range cur.nodes.size).filter fun i => heap[i]? != some (cur.node i)

/-- A current node is kept exactly when the closure of the changed nodes over their parents leaves
it out, in a closed graph whose current nodes start the draft heap. -/
theorem kept_iff (cur : Graph) (heap : Array Obj) (hclosed : cur.closed = true)
    (size : cur.nodes.size ≤ heap.size) {i : Nat} (hi : i < cur.nodes.size) :
    i ∈ kept cur heap ↔
      i ∉ close (parents cur) (changed cur heap) (Finset.range cur.nodes.size) := by
  set C := close (parents cur) (changed cur heap) (Finset.range cur.nodes.size)
  have hseeds : ∀ j ∈ changed cur heap, j ∈ Finset.range cur.nodes.size := fun j hj => by
    simpa [changed] using (List.mem_filter.mp hj).1
  have hdeps : ∀ j ∈ Finset.range cur.nodes.size, ∀ p ∈ parents cur j,
      p ∈ Finset.range cur.nodes.size := fun j _ p hp => by
    simpa [parents] using (List.mem_filter.mp hp).1
  have refsIn : ∀ j < cur.nodes.size, ∀ r ∈ (cur.node j).refs, r < cur.nodes.size := by
    intro j hj r hr
    simp only [Graph.closed, Bool.and_eq_true, Array.all_eq_true] at hclosed
    have h := hclosed.2 j hj
    simp only [List.all_eq_true, decide_eq_true_eq] at h
    exact h r (by simpa [Graph.node, hj] using hr)
  have parent : ∀ j < cur.nodes.size, ∀ r ∈ (cur.node j).refs, j ∈ parents cur r :=
    fun j hj r hr => List.mem_filter.mpr ⟨List.mem_range.mpr hj, List.contains_iff_mem.mpr hr⟩
  constructor
  · intro hk hc
    have keeps := kept_closed cur heap
    -- The current nodes `kept` leaves out hold the seeds and are closed over parents.
    have least := close_least (parents cur) (changed cur heap) (Finset.range cur.nodes.size)
      ((Finset.range cur.nodes.size).filter (· ∉ kept cur heap))
      (by
        intro j hj p hp
        obtain ⟨_, hjk⟩ := Finset.mem_filter.mp hj
        obtain ⟨hpn, hpr⟩ := List.mem_filter.mp hp
        refine Finset.mem_filter.mpr ⟨by simpa using hpn, fun hpk => hjk ?_⟩
        obtain ⟨_, same, all⟩ := keeps p hpk
        have hpn' : p < cur.nodes.size := by simpa using hpn
        rw [same hpn'] at all
        simp only [Option.getD_some, List.all_eq_true, hpn', ↓reduceIte,
          List.contains_iff_mem] at all
        exact all j (List.contains_iff_mem.mp hpr))
      (by
        intro j hj
        obtain ⟨hjn, hjc⟩ := List.mem_filter.mp hj
        refine Finset.mem_filter.mpr ⟨by simpa using hjn, fun hjk => ?_⟩
        have := (keeps j hjk).2.1 (by simpa using hjn)
        simp [this] at hjc)
    exact (Finset.mem_filter.mp (least hc)).2 hk
  · intro hc
    have closedC :=
      close_closed (parents cur) (changed cur heap) (Finset.range cur.nodes.size) hseeds hdeps
    -- The current nodes the closure leaves out satisfy the keep conditions.
    let S := (List.range cur.nodes.size).filter fun j => decide (j ∉ C)
    have unchanged : ∀ j < cur.nodes.size, j ∉ C → heap[j]? = some (cur.node j) := by
      intro j hj hjc
      by_contra hne
      exact hjc (close_seeds _ _ _ j
        (List.mem_filter.mpr ⟨List.mem_range.mpr hj, by simpa using hne⟩))
    have hS : ∀ j ∈ S, Keeps cur heap S j := by
      intro j hj
      obtain ⟨hjn, hjc⟩ := List.mem_filter.mp hj
      have hjn' : j < cur.nodes.size := List.mem_range.mp hjn
      have hjc' : j ∉ C := by simpa using hjc
      refine ⟨Nat.lt_of_lt_of_le hjn' size, fun _ => unchanged j hjn' hjc', ?_⟩
      rw [unchanged j hjn' hjc']
      simp only [Option.getD_some, List.all_eq_true, hjn', ↓reduceIte, List.contains_iff_mem]
      intro r hr
      refine List.mem_filter.mpr ⟨List.mem_range.mpr (refsIn j hjn' r hr), ?_⟩
      simp only [decide_eq_true_eq]
      exact fun hrc => hjc' (closedC r hrc j (parent j hjn' r hr))
    exact kept_greatest cur heap S hS i
      (List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simpa using hc⟩)

end Reconcile.KeptClosure
