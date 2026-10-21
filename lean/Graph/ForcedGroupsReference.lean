import Graph.ForcedGroups
import Graph.FiniteReachability

/-! A reference partition for `ForcedGroups`, computed with `FiniteReachability` from
complete-domain support uniqueness, and the dense row-major problem that the Policy bridge builds
from selection domains (`fromDomains`). -/

namespace Reconcile.ForcedGroups

/-- Complete-domain support uniqueness, computed independently of an efficient SCC routine. -/
def referenceGraph (p : Problem) : FiniteReachability.Graph where
  vertices := p.literals
  next := fun source => p.literals.filter (mandatory p source)
  admitted := by intro source; exact Finset.filter_subset _ _

theorem reference_edge (p : Problem) (source target : Nat) :
    target ∈ (referenceGraph p).next source ↔ mandatory p source target := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    obtain ⟨edge, hmem, he⟩ := h
    have ht : target ∈ supports p edge := by rw [he]; simp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht).1, ⟨edge, hmem, he⟩⟩

theorem reference_reaches (p : Problem) (source target : Nat) :
    FiniteReachability.reaches (referenceGraph p) source target ↔ reaches p source target := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail path edge ih => exact ih.tail ((reference_edge p _ _).mp edge)
  · intro h
    induction h with
    | refl => exact .refl
    | tail path edge ih => exact ih.tail ((reference_edge p _ _).mpr edge)

/-- A proved executable SCC certificate, rather than an assumed partition field. -/
def referencePartition (p : Problem) : Partition p :=
  let labels := FiniteReachability.cachedLabels (referenceGraph p) p.literals.card
  { classOf := labels.get
    exact := by
      intro a ha b hb
      simp only [labels, FiniteReachability.cachedLabels_get]
      rw [FiniteReachability.leader_eq_iff (referenceGraph p) ha hb]
      simp only [reference_reaches, sameComponent] }

/-- Dense row-major choice positions for the executable native correspondence bridge. -/
def fromDomains (domains : Policy.Domains) : Problem :=
  let entries := (domains.zipIdx.flatMap fun (domain, node) =>
    domain.map fun choice => (node, choice)).toArray
  let fallback : Nat × Policy.Choice := (0, { identity := 0, storage := 0, retained := false, required := [] })
  { nodes := Finset.range domains.length
    literals := Finset.range entries.size
    owner := fun id => (entries[id]?.getD fallback).1
    choice := fun id => (entries[id]?.getD fallback).2 }

example : encode (referencePartition twoCycle) {0, 1} = {0} := by decide
example : decode (referencePartition twoCycle) {0} = {0, 1} := by decide
example : (referencePartition alternatives).classOf 1 ≠
    (referencePartition alternatives).classOf 2 := by decide

end Reconcile.ForcedGroups
