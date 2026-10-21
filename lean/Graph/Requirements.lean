import Heap.ReuseClosure

/-! Requirement closure (`src/graph/requirements.ts`): `close` is the least set of facts that
contains the seeds and is closed under the rules, and resuming from known facts under an extended
rule graph gives the same closure as starting from the seeds (`close_resume`). -/

namespace Reconcile.Requirements

/-- Positive form of the finite worklist `reuseSurvivors` (`ReuseClosure`). The runtime Set
worklist computes this least closure; traversal order is not observable here. -/
def close (successors : Nat → List Nat) (seeds : List Nat) (domain : Finset Nat) : Finset Nat :=
  domain \ reuseSurvivors successors seeds domain

def Closed (successors : Nat → List Nat) (facts : Finset Nat) : Prop :=
  ∀ fact ∈ facts, ∀ next ∈ successors fact, next ∈ facts

theorem close_domain (successors : Nat → List Nat) (seeds : List Nat) (domain : Finset Nat) :
    close successors seeds domain ⊆ domain := Finset.sdiff_subset

theorem close_seeds (successors : Nat → List Nat) (seeds : List Nat) (domain : Finset Nat)
    (hseeds : ∀ fact ∈ seeds, fact ∈ domain) : ∀ fact ∈ seeds, fact ∈ close successors seeds domain := by
  intro fact hf
  exact Finset.mem_sdiff.mpr ⟨hseeds fact hf, reuseSurvivors_excludes successors seeds domain fact hf⟩

theorem close_closed (successors : Nat → List Nat) (seeds : List Nat) (domain : Finset Nat)
    (hdeps : ∀ fact ∈ domain, ∀ next ∈ successors fact, next ∈ domain) :
    Closed successors (close successors seeds domain) := by
  intro fact hf next hn
  obtain ⟨hd, hr⟩ := Finset.mem_sdiff.mp hf
  exact Finset.mem_sdiff.mpr ⟨hdeps fact hd next hn,
    reuseSurvivors_propagates successors seeds domain fact hd hr next hn⟩

theorem close_least (successors : Nat → List Nat) (seeds : List Nat) (domain facts : Finset Nat)
    (hpre : ∀ child parent, parent ∈ successors child → parent ∈ domain → child ∈ domain)
    (hclosed : Closed successors facts) (hseeds : ∀ fact ∈ seeds, fact ∈ facts) :
    close successors seeds domain ⊆ facts := by
  have hs : DependencyClosed successors (domain \ facts) := by
    intro child parent hp hs
    obtain ⟨hd, hf⟩ := Finset.mem_sdiff.mp hs
    exact Finset.mem_sdiff.mpr ⟨hpre child parent hp hd,
      fun h => hf (hclosed child h parent hp)⟩
  have hsurvivors := reuseSurvivors_greatest successors seeds domain (domain \ facts)
    Finset.sdiff_subset hs (fun fact hf h => (Finset.mem_sdiff.mp h).2 (hseeds fact hf))
  intro fact hf
  obtain ⟨hd, hn⟩ := Finset.mem_sdiff.mp hf
  by_contra h
  exact hn (hsurvivors (Finset.mem_sdiff.mpr ⟨hd, h⟩))

-- Resuming from previously derived facts is equivalent to closing the original
-- seeds under an extended rule graph. Facts remain valid when discovery learns
-- new edges; this does not model native observation or iterator bookkeeping.
theorem close_resume (old next : Nat → List Nat) (seeds known : List Nat) (domain : Finset Nat)
    (hknown : ∀ fact, fact ∈ known ↔ fact ∈ close old seeds domain)
    (hext : ∀ fact child, child ∈ old fact → child ∈ next fact)
    (hpre : ∀ child parent, parent ∈ next child → parent ∈ domain → child ∈ domain)
    (hdeps : ∀ fact ∈ domain, ∀ child ∈ next fact, child ∈ domain)
    (hseeds : ∀ fact ∈ seeds, fact ∈ domain) :
    close next known domain = close next seeds domain := by
  have hc := close_closed next seeds domain hdeps
  have hold : close old seeds domain ⊆ close next seeds domain :=
    close_least old seeds domain _
      (fun child parent hp hd => hpre child parent (hext child parent hp) hd)
      (fun fact hf child hh => hc fact hf child (hext fact child hh))
      (close_seeds next seeds domain hseeds)
  apply Finset.Subset.antisymm
  · exact close_least next known domain _ hpre hc
      (fun fact hf => hold ((hknown fact).mp hf))
  · exact close_least next seeds domain _ hpre (close_closed next known domain hdeps)
      (fun fact hf => close_seeds next known domain
        (fun value hv => close_domain old seeds domain ((hknown value).mp hv))
        fact ((hknown fact).mpr (close_seeds old seeds domain hseeds fact hf)))

end Reconcile.Requirements
