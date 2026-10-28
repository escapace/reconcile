import Graph.RequirementPropagation

/-! Requirement closure (`closeRequirements` in `src/graph/requirements.ts`): `close` is the set
the runtime's eager queue (`RequirementPropagation.run`) admits from the seeds, run until the queue
drains (`close_drains`). It is the least set of facts that holds the seeds and is closed under the
rules (`close_seeds`, `close_closed`, `close_least`). -/

namespace Reconcile.Requirements

open RequirementAdmission RequirementPropagation

def Closed (successors : Nat → List Nat) (facts : Finset Nat) : Prop :=
  ∀ fact ∈ facts, ∀ next ∈ successors fact, next ∈ facts

/-- The facts `closeRequirements(seeds, successors)` returns: the eager queue from the seeds, given
one step for each fact of `domain`. -/
def close (successors : Nat → List Nat) (seeds : List Nat) (domain : Finset Nat) : Finset Nat :=
  (run successors domain.card (start ∅ seeds)).admitted

/-- When the domain holds the seeds and is closed, its size bounds the steps, so `close` is the
completed loop. -/
theorem close_drains (successors : Nat → List Nat) (seeds : List Nat) (domain : Finset Nat)
    (hseeds : ∀ fact ∈ seeds, fact ∈ domain)
    (hdeps : ∀ fact ∈ domain, ∀ next ∈ successors fact, next ∈ domain) :
    (run successors domain.card (start ∅ seeds)).pending = [] :=
  run_drains successors ∅ domain hdeps domain.card _ (start_invariant ∅ seeds)
    (fun fact hf => hseeds fact (by simpa [start] using hf)) (by simp [start])

/-- With no seeds nothing is required, so the runtime skips the worklist. -/
theorem close_no_seeds (successors : Nat → List Nat) (domain : Finset Nat) :
    close successors [] domain = ∅ := by
  cases h : domain.card <;> simp [close, start, admit, run, h]

theorem close_seeds (successors : Nat → List Nat) (seeds : List Nat) (domain : Finset Nat) :
    ∀ fact ∈ seeds, fact ∈ close successors seeds domain :=
  fun _ hf => run_admitted_mono successors _ _ (by simp [start, hf])

/-- Leastness: every fact `close` admits lies in each closed set that holds the seeds. -/
theorem close_least (successors : Nat → List Nat) (seeds : List Nat) (domain facts : Finset Nat)
    (hclosed : Closed successors facts) (hseeds : ∀ fact ∈ seeds, fact ∈ facts) :
    close successors seeds domain ⊆ facts :=
  fun fact hf => run_admitted_closed successors (· ∈ facts) hclosed _ _
    (fun fact hf => hseeds fact ((admit_mem _ _ _).mp hf).1)
    (fun fact hf => hseeds fact (by simpa [start] using hf)) fact hf

theorem close_closed (successors : Nat → List Nat) (seeds : List Nat) (domain : Finset Nat)
    (hseeds : ∀ fact ∈ seeds, fact ∈ domain)
    (hdeps : ∀ fact ∈ domain, ∀ next ∈ successors fact, next ∈ domain) :
    Closed successors (close successors seeds domain) :=
  run_closed successors ∅ seeds domain.card (by simp)
    (close_drains successors seeds domain hseeds hdeps)

end Reconcile.Requirements
