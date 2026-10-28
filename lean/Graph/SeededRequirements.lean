import Graph.Requirements

/-! Seeded closure removes only reverse incidences whose destination is already an initial
failure. It changes a private compiled index, not discovery or native checks. -/
namespace Reconcile.SeededRequirements

open Requirements RequirementAdmission RequirementPropagation

def trim (seeds : Finset Nat) (successors : Nat → List Nat) (fact : Nat) : List Nat :=
  (successors fact).filter fun next => decide (next ∉ seeds)

@[simp] theorem mem_trim (seeds : Finset Nat) (successors : Nat → List Nat)
    (fact next : Nat) :
    next ∈ trim seeds successors fact ↔ next ∈ successors fact ∧ next ∉ seeds := by
  simp [trim]

theorem admit_filter (seeds known : Finset Nat) (input : List Nat)
    (included : seeds ⊆ known) :
    admit known (input.filter fun next => decide (next ∉ seeds)) = admit known input := by
  induction input generalizing known with
  | nil => rfl
  | cons head rest ih =>
    by_cases hs : head ∈ seeds
    · have hk := included hs
      simp [hs, admit, hk]
      simpa only [decide_not] using ih known included
    · by_cases hk : head ∈ known
      · simp [hs, admit, hk]
        simpa only [decide_not] using ih known included
      · have enlarged : seeds ⊆ insert head known :=
          fun _ hf => Finset.mem_insert_of_mem (included hf)
        simp [hs, admit, hk]
        simpa only [decide_not] using ih _ enlarged

theorem union_trim (seeds known : Finset Nat) (successors : Nat → List Nat) (fact : Nat)
    (included : seeds ⊆ known) :
    known ∪ (trim seeds successors fact).toFinset = known ∪ (successors fact).toFinset := by
  ext next
  by_cases hs : next ∈ seeds
  · simp [hs, included hs]
  · simp [hs]

theorem step_eq (seeds : Finset Nat) (successors : Nat → List Nat)
    (processed : List Nat) (head : Nat) (rest : List Nat) (known : Finset Nat)
    (included : seeds ⊆ known) :
    step (trim seeds successors) processed head rest known =
      step successors processed head rest known := by
  simp only [step, union_trim seeds known successors head included]
  rw [trim, admit_filter seeds known (successors head) included]

theorem run_eq (seeds : Finset Nat) (successors : Nat → List Nat)
    (fuel : Nat) (state : State) (included : seeds ⊆ state.admitted) :
    run (trim seeds successors) fuel state = run successors fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    rcases state with ⟨processed, pending, known⟩
    cases pending with
    | nil => rfl
    | cons head rest =>
      simp only [run]
      rw [step_eq seeds successors processed head rest known included]
      exact ih _ (fun _ hf => Finset.mem_union_left _ (included hf))

/-- Trimming keeps the closure: the queue from the seeds already admits every trimmed incidence's
destination (`run_eq`). -/
theorem close_eq (successors : Nat → List Nat) (seeds : List Nat) (domain : Finset Nat) :
    close (trim seeds.toFinset successors) seeds domain = close successors seeds domain :=
  congrArg State.admitted (run_eq _ _ _ _ (by simp [start]))

def scans (successors : Nat → List Nat) (trace : List Nat) : Nat :=
  (trace.map fun fact => (successors fact).length).sum

theorem scans_le (seeds : Finset Nat) (successors : Nat → List Nat) (trace : List Nat) :
    scans (trim seeds successors) trace ≤ scans successors trace := by
  induction trace with
  | nil => rfl
  | cons head rest ih =>
    simpa [scans, trim] using Nat.add_le_add (List.length_filter_le _ (successors head)) ih

-- Filtering sources would lose the late failure of node 1.
def cycle : Nat → List Nat
  | 0 => [1]
  | 1 => [0]
  | _ => []

example : (run (trim {0} cycle) 2 (start ∅ [0])).processed = [0, 1] := by decide
example : (run (fun fact => if fact = 0 then [] else cycle fact) 2
    (start ∅ [0])).processed = [0] := by decide

end Reconcile.SeededRequirements
