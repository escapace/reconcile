import Graph.RequirementPropagation

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

theorem closed_iff (seeds facts : Finset Nat) (successors : Nat → List Nat)
    (included : seeds ⊆ facts) :
    Closed (trim seeds successors) facts ↔ Closed successors facts := by
  constructor
  · intro closed fact hf next hn
    by_cases hs : next ∈ seeds
    · exact included hs
    · exact closed fact hf next (mem_trim seeds successors fact next |>.mpr ⟨hn, hs⟩)
  · intro closed fact hf next hn
    exact closed fact hf next ((mem_trim seeds successors fact next).mp hn).1

theorem close_eq (successors : Nat → List Nat) (seeds : List Nat) (domain : Finset Nat)
    (seedBound : ∀ fact ∈ seeds, fact ∈ domain)
    (pre : ∀ child parent, parent ∈ successors child → parent ∈ domain → child ∈ domain)
    (deps : ∀ fact ∈ domain, ∀ next ∈ successors fact, next ∈ domain) :
    close (trim seeds.toFinset successors) seeds domain = close successors seeds domain := by
  have filteredDeps : ∀ fact ∈ domain, ∀ next ∈ trim seeds.toFinset successors fact,
      next ∈ domain := fun fact hf next hn => deps fact hf next (mem_trim _ _ _ _ |>.mp hn).1
  have oldSeeds : seeds.toFinset ⊆ close successors seeds domain :=
    fun _ hf => close_seeds successors seeds domain seedBound _ (List.mem_toFinset.mp hf)
  have newSeeds : seeds.toFinset ⊆ close (trim seeds.toFinset successors) seeds domain :=
    fun _ hf => close_seeds _ seeds domain seedBound _ (List.mem_toFinset.mp hf)
  apply Finset.Subset.antisymm
  · exact close_least _ seeds domain _
      (fun child parent hp hd => pre child parent (mem_trim _ _ _ _ |>.mp hp).1 hd)
      ((closed_iff _ _ _ oldSeeds).mpr (close_closed _ _ _ deps))
      (close_seeds _ _ _ seedBound)
  · exact close_least _ seeds domain _ pre
      ((closed_iff _ _ _ newSeeds).mp (close_closed _ _ _ filteredDeps))
      (close_seeds _ _ _ seedBound)

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
