import Graph.Construction

/-!
First refinement layer for a dependency-driven construction frontier. Outstanding
counts include repeated dependency occurrences. Discharging a newly ready set
preserves the baseline readiness predicate and therefore its exact stable waves.
ConstructionIncidence and ConstructionRankUpdates supply the reverse-incidence
and level refinements; ConstructionScheduler assembles exact schedule equality.
This intermediate model supports the current runtime, without modeling native effects.
-/
namespace Reconcile.ConstructionFrontier

open Reconcile.Construction

def outstanding (dependencies : List Nat) (known : Finset Nat) : Nat :=
  (dependencies.filter fun dependency => decide (dependency ∉ known)).length

def discharged (dependencies : List Nat) (known added : Finset Nat) : Nat :=
  (dependencies.filter fun dependency => decide (dependency ∉ known ∧ dependency ∈ added)).length

theorem outstanding_zero_iff (dependencies : List Nat) (known : Finset Nat) :
    outstanding dependencies known = 0 ↔ ∀ dependency ∈ dependencies, dependency ∈ known := by
  simp [outstanding, List.filter_eq_nil_iff]

theorem discharge_partition (dependencies : List Nat) (known added : Finset Nat) :
    outstanding dependencies known =
      outstanding dependencies (known ∪ added) + discharged dependencies known added := by
  induction dependencies with
  | nil => simp [outstanding, discharged]
  | cons dependency rest ih =>
    by_cases hk : dependency ∈ known <;> by_cases ha : dependency ∈ added <;>
      simp_all [outstanding, discharged, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]

theorem decrement_exact (dependencies : List Nat) (known added : Finset Nat) :
    outstanding dependencies known - discharged dependencies known added =
      outstanding dependencies (known ∪ added) := by
  have h := discharge_partition dependencies known added
  omega

theorem discharge_bounded (dependencies : List Nat) (known added : Finset Nat) :
    discharged dependencies known added ≤ outstanding dependencies known := by
  have h := discharge_partition dependencies known added
  omega

def counterReady (deps : Dependencies) (known : Finset Nat) (node : Nat) : Bool :=
  decide (outstanding (deps node) known = 0)

theorem counterReady_eq_ready (deps : Dependencies) (known : Finset Nat) (node : Nat) :
    counterReady deps known node = ready deps known node := by
  apply Bool.eq_iff_iff.mpr
  simp [counterReady, ready, outstanding_zero_iff]

def counterWaves (deps : Dependencies) : Nat → Finset Nat → List Nat → Option (List Nat)
  | 0, _, pending => if pending.isEmpty then some [] else none
  | fuel + 1, known, pending =>
    if pending.isEmpty then some [] else
      let wave := pending.filter (counterReady deps known)
      if wave.isEmpty then none else
        let waiting := pending.filter fun node => !counterReady deps known node
        (counterWaves deps fuel (known ∪ wave.toFinset) waiting).map (wave ++ ·)

theorem counterWaves_eq_waves (deps : Dependencies) (fuel : Nat)
    (known : Finset Nat) (pending : List Nat) :
    counterWaves deps fuel known pending = waves deps fuel known pending := by
  induction fuel generalizing known pending with
  | zero => rfl
  | succ fuel ih =>
    have hr : counterReady deps = ready deps := by
      funext known node
      exact counterReady_eq_ready deps known node
    simp only [counterWaves, waves, hr, ih]

def counterSchedule (deps : Dependencies) (retained : Finset Nat) (nodes : List Nat) :
    Option (List Nat) :=
  let fresh := nodes.filter fun node => decide (node ∉ retained)
  let shells := fresh.filter fun node => (deps node).isEmpty
  let pending := fresh.filter fun node => !(deps node).isEmpty
  (counterWaves deps nodes.length (retained ∪ shells.toFinset) pending).map (shells ++ ·)

theorem counterSchedule_eq_schedule (deps : Dependencies) (retained : Finset Nat)
    (nodes : List Nat) : counterSchedule deps retained nodes = schedule deps retained nodes := by
  simp only [counterSchedule, schedule, counterWaves_eq_waves]

example : outstanding [1, 1, 2] {2} = 2 := by decide
example : discharged [1, 1, 2] {2} {1} = 2 := by decide
example : outstanding [1, 1, 2] {1, 2} = 0 := by decide
-- Node 1 is already dependency-ready, but the empty shell 2 still precedes it.
example : counterSchedule (fun node => if node = 1 then [0] else []) {0} [0, 1, 2] =
    some [2, 1] := by decide

end Reconcile.ConstructionFrontier
