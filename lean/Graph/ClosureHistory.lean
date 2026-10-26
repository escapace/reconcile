import Graph.RequirementPropagation

/-! Ordered growing rule graphs used by the fact-renaming model. The fact-renaming
statements use this namespace and the `eventStep` signature; that model always uses
unconditional rule insertion (`eventStep false`). -/
namespace Reconcile.OnlineRequirements

open RequirementAdmission RequirementPropagation

abbrev Graph := Nat → List Nat

def appendUnique (row : List Nat) (fact : Nat) : List Nat :=
  if fact ∈ row then row else row ++ [fact]

def add (graph : Graph) (source target : Nat) : Graph :=
  fun node => if node = source then appendUnique (graph node) target else graph node

structure Online where
  graph : Graph
  known : Finset Nat
  order : List Nat

inductive Event where
  | require (fact : Nat)
  | imply (source target : Nat)
  deriving Repr, DecidableEq

def expand (fuel : Nat) (state : Online) (fact : Nat) : Online :=
  let work := run state.graph fuel (start state.known [fact])
  { state with known := work.admitted, order := state.order ++ work.processed ++ work.pending }

theorem expand_known (fuel : Nat) (state : Online) (fact : Nat) (settled : fact ∈ state.known) :
    expand fuel state fact = state := by
  cases state
  cases fuel <;> simp_all [expand, start, admit, run]

def eventStep (optimized : Bool) (fuel : Nat) (state : Online) : Event → Online
  | .require fact => expand fuel state fact
  | .imply source target =>
    if optimized && decide (target ∈ state.known) then state
    else
      let next := { state with graph := add state.graph source target }
      if source ∈ state.known then expand fuel next target else next

/-- Running from a processed prefix only prepends that prefix. -/
theorem run_processed (graph : Graph) (fuel : Nat) (processed pending : List Nat)
    (admitted : Finset Nat) :
    run graph fuel ⟨processed, pending, admitted⟩ =
      let work := run graph fuel ⟨[], pending, admitted⟩
      ⟨processed ++ work.processed, work.pending, work.admitted⟩ := by
  induction fuel generalizing processed pending admitted with
  | zero => simp [run]
  | succ fuel ih =>
    cases pending with
    | nil => simp [run]
    | cons head rest =>
      simp only [run, step, List.nil_append]
      rw [ih (processed ++ [head]), ih [head]]
      simp [List.append_assoc]

/-- The native `require`: a known fact returns at once; otherwise it is admitted and the
queue starts from its successors. This is one unfolding of `expand` with one more step of
fuel, so completed order and closure are unchanged. -/
def expandUnfolded (fuel : Nat) (state : Online) (fact : Nat) : Online :=
  if fact ∈ state.known then state
  else
    let work := run state.graph fuel (start (insert fact state.known) (state.graph fact))
    { state with known := work.admitted,
                 order := state.order ++ [fact] ++ work.processed ++ work.pending }

theorem expandUnfolded_eq (fuel : Nat) (state : Online) (fact : Nat) :
    expandUnfolded fuel state fact = expand (fuel + 1) state fact := by
  by_cases known : fact ∈ state.known
  · rw [expand_known _ _ _ known]
    simp [expandUnfolded, known]
  · have single : state.known ∪ [fact].toFinset = insert fact state.known := by
      ext x; simp
    simp only [expandUnfolded, known, ↓reduceIte, expand, start, admit, run, step,
      List.nil_append, single]
    rw [run_processed state.graph fuel [fact]]
    simp [List.append_assoc]

def empty : Online := ⟨fun _ => [], ∅, []⟩

end Reconcile.OnlineRequirements
