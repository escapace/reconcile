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

/-- The finite queue completes when the supplied domain bounds the actual rule graph. -/
theorem expand_drains (vertices : Finset Nat) (state : Online) (fact : Nat)
    (knownBound : state.known ⊆ vertices) (factBound : fact ∈ vertices)
    (graphBound : ∀ node ∈ vertices, ∀ next ∈ state.graph node, next ∈ vertices) :
    (run state.graph vertices.card (start state.known [fact])).pending = [] := by
  apply run_drains state.graph state.known vertices graphBound vertices.card _
    (start_invariant _ _)
  · intro node member
    rcases Finset.mem_union.mp member with old | seed
    · exact knownBound old
    · simpa using (List.mem_singleton.mp (List.mem_toFinset.mp seed)) ▸ factBound
  · simp [start]

/-- Completed model order is the native worklist's ordered fresh-insertion trace. -/
theorem expand_order (vertices : Finset Nat) (state : Online) (fact : Nat)
    (knownBound : state.known ⊆ vertices) (factBound : fact ∈ vertices)
    (graphBound : ∀ node ∈ vertices, ∀ next ∈ state.graph node, next ∈ vertices) :
    (expand vertices.card state fact).order = state.order ++
      lazyTrace state.graph vertices.card state.known [fact] := by
  have trace := run_insertions state.graph vertices.card (start state.known [fact])
  have complete := completed_insertion_order state.graph state.known vertices [fact]
    knownBound (by simpa using factBound) graphBound
  simp only [start, List.nil_append] at trace
  simp only [expand, List.append_assoc, start]
  rw [trace, complete]

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
