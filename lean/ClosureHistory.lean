import RequirementPropagation

/-! Ordered growing rule graphs used by the fact-renaming model.
The namespace and eventStep signature preserve the existing renaming statements;
that model always uses unconditional rule insertion (`eventStep false`). -/
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

def empty : Online := ⟨fun _ => [], ∅, []⟩

end Reconcile.OnlineRequirements
