import ClosureHistory

/-! Exact representation of private discovery facts. A bijective
renaming models exact visible object identity, never shared storage ownership.
Stable first-use interning and unchanged canonical object arguments remain native
correspondence obligations; queries may intern labels before they become facts. -/
namespace Reconcile.FactRenaming

open RequirementAdmission RequirementPropagation OnlineRequirements

abbrev Renaming := Nat ≃ Nat

theorem membership (names : Renaming) (known : Finset Nat) (fact : Nat) :
    names fact ∈ known.image names ↔ fact ∈ known := by
  simp [Finset.mem_image]

theorem list_set (names : Renaming) (facts : List Nat) :
    (facts.map names).toFinset = facts.toFinset.image names := by
  ext fact
  simp

theorem admission (names : Renaming) (known : Finset Nat) (facts : List Nat) :
    admit (known.image names) (facts.map names) = (admit known facts).map names := by
  induction facts generalizing known with
  | nil => rfl
  | cons head rest ih =>
    by_cases present : head ∈ known
    · simp [admit, present, ih]
    · simpa [admit, membership, present, Finset.image_insert] using
        congrArg (List.cons (names head)) (ih (insert head known))

def graph (names : Renaming) (edges : Graph) : Graph :=
  fun fact => (edges (names.symm fact)).map names

def state (names : Renaming) (work : State) : State :=
  ⟨work.processed.map names, work.pending.map names, work.admitted.image names⟩

theorem start_eq (names : Renaming) (known : Finset Nat) (seeds : List Nat) :
    state names (start known seeds) = start (known.image names) (seeds.map names) := by
  simp [state, start, admission, list_set, Finset.image_union]

theorem step_eq (names : Renaming) (edges : Graph) (processed : List Nat)
    (head : Nat) (rest : List Nat) (known : Finset Nat) :
    state names (step edges processed head rest known) =
      step (graph names edges) (processed.map names) (names head) (rest.map names)
        (known.image names) := by
  simp [state, step, graph, admission, list_set, Finset.image_union]

theorem run_eq (names : Renaming) (edges : Graph) (fuel : Nat) (work : State) :
    state names (run edges fuel work) = run (graph names edges) fuel (state names work) := by
  induction fuel generalizing work with
  | zero => rfl
  | succ fuel ih =>
    rcases work with ⟨processed, pending, known⟩
    cases pending with
    | nil => rfl
    | cons head rest =>
      change state names (run edges fuel (step edges processed head rest known)) =
        run (graph names edges) fuel
          (step (graph names edges) (processed.map names) (names head) (rest.map names)
            (known.image names))
      rw [← step_eq]
      exact ih _

theorem append_eq (names : Renaming) (row : List Nat) (fact : Nat) :
    (appendUnique row fact).map names = appendUnique (row.map names) (names fact) := by
  by_cases present : fact ∈ row <;> simp [appendUnique, present]

theorem graph_add (names : Renaming) (edges : Graph) (source target : Nat) :
    graph names (add edges source target) =
      add (graph names edges) (names source) (names target) := by
  funext fact
  by_cases equal : fact = names source
  · subst fact
    simp [graph, add, append_eq]
  · have inverse : names.symm fact ≠ source := by
      intro same
      apply equal
      rw [← names.apply_symm_apply fact, same]
    simp [graph, add, equal, inverse]

def online (names : Renaming) (current : Online) : Online :=
  ⟨graph names current.graph, current.known.image names, current.order.map names⟩

theorem expand_eq (names : Renaming) (fuel : Nat) (current : Online) (fact : Nat) :
    online names (expand fuel current fact) = expand fuel (online names current) (names fact) := by
  have work := (run_eq names current.graph fuel (start current.known [fact])).symm
  rw [start_eq] at work
  simp only [List.map_singleton] at work
  simp [expand, online, work, state]

def event (names : Renaming) : Event → Event
  | .require fact => .require (names fact)
  | .imply source target => .imply (names source) (names target)

theorem event_eq (names : Renaming) (fuel : Nat) (current : Online) (input : Event) :
    online names (eventStep false fuel current input) =
      eventStep false fuel (online names current) (event names input) := by
  cases input with
  | require fact => exact expand_eq names fuel current fact
  | imply source target =>
    have edges : online names { current with graph := add current.graph source target } =
        { online names current with
          graph := add (graph names current.graph) (names source) (names target) } := by
      simp [online, graph_add]
    by_cases active : source ∈ current.known
    · have mapped : names source ∈ (online names current).known := (membership _ _ _).mpr active
      simpa [eventStep, event, active, mapped, edges] using
        expand_eq names fuel { current with graph := add current.graph source target } target
    · have mapped : names source ∉ (online names current).known :=
        fun member => active ((membership _ _ _).mp member)
      simpa [eventStep, event, active, mapped] using edges

/-- Membership queries have no closure effect, even when the native interner first sees a key. -/
inductive Action where
  | query (fact : Nat)
  | update (input : Event)
  deriving Repr, DecidableEq

def action (names : Renaming) : Action → Action
  | .query fact => .query (names fact)
  | .update input => .update (event names input)

def execute (fuel : Nat) (current : Online) : Action → Option Bool × Online
  | .query fact => (some (decide (fact ∈ current.known)), current)
  | .update input => (none, eventStep false fuel current input)

theorem execute_eq (names : Renaming) (fuel : Nat) (current : Online) (input : Action) :
    execute fuel (online names current) (action names input) =
      let result := execute fuel current input
      (result.1, online names result.2) := by
  cases input with
  | query fact => simp [execute, action, online]
  | update input => simp [execute, action, event_eq]

def observations (fuel : Nat) (current : Online) : List Action → List (Option Bool × List Nat)
  | [] => []
  | input :: rest =>
    let result := execute fuel current input
    (result.1, result.2.order) :: observations fuel result.2 rest

theorem observations_eq (names : Renaming) (fuel : Nat) (current : Online)
    (inputs : List Action) :
    observations fuel (online names current) (inputs.map (action names)) =
      (observations fuel current inputs).map (fun entry => (entry.1, entry.2.map names)) := by
  induction inputs generalizing current with
  | nil => rfl
  | cons input rest ih =>
    simp only [List.map_cons, observations, execute_eq]
    rw [ih]
    rfl

/-- Equal mapped insertion order also preserves each live Set iterator position. -/
theorem cursor_eq (names : Renaming) (current : Online) (index : Nat) :
    (online names current).order[index]? = current.order[index]?.map names := by
  simp [online]

theorem empty_eq (names : Renaming) : online names empty = empty := by
  simp only [online, empty, Finset.image_empty, List.map_nil]
  rfl

example : observations 3 empty [.query 1, .update (.imply 0 1), .query 1,
    .update (.require 0), .query 1] =
    [(some false, []), (none, []), (some false, []), (none, [0, 1]), (some true, [0, 1])] := by
  decide

example : (admit ∅ [0, 1]).map (fun _ => 0) ≠ admit ∅ ([0, 1].map (fun _ => 0)) := by decide

end Reconcile.FactRenaming
