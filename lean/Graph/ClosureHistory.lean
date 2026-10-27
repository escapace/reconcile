import Graph.Requirements

/-! Online requirement closure (`RequirementClosure` in `src/graph/requirements.ts`): rules and
required facts arrive as a history of events, and `eventStep` expands a newly required fact, or the
consequence of a rule whose antecedent is known, with the eager queue. After any history, `known`
is the least closure of the required facts under the rules received (`replay_known`), so every
arrival order derives the same closure. `FactRenaming` relabels these histories. -/
namespace Reconcile.OnlineRequirements

open RequirementAdmission RequirementPropagation Requirements

abbrev Graph := Nat → List Nat

/-- `imply` appends the consequence to its antecedent's row, as the runtime does, even when the row
already holds it; admission skips the repeat. -/
def add (graph : Graph) (source target : Nat) : Graph :=
  fun node => if node = source then graph node ++ [target] else graph node

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

def eventStep (fuel : Nat) (state : Online) : Event → Online
  | .require fact => expand fuel state fact
  | .imply source target =>
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

/-! ## The closure after any history -/

/-- The facts an event names. -/
def Event.facts : Event → List Nat
  | .require fact => [fact]
  | .imply source target => [source, target]

/-- The facts a history requires, in order. -/
def required (events : List Event) : List Nat :=
  events.flatMap fun
    | .require fact => [fact]
    | .imply .. => []

def replay (fuel : Nat) (events : List Event) : Online := events.foldl (eventStep fuel) empty

/-- `known` is the least closure of `seeds` under `graph`, and the rules stay inside `domain`. -/
def Least (domain : Finset Nat) (seeds : List Nat) (state : Online) : Prop :=
  state.known ⊆ domain ∧ (∀ fact, ∀ next ∈ state.graph fact, next ∈ domain) ∧
    (∀ fact ∈ seeds, fact ∈ state.known) ∧ Closed state.graph state.known ∧
    ∀ facts, Closed state.graph facts → (∀ fact ∈ seeds, fact ∈ facts) →
      state.known ⊆ facts

theorem closed_of_add {graph : Graph} {source target : Nat} {facts : Finset Nat}
    (h : Closed (add graph source target) facts) : Closed graph facts := by
  intro fact hf next hn
  apply h fact hf next
  by_cases hs : fact = source
  · subst hs; simp [add, hn]
  · simp [add, hs, hn]

/-- Expanding `fact` from known facts whose successors are known or `fact` admits a closed set,
inside the domain and inside every closed set that holds the known facts and `fact`. -/
theorem expand_least (domain : Finset Nat) (fuel : Nat) (state : Online) (fact : Nat)
    (enough : domain.card ≤ fuel) (inside : state.known ⊆ domain)
    (bounded : ∀ fact, ∀ next ∈ state.graph fact, next ∈ domain) (hfact : fact ∈ domain)
    (base : ∀ known ∈ state.known, ∀ next ∈ state.graph known,
      next ∈ state.known ∨ next = fact) :
    let after := expand fuel state fact
    after.graph = state.graph ∧ after.known ⊆ domain ∧ state.known ⊆ after.known ∧
      fact ∈ after.known ∧ Closed state.graph after.known ∧
      ∀ facts, state.known ⊆ facts → fact ∈ facts → Closed state.graph facts →
        after.known ⊆ facts := by
  have startPending : ∀ facts : Finset Nat, fact ∈ facts →
      ∀ x ∈ (start state.known [fact]).pending, x ∈ facts := fun facts hf x hx => by
    have := ((admit_mem _ _ _).mp hx).1
    simp only [List.mem_singleton] at this
    exact this ▸ hf
  have startAdmitted : ∀ facts : Finset Nat, state.known ⊆ facts → fact ∈ facts →
      ∀ x ∈ (start state.known [fact]).admitted, x ∈ facts := fun facts hk hf x hx => by
    simp only [start, Finset.mem_union, List.mem_toFinset, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hk hx
    · exact hf
  have drained : (run state.graph fuel (start state.known [fact])).pending = [] :=
    run_drains state.graph state.known domain (fun x _ next hn => bounded x next hn) fuel _
      (start_invariant _ _) (startAdmitted domain inside hfact) (by simpa [start] using enough)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact run_admitted_closed state.graph (· ∈ domain) (fun x _ next hn => bounded x next hn)
      fuel _ (startPending domain hfact) (startAdmitted domain inside hfact)
  · exact fun x hx => run_admitted_mono state.graph fuel _ (by simp [start, hx])
  · exact run_admitted_mono state.graph fuel _ (by simp [start])
  · exact run_closed state.graph state.known [fact] fuel (by simpa using base) drained
  · intro facts hk hf hc
    exact run_admitted_closed state.graph (· ∈ facts) hc fuel _ (startPending facts hf)
      (startAdmitted facts hk hf)

/-- Each event keeps `known` the least closure of the facts required so far under the rules
received so far. -/
theorem eventStep_least (domain : Finset Nat) (fuel : Nat) (seeds : List Nat) (state : Online)
    (event : Event) (enough : domain.card ≤ fuel)
    (inDomain : ∀ fact ∈ event.facts, fact ∈ domain)
    (h : Least domain seeds state) :
    Least domain (seeds ++ required [event]) (eventStep fuel state event) := by
  obtain ⟨inside, bounded, hseeds, hclosed, hleast⟩ := h
  cases event with
  | require fact =>
    have hfact : fact ∈ domain := inDomain fact (by simp [Event.facts])
    obtain ⟨hgraph, inside', grows, has, closed', least'⟩ :=
      expand_least domain fuel state fact enough inside bounded hfact
        (fun known hk next hn => Or.inl (hclosed known hk next hn))
    simp only [eventStep, required, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine ⟨inside', hgraph ▸ bounded, ?_, hgraph ▸ closed', ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact grows (hseeds x hx)
      · exact (List.mem_singleton.mp hx) ▸ has
    · intro facts hc hs
      rw [hgraph] at hc
      exact least' facts (hleast facts hc fun x hx => hs x (by simp [hx]))
        (hs fact (by simp)) hc
  | imply source target =>
    have htarget : target ∈ domain := inDomain target (by simp [Event.facts])
    simp only [required, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have bounded' : ∀ fact, ∀ next ∈ add state.graph source target fact, next ∈ domain := by
      intro fact next hn
      by_cases hs : fact = source
      · simp only [add, hs, ↓reduceIte, List.mem_append, List.mem_singleton] at hn
        rcases hn with hn | rfl
        · exact bounded source next hn
        · exact htarget
      · simp only [add, hs, ↓reduceIte] at hn
        exact bounded fact next hn
    by_cases active : source ∈ state.known
    · obtain ⟨hgraph, inside', grows, has, closed', least'⟩ :=
        expand_least domain fuel { state with graph := add state.graph source target } target
          enough inside bounded' htarget (by
            intro known hk next hn
            by_cases hs : known = source
            · simp only [add, hs, ↓reduceIte, List.mem_append, List.mem_singleton] at hn
              rcases hn with hn | rfl
              · exact Or.inl (hclosed source (hs ▸ hk) next hn)
              · exact Or.inr rfl
            · simp only [add, hs, ↓reduceIte] at hn
              exact Or.inl (hclosed known hk next hn))
      simp only [eventStep, active, ↓reduceIte]
      refine ⟨inside', hgraph ▸ bounded', fun x hx => grows (hseeds x hx), hgraph ▸ closed',
        ?_⟩
      intro facts hc hs
      rw [hgraph] at hc
      have known := hleast facts (closed_of_add hc) hs
      exact least' facts known (hc source (known active) target (by simp [add])) hc
    · simp only [eventStep, active, ↓reduceIte]
      refine ⟨inside, bounded', hseeds, ?_,
        fun facts hc hs => hleast facts (closed_of_add hc) hs⟩
      intro fact hf next hn
      have hs : fact ≠ source := fun same => active (same ▸ hf)
      simp only [add, hs, ↓reduceIte] at hn
      exact hclosed fact hf next hn

theorem foldl_least (domain : Finset Nat) (fuel : Nat) (enough : domain.card ≤ fuel)
    (events : List Event)
    (inDomain : ∀ event ∈ events, ∀ fact ∈ event.facts, fact ∈ domain)
    (seeds : List Nat) (state : Online) (h : Least domain seeds state) :
    Least domain (seeds ++ required events) (events.foldl (eventStep fuel) state) := by
  induction events generalizing seeds state with
  | nil => simpa [required] using h
  | cons event rest ih =>
    have step := eventStep_least domain fuel seeds state event enough
      (inDomain event List.mem_cons_self) h
    have tail := ih (fun e he => inDomain e (List.mem_cons_of_mem event he)) _ _ step
    have split : required (event :: rest) = required [event] ++ required rest := by
      simp [required]
    simpa [List.foldl_cons, split, List.append_assoc] using tail

/-- After any history whose facts lie in `domain`, with a step for each of its facts, `known` is
`close` from scratch: the least closure of the required facts under the rules received. -/
theorem replay_known (domain : Finset Nat) (fuel : Nat) (events : List Event)
    (enough : domain.card ≤ fuel)
    (inDomain : ∀ event ∈ events, ∀ fact ∈ event.facts, fact ∈ domain) :
    (replay fuel events).known =
      close (replay fuel events).graph (required events) domain := by
  have initial : Least domain [] empty :=
    ⟨by simp [empty], by simp [empty], by simp, by simp [empty, Closed],
      fun _ _ _ => by simp [empty]⟩
  obtain ⟨inside, bounded, hseeds, hclosed, hleast⟩ :=
    foldl_least domain fuel enough events inDomain [] empty initial
  simp only [List.nil_append] at inside bounded hseeds hclosed hleast
  have seedsIn : ∀ fact ∈ required events, fact ∈ domain := fun fact hf =>
    inside (hseeds fact hf)
  apply Finset.Subset.antisymm
  · exact hleast _ (close_closed _ _ domain seedsIn fun fact _ next hn => bounded fact next hn)
      (close_seeds _ _ domain)
  · exact close_least _ _ domain _ hclosed hseeds

end Reconcile.OnlineRequirements
