import Graph.Construction
import Graph.Claims
import Graph.GraphPolicy
import Graph.ForwardDemands
import Graph.Execution
import Graph.IncomingConsensus
import Graph.ForcedGroupsReference
import Graph.SupportedChoices
import Graph.Driver
import Graph.Requirements
import Graph.Provenance
import Lean
import Mathlib.Data.Finset.Sort

/-! Oracle for the `Policy` family: runs the fixtures in `policy-fixtures.json` through the
selection models, one mode per request: support, groups, strongly connected components,
consensus, claims, construction, selection, preferred streams, forward pruning, driver,
provenance, requirements and execution. -/

namespace Reconcile.PolicyOracle

open Reconcile.Policy Lean

structure ConsensusFixture where
  name : String
  labels : List Nat
  queries : List Nat
  deriving FromJson

structure ConsensusObservation where
  name : String
  tag : String
  label : Option Nat
  answers : List Bool
  deriving ToJson

structure ClaimsFixture where
  name : String
  mask : Nat
  insertions : Array Nat
  queries : List Nat
  deriving FromJson

structure ClaimsState where
  modes : List Nat
  answers : List Bool
  compact : Bool
  deriving ToJson

structure ClaimsObservation where
  name : String
  states : Array ClaimsState
  deriving ToJson

private def observeClaims (store : Reconcile.Claims.Store) (queries : List Nat) : ClaimsState :=
  { modes := (Reconcile.Claims.decode store).sort (· ≤ ·)
    answers := queries.map (Reconcile.Claims.has store)
    compact := match store with | .compact _ => true | .expanded _ => false }

structure ConstructionFixture where
  name : String
  dependencies : Array (Array Nat)
  retained : Array Bool
  deriving FromJson

structure ConstructionObservation where
  name : String
  order : Option (List Nat)
  deriving ToJson

structure PolicyFixture where
  name : String
  domains : Domains
  deriving FromJson

structure GroupObservation where
  name : String
  labels : List Nat
  deriving ToJson

structure SccFixture where
  name : String
  edges : Array (List Nat)
  deriving FromJson

structure PreferredFixture where
  name : String
  domains : Domains
  preferred : Array (List Nat)
  deriving FromJson

structure PolicyObservation where
  name : String
  plans : List (List Nat)
  scores : List Nat
  deriving ToJson


structure DriverFixture where
  name : String
  plans : List Reconcile.Driver.Candidate
  ordinary : Array (Option Nat)
  replays : Array (Option Nat)
  deriving FromJson

structure DriverObservation where
  name : String
  result : Reconcile.Driver.Result
  deriving ToJson

structure ProvenanceFixture where
  name : String
  facts : Reconcile.Provenance.Facts
  deriving FromJson

structure ProvenanceObservation where
  name : String
  decision : Reconcile.Provenance.Decision
  deriving ToJson

structure FactFixture where
  name : String
  seeds : Array Nat
  implications : Array (Array Nat)
  deriving FromJson

structure FactObservation where
  name : String
  closed : List Nat
  deriving ToJson

structure InputBinding where
  choice : Nat
  writer : Nat
  exposed : Nat
  storage : Nat
  mode : Nat
  fixed : Bool
  palette : Array Nat
  construction : List Requirement
  deriving FromJson

structure Action where
  id : Nat
  revision : Nat
  type : String
  node : Nat
  exposed : Nat
  storage : Nat
  mode : Nat
  deriving FromJson

structure ExecutionFixture where
  name : String
  id : Nat
  bindings : Array InputBinding
  events : Array Action
  deriving FromJson

structure ExecutionState where
  id : Nat
  revision : Nat
  phase : String
  bindings : List (List Nat)
  checked : List Nat
  claims : List (List Nat)
  deriving ToJson

structure ExecutionObservation where
  name : String
  states : Array ExecutionState
  deriving ToJson

private def bindingOf (input : InputBinding) : Reconcile.Execution.Binding := {
  choice := input.choice, writer := input.writer, exposed := input.exposed,
  storage := input.storage, mode := input.mode, palette := input.palette.toList.toFinset,
  fixed := input.fixed, construction := input.construction }

private def phaseName : Reconcile.Execution.Phase → String
  | .publishing => "publishing"
  | .checking => "checking"
  | .done => "done"
  | .rejected => "rejected"

private def observe (s : Reconcile.Execution.State) : ExecutionState :=
  let nodes := s.domain.sort (· ≤ ·)
  { id := s.id
    revision := s.revision
    phase := phaseName s.phase
    bindings := nodes.map fun n =>
      let b := s.bindings n
      [b.choice, b.writer, b.exposed, b.storage, b.mode]
    checked := if s.phase = .checking then s.checked.sort (· ≤ ·) else []
    claims := nodes.map fun n =>
      ((s.claims.filter (fun p => p.1 = n)).image Prod.snd).sort (· ≤ ·) }

private def step (s : Reconcile.Execution.State) (a : Action) : Except String Reconcile.Execution.State := do
  let r : Reconcile.Execution.Receipt := ⟨a.id, a.revision⟩
  if ¬ Reconcile.Execution.current s r ∨ s.phase = .done ∨ s.phase = .rejected then return s
  match a.type with
  | "published" => return Reconcile.Execution.published s r
  | "checked" => return Reconcile.Execution.verify s r a.node
  | "finish" => return Reconcile.Execution.finish s r
  | "reject" => return { s with phase := .rejected }
  | "rebind" =>
    if s.phase ≠ .checking then return s
    return (Reconcile.Execution.rebind s r a.node a.exposed a.storage a.mode).getD
      { s with phase := .rejected }
  | _ => .error "unknown execution event"

private def runExecution (f : ExecutionFixture) : Except String ExecutionObservation := do
  let fallback : Reconcile.Execution.Binding := ⟨0, 0, 0, 0, 0, ∅, false, []⟩
  let bindings := fun n => (f.bindings[n]?).map bindingOf |>.getD fallback
  let domain := Finset.range f.bindings.size
  let mut s : Reconcile.Execution.State := {
    id := f.id, revision := 0, phase := .publishing, domain, bindings, checked := ∅,
    claims := ((List.range f.bindings.size).map fun n => (n, (bindings n).mode)).toFinset }
  let mut states := #[observe s]
  for action in f.events do
    s ← step s action
    states := states.push (observe s)
  return { name := f.name, states }

def run (args : List String) : IO UInt32 := do
  let content ← IO.FS.readFile (args.headD "lean/fixtures/policy-fixtures.json")
  let result : Except String Json := do
    let input ← Json.parse content
    match args[1]?.getD "selection" with
    | "support" =>
      let fixtures ← fromJson? (α := Array PolicyFixture) input
      return toJson (fixtures.map fun fixture =>
        let problem := Reconcile.ForcedGroups.fromDomains fixture.domains
        let live := Reconcile.SupportedChoices.survivors problem
        ({ name := fixture.name, labels := live.sort (· ≤ ·) } : GroupObservation))
    | "groups" =>
      let fixtures ← fromJson? (α := Array PolicyFixture) input
      return toJson (fixtures.map fun fixture =>
        let problem := Reconcile.ForcedGroups.fromDomains fixture.domains
        let partition := Reconcile.ForcedGroups.referencePartition problem
        ({ name := fixture.name,
           labels := (List.range problem.literals.card).map partition.classOf } : GroupObservation))
    | "scc" =>
      let fixtures ← fromJson? (α := Array SccFixture) input
      return toJson (fixtures.map fun fixture =>
        let graph : Reconcile.FiniteReachability.Graph := {
          vertices := Finset.range fixture.edges.size
          next := fun source => (fixture.edges[source]?.getD []).toFinset.filter
            fun target => target < fixture.edges.size
          admitted := by
            intro source target ht
            exact Finset.mem_range.mpr (Finset.mem_filter.mp ht).2 }
        let labels := Reconcile.FiniteReachability.cachedLabels graph fixture.edges.size
        ({ name := fixture.name, labels := (List.range fixture.edges.size).map labels.get } : GroupObservation))
    | "consensus" =>
      let fixtures ← fromJson? (α := Array ConsensusFixture) input
      return toJson (fixtures.map fun fixture =>
        let summary := Reconcile.IncomingConsensus.summarize fixture.labels
        let (tag, label) := match summary with
          | .empty => ("empty", none)
          | .one label => ("one", some label)
          | .conflict => ("conflict", none)
        ({ name := fixture.name, tag, label,
           answers := fixture.queries.map fun query => decide (Reconcile.IncomingConsensus.accepts summary query)
         } : ConsensusObservation))
    | "claims" =>
      let fixtures ← fromJson? (α := Array ClaimsFixture) input
      return toJson (fixtures.map fun fixture => Id.run do
        let mut store := Reconcile.Claims.Store.compact fixture.mask
        let mut states := #[observeClaims store fixture.queries]
        for mode in fixture.insertions do
          store := Reconcile.Claims.add store mode
          states := states.push (observeClaims store fixture.queries)
        return ({ name := fixture.name, states } : ClaimsObservation))
    | "construction" =>
      let fixtures ← fromJson? (α := Array ConstructionFixture) input
      return toJson (fixtures.map fun fixture =>
        let nodes := List.range fixture.dependencies.size
        let retained := (nodes.filter fun node => fixture.retained[node]?.getD false).toFinset
        let deps := fun node => (fixture.dependencies[node]?.getD #[]).toList
        ({ name := fixture.name, order := Reconcile.Construction.schedule deps retained nodes } : ConstructionObservation))
    | "selection" =>
      let fixtures ← fromJson? (α := Array PolicyFixture) input
      return toJson (fixtures.map fun fixture =>
        let plans := rankedPlans fixture.domains
        ({ name := fixture.name, plans := plans.map (·.map Choice.identity), scores := plans.map score } : PolicyObservation))
    | "preferred" =>
      let fixtures ← fromJson? (α := Array PreferredFixture) input
      return toJson (fixtures.map fun fixture =>
        let plans := rankedPreferred fixture.domains fun rank node =>
          (fixture.preferred[rank]?.getD []).contains node
        ({ name := fixture.name, plans := plans.map (·.map Choice.identity), scores := plans.map score } : PolicyObservation))
    | "forward" =>
      let fixtures ← fromJson? (α := Array PreferredFixture) input
      return toJson (fixtures.map fun fixture =>
        let plans := Reconcile.ForwardDemands.ranked fixture.domains fun rank node =>
          (fixture.preferred[rank]?.getD []).contains node
        ({ name := fixture.name, plans := plans.map (·.map Choice.identity), scores := plans.map score } : PolicyObservation))
    | "driver" =>
      let fixtures ← fromJson? (α := Array DriverFixture) input
      return toJson (fixtures.map fun fixture =>
        let reports : Reconcile.Driver.Reports := fun candidate replay =>
          ((if replay then fixture.replays else fixture.ordinary)[candidate.id]?).getD none
        ({ name := fixture.name, result := Reconcile.Driver.run reports fixture.plans none } : DriverObservation))
    | "provenance" =>
      let fixtures ← fromJson? (α := Array ProvenanceFixture) input
      return toJson (fixtures.map fun fixture =>
        ({ name := fixture.name, decision := Reconcile.Provenance.choose fixture.facts } : ProvenanceObservation))
    | "requirements" =>
      let fixtures ← fromJson? (α := Array FactFixture) input
      return toJson (fixtures.map fun fixture =>
        let successors := fun n => (fixture.implications[n]?.getD #[]).toList
        let closed := Reconcile.Requirements.close successors fixture.seeds.toList
          (Finset.range fixture.implications.size)
        ({ name := fixture.name, closed := closed.sort (· ≤ ·) } : FactObservation))
    | "execution" =>
      let fixtures ← fromJson? (α := Array ExecutionFixture) input
      return toJson (← fixtures.mapM runExecution)
    | _ => .error "unknown oracle mode"
  match result with
  | .error error => IO.eprintln error; return 1
  | .ok output => IO.println output.compress; return 0

end Reconcile.PolicyOracle
