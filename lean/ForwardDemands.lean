import ActiveDemands

namespace Reconcile.ForwardDemands

open Policy ActiveDemands IncomingConsensus

/-- Only already-selected choices contribute to the maintained summary. -/
def numbered (before : Plan) : List (Nat × Choice) := before.zipIdx.map Prod.swap

/-- Additional look-ahead only; self/backward checks remain the selector's responsibility. -/
def guard (before : Plan) (choice : Choice) : Bool :=
  (forward before.length choice).all fun edge =>
    decide (accepts ((maintained (numbered before)).1 edge.node) edge.identity)

/-- Feasibility makes every active demand agree with a proposed outgoing demand. -/
theorem completion_accepts {before suffix : Plan} {choice : Choice}
    (hf : feasible (before ++ choice :: suffix)) : guard before choice = true := by
  simp only [guard, List.all_eq_true, decide_eq_true_eq]
  intro edge he
  rw [maintained_iff_scan]
  intro entry hm _ prior hp hn
  obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hm
  have hmem := List.fst_mem_of_mem_zipIdx hpair
  have hprior := hf.2 pair.1 (List.mem_append_left _ hmem) prior hp
  have hchoice := hf.2 choice (by simp) edge (List.mem_filter.mp he).1
  rw [hn] at hprior
  exact Option.some.inj (hprior.symm.trans hchoice)

theorem rejected_no_completion {before : Plan} {choice : Choice}
    (h : guard before choice = false) (suffix : Plan) :
    ¬ feasible (before ++ choice :: suffix) := by
  intro hf
  have := completion_accepts hf
  simp [h] at this

/-- Ordered depth-first enumeration, with the new guard before recursive descent. -/
def search (prune : Bool) (before : Plan) : Domains → List Plan
  | [] => [before].filter check
  | domain :: rest => domain.flatMap fun choice =>
      if prune && !guard before choice then []
      else search prune (before ++ [choice]) rest

theorem reference_eq (before : Plan) (domains : Domains) :
    search false before domains = ((assignments domains).map (before ++ ·)).filter check := by
  induction domains generalizing before with
  | nil => simp [search, assignments]
  | cons domain rest ih =>
    simp [search, assignments, ih, List.map_flatMap, List.filter_flatMap,
      List.map_map, Function.comp_def, List.append_assoc]

/-- Pruning removes empty subtrees without changing multiplicity or traversal order. -/
theorem search_eq (before : Plan) (domains : Domains) :
    search true before domains = search false before domains := by
  induction domains generalizing before with
  | nil => rfl
  | cons domain rest ih =>
    simp only [search, Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    congr 1
    funext choice
    cases hg : guard before choice with
    | true => simp [ih]
    | false =>
      simp only [Bool.not_false, ↓reduceIte]
      rw [reference_eq]
      symm
      apply List.filter_eq_nil_iff.mpr
      intro plan hp
      obtain ⟨suffix, _, rfl⟩ := List.mem_map.mp hp
      simpa only [Bool.not_eq_true, ← check_iff_feasible, List.append_assoc,
        List.singleton_append] using rejected_no_completion hg suffix

theorem search_feasiblePlans (domains : Domains) :
    search true [] domains = feasiblePlans domains := by
  rw [search_eq, reference_eq]
  simp [feasiblePlans]

/-- The same score tiers and preference facts give exactly the full ranked stream. -/
def ranked (domains : Domains) (preferred : Nat → Nat → Bool) : List Plan :=
  (List.range (domains.length + 1)).reverse.flatMap fun rank =>
    (search true [] (orderedDomains domains (preferred rank) 0)).filter fun plan =>
      decide (score plan = rank)

theorem ranked_eq (domains : Domains) (preferred : Nat → Nat → Bool) :
    ranked domains preferred = rankedPreferred domains preferred := by
  simp only [ranked, rankedPreferred, search_feasiblePlans]

/-- Count attempted extensions, including guards, but excluding materialized output. -/
def visits (prune : Bool) (before : Plan) : Domains → Nat
  | [] => 0
  | domain :: rest => (domain.map fun choice =>
      1 + if prune && !guard before choice then 0
      else visits prune (before ++ [choice]) rest).sum

def witness : Domains := [
  [{ identity := 0, storage := 0, retained := true, required := [⟨3, 7⟩] }],
  [{ identity := 1, storage := 1, retained := true, required := [⟨3, 8⟩] },
   { identity := 10, storage := 1, retained := false, required := [] }],
  [{ identity := 20, storage := 2, retained := true, required := [] },
   { identity := 21, storage := 2, retained := true, required := [] }],
  [{ identity := 7, storage := 3, retained := true, required := [] },
   { identity := 8, storage := 3, retained := true, required := [] }]]

/-- Static support admits both demands, yet the early contradiction removes work. -/
theorem strict_work_witness :
    (search true [] witness).length = 2 ∧
    search true [] witness = search false [] witness ∧
    visits true [] witness < visits false [] witness := by decide

/-- Contradictions inside a single choice may escape this deliberately partial guard. -/
def contradictory : Choice :=
  { identity := 0, storage := 0, retained := true, required := [⟨1, 7⟩, ⟨1, 8⟩] }

example : guard [] contradictory = true := by decide
example : check [contradictory, freshChoice 7] = false := by decide

example : guard [contradictory]
    { identity := 1, storage := 1, retained := true, required := [⟨1, 7⟩] } = true := by decide

-- A conflict at a future target rejects every proposed identity, including one of
-- the identities originally contributing to that conflict.
example : guard
    [{ identity := 0, storage := 0, retained := true, required := [⟨2, 7⟩, ⟨2, 8⟩] }]
    { identity := 1, storage := 1, retained := true, required := [⟨2, 7⟩] } = false := by decide

-- Native correspondence: the runtime's incoming table must equal maintained for
-- its selected before, with the existing reversible trail. Requirements and identity
-- labels are private, stable facts for this stream. The guard reads no native object.
-- Preserve static membership, self/backward checks, storage/group checks, score bounds,
-- callback invocation for every original tier, generator order and restoration.
-- This finite enumerator establishes empty-subtree removal, not native publication
-- correctness or equality of JavaScript observations by itself.

end Reconcile.ForwardDemands
