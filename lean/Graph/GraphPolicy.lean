import Mathlib.Data.List.Basic
import Lean

/-! Closed, finite selection constraints and the reference model of the ranked selection stream,
to which `CompactImmutable` relates the masks of `src/graph/immutable-selection.ts`. Native capture
supplies the identity and storage labels. -/

namespace Reconcile.Policy

structure Requirement where
  node : Nat
  identity : Nat
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

structure Choice where
  identity : Nat
  storage : Nat
  retained : Bool
  required : List Requirement
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

abbrev Plan := List Choice
abbrev Domains := List (List Choice)

def allowed : Domains → Plan → Prop
  | [], [] => True
  | domain :: domains, choice :: choices => choice ∈ domain ∧ allowed domains choices
  | _, _ => False

def assignments : Domains → List Plan
  | [] => [[]]
  | domain :: rest => domain.flatMap fun choice => (assignments rest).map (choice :: ·)

theorem assignments_allowed (domains : Domains) (plan : Plan) :
    plan ∈ assignments domains ↔ allowed domains plan := by
  induction domains generalizing plan with
  | nil => cases plan <;> simp [assignments, allowed]
  | cons domain rest ih =>
    cases plan with
    | nil => simp [assignments, allowed]
    | cons choice choices =>
      simp only [assignments, List.mem_flatMap, List.mem_map, List.cons.injEq, allowed]
      constructor
      · rintro ⟨head, hh, tail, ht, he, hs⟩
        subst head; subst tail
        exact ⟨hh, (ih choices).mp ht⟩
      · rintro ⟨hh, ht⟩
        exact ⟨choice, hh, choices, (ih choices).mpr ht, rfl, rfl⟩

def feasible (plan : Plan) : Prop :=
  plan.Pairwise (fun left right => left.storage ≠ right.storage) ∧
  ∀ choice ∈ plan, ∀ edge ∈ choice.required,
    (plan[edge.node]?).map Choice.identity = some edge.identity

def check (plan : Plan) : Bool :=
  decide (plan.Pairwise (fun left right => left.storage ≠ right.storage)) &&
  plan.all fun choice => choice.required.all fun edge =>
    decide ((plan[edge.node]?).map Choice.identity = some edge.identity)

theorem check_iff_feasible (plan : Plan) : check plan = true ↔ feasible plan := by
  simp [check, feasible, List.all_eq_true]

def feasiblePlans (domains : Domains) : List Plan := (assignments domains).filter check

theorem feasiblePlans_exact (domains : Domains) (plan : Plan) :
    plan ∈ feasiblePlans domains ↔ allowed domains plan ∧ feasible plan := by
  simp [feasiblePlans, assignments_allowed, check_iff_feasible]

def score (plan : Plan) : Nat := (plan.map fun choice => if choice.retained then 1 else 0).sum

-- Earliest plan wins equal scores, matching traversal-order tie breaking.
def best : List Plan → Option Plan
  | [] => none
  | plan :: rest =>
    match best rest with
    | none => some plan
    | some next => some (if score next ≤ score plan then plan else next)

theorem best_mem {plans : List Plan} {plan : Plan} (h : best plans = some plan) : plan ∈ plans := by
  induction plans generalizing plan with
  | nil => simp [best] at h
  | cons head rest ih =>
    simp only [best] at h
    split at h
    · cases h; simp
    · rename_i next hn
      split at h
      · cases h; simp
      · cases h; exact List.mem_cons_of_mem head (ih hn)

theorem best_none (plans : List Plan) : best plans = none ↔ plans = [] := by
  cases plans with
  | nil => simp [best]
  | cons head rest => simp only [best]; split <;> simp

theorem best_maximum {plans : List Plan} {plan : Plan} (h : best plans = some plan) :
    ∀ other ∈ plans, score other ≤ score plan := by
  induction plans generalizing plan with
  | nil => simp [best] at h
  | cons head rest ih =>
    simp only [best] at h
    split at h
    · rename_i hn
      have hr := (best_none rest).mp hn
      subst rest; cases h
      simp
    · rename_i next hn
      have hm := ih hn
      split at h
      · rename_i hs
        cases h
        intro other ho
        rcases List.mem_cons.mp ho with he | he
        · subst other; exact Nat.le_refl _
        · exact Nat.le_trans (hm other he) hs
      · rename_i hs
        cases h
        intro other ho
        rcases List.mem_cons.mp ho with he | he
        · subst other; exact Nat.le_of_lt (Nat.lt_of_not_ge hs)
        · exact hm other he

def select (domains : Domains) : Option Plan := best (feasiblePlans domains)

theorem select_sound {domains : Domains} {plan : Plan} (h : select domains = some plan) :
    allowed domains plan ∧ feasible plan :=
  (feasiblePlans_exact domains plan).mp (best_mem h)

theorem select_optimal {domains : Domains} {plan : Plan} (h : select domains = some plan)
    {other : Plan} (ha : allowed domains other) (hf : feasible other) : score other ≤ score plan :=
  best_maximum h other ((feasiblePlans_exact domains other).mpr ⟨ha, hf⟩)

theorem select_complete (domains : Domains) :
    select domains = none ↔ ¬ ∃ plan, allowed domains plan ∧ feasible plan := by
  rw [select, best_none]
  simp only [List.eq_nil_iff_forall_not_mem, feasiblePlans_exact, not_exists]


theorem allowed_length {domains : Domains} {plan : Plan} (h : allowed domains plan) :
    plan.length = domains.length := by
  induction domains generalizing plan with
  | nil => cases plan <;> simp_all [allowed]
  | cons domain rest ih =>
    cases plan with
    | nil => simp [allowed] at h
    | cons choice choices =>
      have ht := ih h.2
      simpa using ht

theorem score_le_length (plan : Plan) : score plan ≤ plan.length := by
  induction plan with
  | nil => simp [score]
  | cons choice rest ih =>
    simp only [score, List.map_cons, List.sum_cons, List.length_cons] at *
    split <;> omega

-- The executable reference streams score buckets in descending order.
def rankedPlans (domains : Domains) : List Plan :=
  (List.range (domains.length + 1)).reverse.flatMap fun rank =>
    (feasiblePlans domains).filter fun plan => decide (score plan = rank)

theorem rankedPlans_exact (domains : Domains) (plan : Plan) :
    plan ∈ rankedPlans domains ↔ allowed domains plan ∧ feasible plan := by
  simp only [rankedPlans, List.mem_flatMap, List.mem_reverse, List.mem_range,
    List.mem_filter, decide_eq_true_eq, feasiblePlans_exact]
  constructor
  · rintro ⟨rank, _, hp, _⟩
    exact hp
  · intro h
    have hs := score_le_length plan
    have hl := allowed_length h.1
    exact ⟨score plan, by omega, h, rfl⟩

-- Feedback changes domain order only after an entire score tier is exhausted.
-- Model the resulting per-tier preferences as supplied finite facts, not host code.
def freshFirst (domain : List Choice) : List Choice :=
  domain.filter (fun choice => !choice.retained) ++ domain.filter Choice.retained

@[simp] theorem freshFirst_mem (domain : List Choice) (choice : Choice) :
    choice ∈ freshFirst domain ↔ choice ∈ domain := by
  cases hr : choice.retained <;> simp [freshFirst, hr]

def orderedDomains : Domains → (Nat → Bool) → Nat → Domains
  | [], _, _ => []
  | domain :: rest, preferred, index =>
    (if preferred index then freshFirst domain else domain) :: orderedDomains rest preferred (index + 1)

@[simp] theorem orderedDomains_allowed (domains : Domains) (preferred : Nat → Bool)
    (index : Nat) (plan : Plan) :
    allowed (orderedDomains domains preferred index) plan ↔ allowed domains plan := by
  induction domains generalizing plan index with
  | nil => cases plan <;> simp [orderedDomains, allowed]
  | cons domain rest ih =>
    cases plan with
    | nil => simp [orderedDomains, allowed]
    | cons choice choices =>
      simp only [orderedDomains, allowed]
      rw [ih]
      cases preferred index <;> simp

def rankedPreferred (domains : Domains) (preferred : Nat → Nat → Bool) : List Plan :=
  (List.range (domains.length + 1)).reverse.flatMap fun rank =>
    (feasiblePlans (orderedDomains domains (preferred rank) 0)).filter fun plan => decide (score plan = rank)

theorem rankedPreferred_exact (domains : Domains) (preferred : Nat → Nat → Bool) (plan : Plan) :
    plan ∈ rankedPreferred domains preferred ↔ allowed domains plan ∧ feasible plan := by
  simp only [rankedPreferred, List.mem_flatMap, List.mem_reverse, List.mem_range,
    List.mem_filter, decide_eq_true_eq, feasiblePlans_exact, orderedDomains_allowed]
  constructor
  · rintro ⟨rank, _, hp, _⟩
    exact hp
  · intro h
    have hs := score_le_length plan
    have hl := allowed_length h.1
    exact ⟨score plan, by omega, h, rfl⟩


-- These are exactly the suffix score bounds used by the streaming selector.
-- They depend only on finite domains, not on native object behavior.
def minimumScore (domains : Domains) : Nat :=
  (domains.map fun domain => if domain.all Choice.retained then 1 else 0).sum

def maximumScore (domains : Domains) : Nat :=
  (domains.map fun domain => if domain.any Choice.retained then 1 else 0).sum

theorem allowed_score_bounds {domains : Domains} {plan : Plan}
    (h : allowed domains plan) : minimumScore domains ≤ score plan ∧
      score plan ≤ maximumScore domains := by
  induction domains generalizing plan with
  | nil => cases plan <;> simp_all [allowed, minimumScore, maximumScore, score]
  | cons domain domains ih =>
    cases plan with
    | nil => simp [allowed] at h
    | cons choice choices =>
      obtain ⟨hm, ht⟩ := h
      obtain ⟨hl, hu⟩ := ih ht
      have ha : domain.all Choice.retained = true → choice.retained = true :=
        fun h => (List.all_eq_true.mp h) choice hm
      have he : choice.retained = true → domain.any Choice.retained = true :=
        fun h => List.any_eq_true.mpr ⟨choice, hm, h⟩
      have hlow : (if domain.all Choice.retained then 1 else 0) ≤
          (if choice.retained then 1 else 0) := by
        cases hc : choice.retained <;> cases hm : domain.all Choice.retained <;>
          simp_all
      have hhigh : (if choice.retained then 1 else 0) ≤
          (if domain.any Choice.retained then 1 else 0) := by
        cases hc : choice.retained <;> cases heq : domain.any Choice.retained <;>
          simp_all
      exact ⟨Nat.add_le_add hlow hl, Nat.add_le_add hhigh hu⟩

theorem score_append (before suffix : Plan) :
    score (before ++ suffix) = score before + score suffix := by
  simp [score, List.map_append, List.sum_append]

-- A completion at the current score tier survives both numeric pruning tests.
-- Ownership and requirement pruning are separate obligations.
theorem completion_survives_score_pruning {domains : Domains} {before suffix : Plan}
    {goal : Nat} (ha : allowed domains suffix) (hg : score (before ++ suffix) = goal) :
    score before + minimumScore domains ≤ goal ∧
      goal ≤ score before + maximumScore domains := by
  obtain ⟨hl, hu⟩ := allowed_score_bounds ha
  rw [score_append] at hg
  omega

-- An allowed full assignment supplies an in-domain witness at every chosen index.
theorem allowed_at {domains : Domains} {plan : Plan} (ha : allowed domains plan)
    {index : Nat} {choice : Choice} (hg : plan[index]? = some choice) :
    ∃ domain, domains[index]? = some domain ∧ choice ∈ domain := by
  induction domains generalizing plan index with
  | nil => cases plan <;> simp_all [allowed]
  | cons domain domains ih =>
    cases plan with
    | nil => simp [allowed] at ha
    | cons head tail =>
      cases index with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
        subst choice
        exact ⟨domain, rfl, ha.1⟩
      | succ index => exact ih ha.2 hg

-- No ownership or requirement check on a partial assignment may discard a
-- feasible completion: assigned dependencies already match, and future ones
-- have an allowed identity witness. This is the finite pruning boundary, not
-- a proof of the JavaScript stack/iterator implementation.
theorem completion_survives_prefix_pruning {domains : Domains} {plan : Plan}
    (ha : allowed domains plan) (hf : feasible plan) (count : Nat) :
    (plan.take count).Pairwise (fun left right => left.storage ≠ right.storage) ∧
    ∀ choice ∈ plan.take count, ∀ edge ∈ choice.required,
      if edge.node < count then
        ((plan.take count)[edge.node]?).map Choice.identity = some edge.identity
      else ∃ domain candidate, domains[edge.node]? = some domain ∧
        candidate ∈ domain ∧ candidate.identity = edge.identity := by
  refine ⟨hf.1.take, ?_⟩
  intro choice hc edge he
  have hm : choice ∈ plan := List.mem_of_mem_take hc
  have hr := hf.2 choice hm edge he
  split
  · rename_i hlt
    simpa only [List.getElem?_take_of_lt hlt] using hr
  · cases hg : plan[edge.node]? with
    | none => simp [hg] at hr
    | some candidate =>
      obtain ⟨domain, hd, hcand⟩ := allowed_at ha hg
      exact ⟨domain, candidate, hd, hcand, by simpa [hg] using hr⟩

-- Immutable compilation appends a private fresh option to every proposal domain.
-- Native capture supplies the distinct labels; freshness is not inferred from
-- JavaScript allocation semantics inside this model.
def freshChoice (label : Nat) : Choice :=
  { identity := label, storage := label, retained := false, required := [] }

def fallbackDomains (rows : List (Nat × Option Choice)) : Domains :=
  rows.map fun row => row.2.toList ++ [freshChoice row.1]

def freshAssignment (rows : List (Nat × Option Choice)) : Plan :=
  rows.map fun row => freshChoice row.1

theorem freshAssignment_allowed (rows : List (Nat × Option Choice)) :
    allowed (fallbackDomains rows) (freshAssignment rows) := by
  induction rows with
  | nil => trivial
  | cons row rows ih => simpa [fallbackDomains, freshAssignment, allowed] using ih

theorem freshAssignment_feasible (rows : List (Nat × Option Choice))
    (h : (rows.map Prod.fst).Nodup) : feasible (freshAssignment rows) := by
  constructor
  · simpa only [freshAssignment, List.pairwise_map, freshChoice] using
      (List.pairwise_map.mp (List.nodup_iff_pairwise_ne.mp h))
  · intro choice hc edge he
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp hc
    simp [freshChoice] at he

theorem fallback_select_exists (rows : List (Nat × Option Choice))
    (h : (rows.map Prod.fst).Nodup) :
    ∃ plan, select (fallbackDomains rows) = some plan := by
  cases hs : select (fallbackDomains rows) with
  | none =>
    exact False.elim ((select_complete _).mp hs
      ⟨freshAssignment rows, freshAssignment_allowed rows, freshAssignment_feasible rows h⟩)
  | some plan => exact ⟨plan, rfl⟩

/-! The head plan: every node takes the first choice of its domain. When it is feasible and
reaches the top score, it is the first plan of the ranked stream, so the driver may attempt
it before starting the search and resume the stream after it. -/

def headPlan : Domains → Option Plan
  | [] => some []
  | [] :: _ => none
  | (choice :: _) :: rest => (headPlan rest).map (choice :: ·)

/-- Each head is retained, or its domain offers no retained choice. -/
def HeadsMaximal : Domains → Prop
  | [] => True
  | [] :: rest => HeadsMaximal rest
  | (choice :: others) :: rest =>
    (choice.retained = true ∨ ∀ other ∈ choice :: others, other.retained = false) ∧
      HeadsMaximal rest

theorem headPlan_first {domains : Domains} {plan : Plan} (h : headPlan domains = some plan) :
    (assignments domains).head? = some plan := by
  induction domains generalizing plan with
  | nil => simp_all [headPlan, assignments]
  | cons domain rest ih =>
    cases domain with
    | nil => simp [headPlan] at h
    | cons choice others =>
      obtain ⟨tail, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      have first := ih ht
      cases hr : assignments rest with
      | nil => simp [hr] at first
      | cons head more =>
        rw [hr] at first
        simp only [List.head?_cons, Option.some.injEq] at first
        subst first
        simp [assignments, hr]

theorem headPlan_allowed {domains : Domains} {plan : Plan} (h : headPlan domains = some plan) :
    allowed domains plan := by
  have first := headPlan_first h
  cases hr : assignments domains with
  | nil => simp [hr] at first
  | cons head more =>
    rw [hr] at first
    simp only [List.head?_cons, Option.some.injEq] at first
    subst first
    exact (assignments_allowed domains head).mp (by simp [hr])

theorem headPlan_score {domains : Domains} {plan : Plan} (h : headPlan domains = some plan)
    (maximal : HeadsMaximal domains) : score plan = maximumScore domains := by
  induction domains generalizing plan with
  | nil => simp_all [headPlan, score, maximumScore]
  | cons domain rest ih =>
    cases domain with
    | nil => simp [headPlan] at h
    | cons choice others =>
      obtain ⟨tail, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨top, more⟩ := maximal
      have tailScore := ih ht more
      simp only [score, maximumScore, List.map_cons, List.sum_cons] at tailScore ⊢
      rw [tailScore]
      congr 1
      rcases top with retained | none
      · have : (choice :: others).any Choice.retained = true :=
          List.any_eq_true.mpr ⟨choice, List.mem_cons_self, retained⟩
        simp [retained, this]
      · have hc := none choice List.mem_cons_self
        have : (choice :: others).any Choice.retained = false := by
          rw [Bool.eq_false_iff]
          intro hany
          obtain ⟨other, hm, ho⟩ := List.any_eq_true.mp hany
          simp [none other hm] at ho
        simp [hc, this]

theorem orderedDomains_none (domains : Domains) (index : Nat) :
    orderedDomains domains (fun _ => false) index = domains := by
  induction domains generalizing index with
  | nil => rfl
  | cons domain rest ih => simp [orderedDomains, ih]

theorem head_filter {α : Type} {plans : List α} {plan : α} {keep : α → Bool}
    (h : plans.head? = some plan) (hk : keep plan = true) :
    (plans.filter keep).head? = some plan := by
  cases plans with
  | nil => simp at h
  | cons head more =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    simp [hk]

theorem head_ranks {α : Type} {f : Nat → List α} {s : Nat} (hs : f s ≠ [])
    (above : ∀ r, s < r → f r = []) :
    ∀ n, s ≤ n → ((List.range (n + 1)).reverse.flatMap f).head? = (f s).head? := by
  intro n hn
  induction n with
  | zero =>
    have : s = 0 := by omega
    subst this
    simp
  | succ n ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.flatMap_cons]
    by_cases equal : s = n + 1
    · subst equal
      cases hf : f (n + 1) with
      | nil => exact absurd hf hs
      | cons head more => simp
    · rw [above (n + 1) (by omega), List.nil_append]
      exact ih (by omega)

/-- A feasible, maximal head plan heads the ranked stream when its own tier has no preference. -/
theorem rankedPreferred_head {domains : Domains} {plan : Plan}
    (preferred : Nat → Nat → Bool) (h : headPlan domains = some plan)
    (maximal : HeadsMaximal domains) (feasibleHead : feasible plan)
    (ordinary : ∀ index, preferred (score plan) index = false) :
    (rankedPreferred domains preferred).head? = some plan := by
  have allowedHead := headPlan_allowed h
  have top := headPlan_score h maximal
  let f := fun rank => (feasiblePlans (orderedDomains domains (preferred rank) 0)).filter
    fun candidate => decide (score candidate = rank)
  have own : (f (score plan)).head? = some plan := by
    have same : preferred (score plan) = fun _ => false := funext ordinary
    simp only [f, same, orderedDomains_none, feasiblePlans]
    rw [List.filter_filter]
    apply head_filter (headPlan_first h)
    simp [(check_iff_feasible plan).mpr feasibleHead]
  have nonempty : f (score plan) ≠ [] := by
    intro empty
    rw [empty] at own
    simp at own
  have above : ∀ r, score plan < r → f r = [] := by
    intro r hr
    rw [List.filter_eq_nil_iff]
    intro candidate member
    have exact := (feasiblePlans_exact _ candidate).mp member
    rw [orderedDomains_allowed] at exact
    have bound := (allowed_score_bounds exact.1).2
    simp only [decide_eq_true_eq]
    omega
  have length : score plan ≤ domains.length := by
    have := score_le_length plan
    have := allowed_length allowedHead
    omega
  unfold rankedPreferred
  rw [head_ranks nonempty above domains.length length, own]

-- Executable witness: a two-node head plan heads the stream; a later retained choice does not.
example :
    (rankedPreferred [[⟨10, 10, true, []⟩], [⟨20, 20, true, []⟩, ⟨1, 1, false, []⟩]]
      (fun _ _ => false)).head? = some [⟨10, 10, true, []⟩, ⟨20, 20, true, []⟩] := by decide
example :
    headPlan [[⟨1, 1, false, []⟩, ⟨20, 20, true, []⟩]] = some [⟨1, 1, false, []⟩] ∧
      (rankedPreferred [[⟨1, 1, false, []⟩, ⟨20, 20, true, []⟩]] (fun _ _ => false)).head? =
        some [⟨20, 20, true, []⟩] := by decide

end Reconcile.Policy
