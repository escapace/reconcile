import Mathlib.Data.List.Basic

/-! Closed, finite selection constraints and the reference model of the ranked selection stream,
to which `CompactImmutable` relates the masks of `src/graph/immutable-selection.ts`. Native capture
supplies the identity and storage labels. -/

namespace Reconcile.Policy

structure Requirement where
  node : Nat
  identity : Nat
  deriving DecidableEq, Repr

structure Choice where
  identity : Nat
  storage : Nat
  retained : Bool
  required : List Requirement
  deriving DecidableEq, Repr

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

-- The head of a ranked stream is the head of its top nonempty score tier
-- (`CompactImmutable.ranked_head`).
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

end Reconcile.Policy
