import Lean

/-! The provenance rule of `produce` finalization (`src/graph/provenance.ts` `chooseSpecial`):
from supplied native facts, `choose` decides whether a value becomes the base, a copy, a fresh
value or stays its source. `chooseOld` is an alternative rule kept for comparison. -/

namespace Reconcile.Provenance

inductive Origin where
  | untracked | base | copy
  deriving DecidableEq, Repr, Lean.FromJson

inductive Decision where
  | base | copy | fresh | source
  deriving DecidableEq, Repr, Lean.ToJson

-- These are supplied native facts, not an interpreter for getters, equality,
-- writable copies, or dependency memory. Storage selection supplies no input here.
structure Facts where
  dependenciesStable : Bool
  currentBacked : Bool
  equivalent : Bool
  forced : Bool
  origin : Origin
  deriving Lean.FromJson

/-- An unchanged value stays itself whether it came from `current` or from outside it; a forced
clone of a linked owner, unstable dependencies or a changed copy make it new. -/
def choose (facts : Facts) : Decision :=
  if facts.origin = .copy then
    if facts.equivalent then .base else .source
  else if !facts.forced && facts.dependenciesStable && facts.equivalent then
    .source
  else if facts.origin = .base then .copy else .fresh

/-- An alternative rule, kept for comparison: only a value backed by `current` stays itself, so an
outside value is always copied. -/
def chooseOld (facts : Facts) : Decision :=
  if facts.origin = .copy then
    if facts.equivalent then .base else .source
  else if facts.currentBacked && !facts.forced && facts.dependenciesStable && facts.equivalent then
    .source
  else if facts.origin = .base then .copy else .fresh

-- Only a registered, equivalent copy can restore an explicit base.
theorem base_iff (facts : Facts) :
    choose facts = .base ↔ facts.origin = .copy ∧ facts.equivalent = true := by
  cases facts with
  | mk dependencies current equal forced origin =>
    cases origin <;> cases dependencies <;> cases current <;> cases equal <;> cases forced <;> decide

-- Keeping an unregistered/base-backed source requires the full conjunction.
-- A changed registered copy is already isolated and follows its separate rule.
theorem source_iff (facts : Facts) :
    choose facts = .source ↔
      (facts.origin = .copy ∧ facts.equivalent = false) ∨
      (facts.origin ≠ .copy ∧ facts.forced = false ∧
        facts.dependenciesStable = true ∧ facts.equivalent = true) := by
  cases facts with
  | mk dependencies current equal forced origin =>
    cases origin <;> cases dependencies <;> cases current <;> cases equal <;> cases forced <;> decide

/-- Where a value came from does not decide whether it stays itself. -/
theorem choose_currentBacked (facts : Facts) (backed : Bool) :
    choose { facts with currentBacked := backed } = choose facts := by
  cases facts with
  | mk dependencies current equal forced origin =>
    cases origin <;> cases dependencies <;> cases current <;> cases equal <;> cases forced <;>
      cases backed <;> decide

/-- For a value backed by `current`, `choose` and the alternative rule agree. -/
theorem choose_eq_old (facts : Facts) (hc : facts.currentBacked = true) :
    choose facts = chooseOld facts := by
  cases facts with
  | mk dependencies current equal forced origin =>
    simp only at hc
    subst hc
    cases origin <;> cases dependencies <;> cases equal <;> cases forced <;> decide

/-- An outside value the recipe never read stays itself unless a linked owner forces a clone or a
dependency changed; then it is new. -/
theorem untracked_source_iff (facts : Facts) (ho : facts.origin = .untracked) :
    choose facts = .source ↔ facts.forced = false ∧ facts.dependenciesStable = true ∧
      facts.equivalent = true := by
  cases facts with
  | mk dependencies current equal forced origin =>
    simp only at ho
    subst ho
    cases dependencies <;> cases current <;> cases equal <;> cases forced <;> decide

theorem untracked_fresh_iff (facts : Facts) (ho : facts.origin = .untracked) :
    choose facts = .fresh ↔ ¬ (facts.forced = false ∧ facts.dependenciesStable = true ∧
      facts.equivalent = true) := by
  cases facts with
  | mk dependencies current equal forced origin =>
    simp only at ho
    subst ho
    cases dependencies <;> cases current <;> cases equal <;> cases forced <;> decide

/-- The alternative rule copies every outside value the recipe never read. -/
theorem chooseOld_untracked_fresh (facts : Facts) (ho : facts.origin = .untracked)
    (hc : facts.currentBacked = false) : chooseOld facts = .fresh := by
  simp [chooseOld, ho, hc]

-- Where the alternative rule fails: it clones an unchanged URL assigned from outside, whose
-- `searchParams` stay the originals, although its params cannot follow the clone.
private def outsideURL : Facts :=
  ⟨true, false, true, false, .untracked⟩

example : chooseOld outsideURL = .fresh := by decide
example : choose outsideURL = .source := by decide

theorem forced_base_copy (facts : Facts) (ho : facts.origin = .base)
    (hf : facts.forced = true) : choose facts = .copy := by
  simp [choose, ho, hf]

end Reconcile.Provenance
