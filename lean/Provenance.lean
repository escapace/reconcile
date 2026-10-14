import Lean
import Mathlib.Data.Bool.Basic

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

def choose (facts : Facts) : Decision :=
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
      (facts.origin ≠ .copy ∧ facts.currentBacked = true ∧ facts.forced = false ∧
        facts.dependenciesStable = true ∧ facts.equivalent = true) := by
  cases facts with
  | mk dependencies current equal forced origin =>
    cases origin <;> cases dependencies <;> cases current <;> cases equal <;> cases forced <;> decide

theorem untracked_fresh (facts : Facts) (ho : facts.origin = .untracked)
    (hc : facts.currentBacked = false) : choose facts = .fresh := by
  simp [choose, ho, hc]

theorem forced_base_copy (facts : Facts) (ho : facts.origin = .base)
    (hf : facts.forced = true) : choose facts = .copy := by
  simp [choose, ho, hf]

end Reconcile.Provenance
