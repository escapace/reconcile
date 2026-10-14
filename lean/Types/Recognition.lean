import Mathlib.Data.List.Basic

namespace Reconcile.Types.Recognition

-- Flags encode stable native predicate results in declared precedence order.
-- A final fallback has flag true. This does not model predicate side effects;
-- expected validation observes only the prefix through its requested rank.
def first : List Bool → Option Nat
  | [] => none
  | true :: _ => some 0
  | false :: rest => (first rest).map Nat.succ

def accepts : List Bool → Nat → Bool
  | [], _ => false
  | flag :: _, 0 => flag
  | true :: _, _ + 1 => false
  | false :: rest, rank + 1 => accepts rest rank

theorem accepts_iff (flags : List Bool) (rank : Nat) :
    accepts flags rank = true ↔ first flags = some rank := by
  induction flags generalizing rank with
  | nil => simp [accepts, first]
  | cons flag rest ih =>
    cases flag <;> cases rank <;> simp [accepts, first, ih]

end Reconcile.Types.Recognition
