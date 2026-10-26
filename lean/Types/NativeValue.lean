/-! Finite native-value facet model. Native parsing, canonicalization, brand checks,
    allocation, and observation traces remain correspondence obligations. Payloads
    are observations, not JS strings interpreted by Lean. -/
namespace Reconcile.Types.NativeValue

inductive TemporalKind where
  | instant | duration | plainDate | plainTime | plainDateTime
  | plainYearMonth | plainMonthDay | zonedDateTime
  deriving DecidableEq, Repr

inductive Payload where
  | url (href : String)
  | parameters (entries : List (String × String))
  | temporal (kind : TemporalKind) (constructor : Nat) (observation : List String)
  deriving DecidableEq, Repr

/-- Compatibility is kind-only for writable native payloads. An immutable Temporal
    target is compatible only when the captured payload itself is equal. -/
def compatible : Payload → Payload → Bool
  | .url _, .url _ => true
  | .parameters _, .parameters _ => true
  | .temporal k c a, .temporal l d b => decide (k = l ∧ c = d ∧ a = b)
  | _, _ => false

def publish (current desired : Payload) : Option Payload :=
  if compatible current desired then some desired else none

theorem published_payload (current desired result : Payload)
    (h : publish current desired = some result) : result = desired := by
  unfold publish at h
  split at h
  · exact (Option.some.inj h).symm
  · contradiction

theorem temporal_compatible_iff (k l : TemporalKind) (c d : Nat) (a b : List String) :
    compatible (.temporal k c a) (.temporal l d b) = true ↔ k = l ∧ c = d ∧ a = b := by
  simp [compatible]

/-- Equality supports immutable reuse; it never identifies two visible objects. -/
def reusable (current desired : Payload) : Bool := decide (current = desired)

/-- Clear, then append every desired pair in capture order. Duplicates survive. -/
def appendEntries (target desired : List (String × String)) : List (String × String) :=
  desired.foldl (fun entries entry => entries ++ [entry]) target

theorem append_entries_eq (target desired : List (String × String)) :
    appendEntries target desired = target ++ desired := by
  induction desired generalizing target with
  | nil => simp [appendEntries]
  | cons entry rest ih =>
    change appendEntries (target ++ [entry]) rest = target ++ (entry :: rest)
    rw [ih]
    simp

theorem clear_append_exact (desired : List (String × String)) :
    appendEntries [] desired = desired := by simp [append_entries_eq]


end Reconcile.Types.NativeValue

namespace Reconcile.Types.NativeValue.ContractTest
-- Executable inhabitants and necessity examples for the finite facet policy.
example : publish (.url "https://a.test/") (.url "https://b.test/") =
    some (.url "https://b.test/") := rfl
example : publish (.parameters [("a", "1")]) (.parameters [("a", "2"), ("a", "3")]) =
    some (.parameters [("a", "2"), ("a", "3")]) := rfl
example : compatible (.temporal .instant 0 ["0"]) (.temporal .instant 0 ["0"]) = true := rfl
example : publish (.temporal .instant 0 ["0"]) (.temporal .instant 0 ["1"]) = none := rfl
example : compatible (.temporal .instant 0 ["0"]) (.temporal .instant 1 ["0"]) = false := rfl
example : Payload.parameters [("a", "1"), ("a", "2")] ≠
    Payload.parameters [("a", "2")] := by decide
example : Payload.parameters [("b", "1"), ("a", "2")] ≠
    Payload.parameters [("a", "2"), ("b", "1")] := by decide
-- Duration components cannot be replaced by normalized elapsed seconds.
example : Payload.temporal .duration 0 ["seconds", "1", "milliseconds", "0"] ≠
    Payload.temporal .duration 0 ["seconds", "0", "milliseconds", "1000"] := by decide
end Reconcile.Types.NativeValue.ContractTest
