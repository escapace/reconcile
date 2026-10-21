/-!
# Draft reads

A draft reads an own property of its object, before its first write, through the object, and from
its working copy afterwards. Every other property comes from the prototype, before and after the
first write. A wrapper such as a Vue reactive proxy can answer reads for keys its object does not
own, such as its internal markers and its own versions of array methods; reading those through
the wrapper would hand the recipe the wrapper's view of `current`, so a draft never does.

`owned` says whether the object, or after the first write the working copy, owns the key.
-/

namespace Reconcile.DraftRead

/-- Where a read takes its value from. -/
inductive Source where
  /-- The object's own property, or its working copy's after the first write. -/
  | own
  /-- The prototype the draft reports. -/
  | prototype
  /-- Whatever the object's wrapper answers for a key the object does not own. -/
  | wrapper
  deriving DecidableEq, Repr

/-- An alternative read, kept for comparison: before the first write every key goes through the
object, so a wrapper answers the keys its object does not own. -/
def readOld (copied owned : Bool) : Source :=
  if owned then .own else if copied then .prototype else .wrapper

/-- The draft read: own properties from the object or its copy, everything else from the
prototype. -/
def read (_copied : Bool) (owned : Bool) : Source :=
  if owned then .own else .prototype

/-- A read does not depend on whether the draft was written: the first write changes no read
source. -/
theorem read_copied (owned : Bool) : read false owned = read true owned := rfl

/-- A draft never reads a wrapper's answer, so no wrapper marker or wrapper method reaches the
recipe. -/
theorem read_not_wrapper (copied owned : Bool) : read copied owned ≠ .wrapper := by
  cases owned <;> simp [read]

/-- After the first write `read` and the alternative read agree; they differ only before it. -/
theorem read_eq_old (owned : Bool) : read true owned = readOld true owned := by
  cases owned <;> rfl

/-- The alternative read hands the recipe the wrapper's answer before the first write. -/
example : readOld false false = .wrapper := rfl

end Reconcile.DraftRead
