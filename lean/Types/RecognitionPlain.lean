import Types.Recognition

/-!
# Plain-object recognition by one prototype read

`builtinFirstMatch` in `src/types/builtins.ts` reads an object's prototype once after the array
probe. When that prototype is `Object.prototype` or `null`, it selects the plain-object fallback
without running the remaining probes; any other object takes the ordered scan of
`Types.Recognition`, each `instanceof` probe deciding membership in the chain from the prototype
already read (`inChain` in `src/object-property.ts`). This module proves that the result is the
scan's: on such a chain every later probe fails, provided each `instanceof` probe uses the default
`Symbol.hasInstance`. A typed array is a value with the typed-array brand whose chain holds
`%TypedArray%.prototype`, so a view whose prototype was replaced, or a `DataView` that inherits a
typed array's prototype, is not one. A view counts only over a buffer the environment recognizes
(`recognizedBuffer`); reading a view's brands and own buffer observes nothing, so the model takes
the answers as given. The reads differ: the object itself is read once,
where the scan read it once per probe, and the walks over its prototypes are the scan's, except
that the typed-array probe does not walk again for `DataView`, which its own probe decided.

Ranks follow the declared order: 0 array, 1 `Date`, 2 `Map`, 3 `Set`, 4 `ArrayBuffer`,
5 `DataView`, 6 typed array, 7 Temporal, 8 `URL`, 9 `URLSearchParams` and 10 the plain-object
fallback. `.builtin 6` is `%TypedArray%.prototype`, the prototype every built-in typed array
class inherits.
-/

namespace Reconcile.Types.RecognitionPlain

open Reconcile.Types.Recognition

/-- A prototype in an object's chain: `Object.prototype`, the prototype of the constructor probed
at a rank from 1 to 5, `%TypedArray%.prototype` at rank 6, or any other object. -/
inductive Proto where
  | object
  | builtin (rank : Nat)
  | other (label : Nat)
  deriving DecidableEq, Repr

/-- The answers to an object's prototype reads, from its own prototype on. `raises` holds when the
read after the last listed prototype throws; otherwise that read returns `null`. -/
structure Chain where
  protos : List Proto
  raises : Bool
  deriving DecidableEq, Repr

/-- `instanceof` with the default `Symbol.hasInstance`: the walk finds the target, or a read
throws before it, or the chain ends. -/
def instanceOutcome (c : Chain) (target : Proto) : ProbeOutcome :=
  if target ∈ c.protos then .hit else if c.raises then .raised else .miss

/-- `value instanceof DataView`, unless `value` is a view over a `foreign` buffer, one the
environment does not recognize. -/
def dataViewOutcome (c : Chain) (brand foreign : Bool) : ProbeOutcome :=
  match instanceOutcome c (.builtin 5) with
  | .hit => if brand && foreign then .miss else .hit
  | o => o

/-- A value with the typed-array brand over a recognized buffer, `&& !(value instanceof DataView)
&& value instanceof %TypedArray%`; the brand check and the buffer's answer read nothing. -/
def typedOutcome (c : Chain) (typed foreign : Bool) : ProbeOutcome :=
  if typed && !foreign then
    match instanceOutcome c (.builtin 5) with
    | .hit => .miss
    | .raised => .raised
    | .miss => instanceOutcome c (.builtin 6)
  else .miss

/-- The prototypes the Temporal, `URL` and `URLSearchParams` probes look for: the live Temporal
constructors' prototypes, none when the namespace is absent, and the two URL prototypes. -/
structure Targets where
  temporal : List Proto
  url : Proto
  params : Proto

/-- No target is `Object.prototype`: the live constructors are the built-in ones. -/
def Targets.Unknown (ts : Targets) : Prop :=
  (∀ p ∈ ts.temporal, p ≠ .object) ∧ ts.url ≠ .object ∧ ts.params ≠ .object

/-- The Temporal probe holds when any constructor's prototype is in the chain. -/
def anyOutcome (c : Chain) (targets : List Proto) : ProbeOutcome :=
  if targets.any (· ∈ c.protos) then .hit else if c.raises then .raised else .miss

/-- The ordered scan's ten probe outcomes for one object: `brand` is the view brand, which a
`DataView` and a typed array hold, and `typed` the typed-array brand. -/
def probes (isArray : ProbeOutcome) (c : Chain) (brand typed foreign : Bool) (ts : Targets) :
    List ProbeOutcome :=
  [isArray, instanceOutcome c (.builtin 1), instanceOutcome c (.builtin 2),
    instanceOutcome c (.builtin 3), instanceOutcome c (.builtin 4),
    dataViewOutcome c brand foreign, typedOutcome c typed foreign, anyOutcome c ts.temporal,
    instanceOutcome c ts.url, instanceOutcome c ts.params]

/-- One read decides: the prototype is `Object.prototype` or `null` and the read did not throw. -/
def plain (c : Chain) : Bool :=
  (c.protos == [] || c.protos == [.object]) && !c.raises

/-- A rank the runtime selects, or nothing when the probe bound `last` stops before it. -/
def selectAt (last r : Nat) : ProbeTrace := if r ≤ last then { selected := some r } else {}

/-- The runtime: the array probe, then one prototype read, which decides a plain object; any other
object takes the ordered scan from rank 1, whose probes are membership in the chain. -/
def recognize (last : Nat) (isArray : ProbeOutcome) (c : Chain) (brand typed foreign : Bool)
    (ts : Targets) : ProbeTrace :=
  match isArray with
  | .miss =>
    if last < 1 then {} else
    if plain c then selectAt last 10 else scanTrace last 0 (probes .miss c brand typed foreign ts)
  | _ => scanTrace last 0 (probes isArray c brand typed foreign ts)

/-- Selection and the raised rank, which the runtime must preserve; `visited` is the trace it
changes. -/
def outcome (trace : ProbeTrace) : Option Nat × Option Nat := (trace.selected, trace.raised)

@[simp] theorem outcome_empty : outcome ({} : ProbeTrace) = (none, none) := rfl

theorem outcome_selectAt (last r : Nat) :
    outcome (selectAt last r) = if r ≤ last then (some r, none) else (none, none) := by
  unfold selectAt
  split <;> rfl

/-- One probe of the scan: a bound stop, a hit, a throw, or the tail after a miss. -/
theorem outcome_scan_cons (last r : Nat) (o : ProbeOutcome) (rest : List ProbeOutcome) :
    outcome (scanTrace last r (o :: rest)) =
      if last < r then (none, none) else
        match o with
        | .hit => (some r, none)
        | .raised => (none, some r)
        | .miss => outcome (scanTrace last (r + 1) rest) := by
  simp only [scanTrace, probe]
  by_cases h : r > last
  · simp [h]
  · simp only [h, if_false]
    cases o <;> rfl

theorem outcome_scan_nil (last r : Nat) :
    outcome (scanTrace last r []) = if r ≤ last then (some r, none) else (none, none) := by
  simp only [scanTrace]
  split <;> rfl

/-- On a plain chain every probe after the array probe fails, whatever brands the object holds. -/
theorem plain_probes (c : Chain) (brand typed foreign : Bool) (ts : Targets) (hts : ts.Unknown)
    (h : plain c = true) :
    probes .miss c brand typed foreign ts = .miss :: List.replicate 9 .miss := by
  obtain ⟨htem, hurl, hpar⟩ := hts
  simp only [plain, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨hp | hp, hr⟩ := h <;>
    simp [probes, instanceOutcome, dataViewOutcome, typedOutcome, anyOutcome, hp, hr, hurl,
      hpar, List.replicate]
  · exact fun hmem => htem _ hmem rfl

/-- The runtime selects the rank the ordered scan selects and raises where it raises. -/
theorem recognize_eq_scan (last : Nat) (isArray : ProbeOutcome) (c : Chain)
    (brand typed foreign : Bool) (ts : Targets) (hts : ts.Unknown) :
    outcome (recognize last isArray c brand typed foreign ts) =
      outcome (scanTrace last 0 (probes isArray c brand typed foreign ts)) := by
  cases isArray with
  | hit => rfl
  | raised => rfl
  | miss =>
    simp only [recognize]
    by_cases hlast : last < 1
    · have : last = 0 := by omega
      subst this
      simp [probes, outcome_scan_cons]
    · simp only [hlast, if_false]
      by_cases hplain : plain c = true
      · simp only [hplain, if_true, plain_probes c brand typed foreign ts hts hplain, List.replicate,
          outcome_scan_cons, outcome_scan_nil, outcome_selectAt]
        (repeat' split) <;> first | rfl | omega
      · simp only [hplain, Bool.false_eq_true, if_false]

/-- Targets that occur in none of the examples' chains. -/
def absent : Targets := { temporal := [], url := .other 1000, params := .other 1001 }

-- A plain object and a `null`-prototype object take the fallback.
example : outcome (recognize 10 .miss { protos := [.object], raises := false } false false false
      absent) = (some 10, none) := rfl
example : outcome (recognize 10 .miss { protos := [], raises := false } false false false absent) =
    (some 10, none) := rfl
-- A typed array is recognized through `%TypedArray%.prototype`.
example : outcome (recognize 10 .miss { protos := [.other 7, .builtin 6, .object], raises := false }
      true true false absent) = (some 6, none) := rfl
-- A typed array or a `DataView` whose prototype is `Object.prototype` or `null` takes the
-- fallback.
example : outcome (recognize 10 .miss { protos := [.object], raises := false } true true false
      absent) = (some 10, none) := rfl
example : outcome (recognize 10 .miss { protos := [], raises := false } true false false absent) =
    (some 10, none) := rfl
-- The typed-array brand decides: a `DataView` that inherits a typed array's prototype takes the
-- fallback, where the view brand alone would select a typed array it cannot copy.
example : outcome (recognize 10 .miss { protos := [.other 7, .builtin 6, .object], raises := false }
      true false false absent) = (some 10, none) := rfl
-- A typed array whose prototype was set to `DataView.prototype` is a `DataView` by its chain and
-- still holds the typed-array brand, so a `DataView`-kind copy reads it through the getters its
-- element type selects.
example : outcome (recognize 10 .miss { protos := [.builtin 5, .object], raises := false } true true
      false absent) = (some 5, none) := rfl
-- A typed array or a `DataView` over a buffer the environment does not recognize, such as one from
-- another environment, takes the fallback.
example : outcome (recognize 10 .miss { protos := [.other 7, .builtin 6, .object], raises := false }
      true true true absent) = (some 10, none) := rfl
example : outcome (recognize 10 .miss { protos := [.builtin 5, .object], raises := false } true false
      true absent) = (some 10, none) := rfl
-- A known-kind check bounded before the fallback rejects a plain object.
example : outcome (recognize 2 .miss { protos := [.object], raises := false } false false false
      absent) = (none, none) := rfl
-- A throwing first read is not plain; it raises as the scan does.
example : outcome (recognize 10 .miss { protos := [], raises := true } false false false absent) =
    (none, some 1) := rfl

/-- Counterexample for `Targets.Unknown`: were `URL` replaced by `Object`, `instanceof URL` would
hold for a plain object, which the runtime no longer asks. -/
example : outcome (recognize 10 .miss { protos := [.object], raises := false } false false false
      { absent with url := .object }) ≠
    outcome (scanTrace 10 0 (probes .miss { protos := [.object], raises := false } false false
      false { absent with url := .object })) := by
  decide

end Reconcile.Types.RecognitionPlain
