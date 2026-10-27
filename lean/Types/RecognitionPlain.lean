/-!
# Plain-object recognition by one prototype read

Recognition runs ordered native predicate probes, the plain-object fallback last. The reference
is the ordered scan `scanTrace`, which `scripts/recognition-scan.ts` runs as the tests'
reference: probes in rank order up to a bound `last`, stopping at the first that holds or throws.

`builtinFirstMatch` in `src/types/builtins.ts` reads an object's prototype once after the array
probe. When that prototype is `Object.prototype` or `null`, it selects the plain-object fallback
without running the remaining probes; any other object takes the ordered scan, each `instanceof`
probe deciding membership in the chain from the prototype already read (`inChain` in
`src/object-property.ts`). This module proves that the result, and the probe that raises an
error, are the scan's: on such a chain every later probe fails, a view's included, provided each
`instanceof` probe uses the default `Symbol.hasInstance` and no live Temporal, `URL` or
`URLSearchParams` constructor's prototype is `Object.prototype` (`Targets.Unknown`). A typed array
is a value with the typed-array brand whose chain holds `%TypedArray%.prototype`, so a view whose
prototype was replaced, or a `DataView` that inherits a typed array's prototype, is not one.

A view counts only over a buffer the environment recognizes: one whose chain holds
`ArrayBuffer.prototype` or `SharedArrayBuffer.prototype` (`recognizedBuffer` in the runtime).
Reading a view's brands and its own buffer observes nothing, but deciding the buffer walks the
buffer's prototype chain, which can raise (`bufferOutcome`). Built-in recognition walks it in the
`DataView` probe (`viewAnswer` in `builtinRemainingMatch`), after the walk for `DataView` and
before the bound at that rank, for every view it does not decide from a plain prototype, and the
typed-array probe reuses the answer; the reference's view probes read it at the same point
(`viewOutcome`). So a known-kind check bounded at the `DataView` rank raises when a typed array's
buffer chain raises. That a repeated walk answers as the first is the stability obligation.

The reads differ: the object itself is read once, where the scan reads it once per probe, and the
walks over its prototypes are the scan's, except that the typed-array probe does not walk again
for `DataView` or the buffer, which the `DataView` probe decided.

Ranks follow the declared order: 0 array, 1 `Date`, 2 `Map`, 3 `Set`, 4 `ArrayBuffer`,
5 `DataView`, 6 typed array, 7 Temporal, 8 `URL`, 9 `URLSearchParams` and 10 the plain-object
fallback. `.builtin 6` is `%TypedArray%.prototype`, the prototype every built-in typed array
class inherits.
-/

namespace Reconcile.Types.RecognitionPlain

/-! ## The ordered scan -/

/-- Supplied native outcomes; a throw terminates the observed predicate prefix. -/
inductive ProbeOutcome where
  | miss
  | hit
  | raised
  deriving DecidableEq, Repr

/-- Both the selected result and the exact predicate-call prefix are observable. -/
structure ProbeTrace where
  selected : Option Nat := none
  raised : Option Nat := none
  visited : List Nat := []
  deriving DecidableEq, Repr

/-- One bounded native call, followed by its continuation only after a miss. -/
def probe (rank last : Nat) (outcome : ProbeOutcome) (rest : Unit → ProbeTrace) : ProbeTrace :=
  if rank > last then {} else
  match outcome with
  | .hit => { selected := some rank, visited := [rank] }
  | .raised => { raised := some rank, visited := [rank] }
  | .miss => let tail := rest (); { tail with visited := rank :: tail.visited }

/-- The ordered scan from `rank`, bounded by `last`; its final fallback makes no predicate call. -/
def scanTrace (last : Nat) (rank : Nat) : List ProbeOutcome → ProbeTrace
  | [] => if rank ≤ last then { selected := some rank } else {}
  | outcome :: rest => probe rank last outcome (fun _ => scanTrace last (rank + 1) rest)

example : scanTrace 1 0 [.miss, .raised, .hit] =
    { raised := some 1, visited := [0, 1] } := by decide

example : scanTrace 0 0 [.miss, .raised] = { visited := [0] } := by decide

example : scanTrace 2 0 [.hit, .raised] =
    { selected := some 0, visited := [0] } := by decide

/-! ## One prototype read -/

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

/-- The prototypes the Temporal, `URL`, `URLSearchParams` and `SharedArrayBuffer` probes look
for: the live Temporal constructors' prototypes, none when the namespace is absent, the two URL
prototypes, and `SharedArrayBuffer.prototype`, none when it is absent. -/
structure Targets where
  temporal : List Proto
  url : Proto
  params : Proto
  shared : List Proto

/-- No target the object's chain is probed for is `Object.prototype`: the live constructors are
the built-in ones. -/
def Targets.Unknown (ts : Targets) : Prop :=
  (∀ p ∈ ts.temporal, p ≠ .object) ∧ ts.url ≠ .object ∧ ts.params ≠ .object

/-- The Temporal probe holds when any constructor's prototype is in the chain. -/
def anyOutcome (c : Chain) (targets : List Proto) : ProbeOutcome :=
  if targets.any (· ∈ c.protos) then .hit else if c.raises then .raised else .miss

/-- Whether the environment recognizes a buffer, from the buffer's chain, as `recognizedBuffer`
decides it: the walk for `ArrayBuffer.prototype`, then, when it ends without it, the walk for
`SharedArrayBuffer.prototype`. -/
def bufferOutcome (b : Chain) (ts : Targets) : ProbeOutcome :=
  match instanceOutcome b (.builtin 4) with
  | .miss => anyOutcome b ts.shared
  | o => o

/-- One read decides: the prototype is `Object.prototype` or `null` and the read did not throw. -/
def plain (c : Chain) : Bool :=
  (c.protos == [] || c.protos == [.object]) && !c.raises

/-- A view's buffer answer, where the view probes read it: a value without the view brand, or
whose prototype decides it plain, needs none (`.hit`); any other view walks its buffer `b`. -/
def viewOutcome (c : Chain) (brand : Bool) (b : Chain) (ts : Targets) : ProbeOutcome :=
  if brand && !plain c then bufferOutcome b ts else .hit

/-- `value instanceof DataView`, then the view's buffer answer: a `DataView` over a buffer the
environment does not recognize is not one. -/
def dataViewOutcome (c : Chain) (brand : Bool) (b : Chain) (ts : Targets) : ProbeOutcome :=
  match instanceOutcome c (.builtin 5) with
  | .raised => .raised
  | dv =>
    match viewOutcome c brand b ts with
    | .hit => dv
    | o => o

/-- A value with the view brand over a recognized buffer, `&& viewElement(value) !== undefined
&& !(value instanceof DataView) && value instanceof %TypedArray%`. -/
def typedOutcome (c : Chain) (brand typed : Bool) (b : Chain) (ts : Targets) : ProbeOutcome :=
  if brand then
    match viewOutcome c brand b ts with
    | .hit =>
      if typed then
        match instanceOutcome c (.builtin 5) with
        | .hit => .miss
        | .raised => .raised
        | .miss => instanceOutcome c (.builtin 6)
      else .miss
    | o => o
  else .miss

/-- The ordered scan's ten probe outcomes for one object: `brand` is the view brand, which a
`DataView` and a typed array hold, `typed` the typed-array brand, and `b` the view's buffer's
chain. -/
def probes (isArray : ProbeOutcome) (c : Chain) (brand typed : Bool) (b : Chain) (ts : Targets) :
    List ProbeOutcome :=
  [isArray, instanceOutcome c (.builtin 1), instanceOutcome c (.builtin 2),
    instanceOutcome c (.builtin 3), instanceOutcome c (.builtin 4),
    dataViewOutcome c brand b ts, typedOutcome c brand typed b ts, anyOutcome c ts.temporal,
    instanceOutcome c ts.url, instanceOutcome c ts.params]

/-- A rank the runtime selects, or nothing when the probe bound `last` stops before it. -/
def selectAt (last r : Nat) : ProbeTrace := if r ≤ last then { selected := some r } else {}

/-- The runtime: the array probe, then one prototype read, which decides a plain object; any other
object takes the ordered scan from rank 1, whose probes are membership in the chain and, for a
view, its buffer's answer. -/
def recognize (last : Nat) (isArray : ProbeOutcome) (c : Chain) (brand typed : Bool) (b : Chain)
    (ts : Targets) : ProbeTrace :=
  match isArray with
  | .miss =>
    if last < 1 then {} else
    if plain c then selectAt last 10 else scanTrace last 0 (probes .miss c brand typed b ts)
  | _ => scanTrace last 0 (probes isArray c brand typed b ts)

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

/-- On a plain chain every probe after the array probe fails, whatever brands the object holds
and whatever its buffer's chain: no view probe reads the buffer. -/
theorem plain_probes (c : Chain) (brand typed : Bool) (b : Chain) (ts : Targets)
    (hts : ts.Unknown) (h : plain c = true) :
    probes .miss c brand typed b ts = .miss :: List.replicate 9 .miss := by
  obtain ⟨htem, hurl, hpar⟩ := hts
  have hview : viewOutcome c brand b ts = .hit := by simp [viewOutcome, h]
  simp only [plain, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨hp | hp, hr⟩ := h <;>
    simp [probes, instanceOutcome, dataViewOutcome, typedOutcome, anyOutcome, hview, hp, hr,
      hurl, hpar, List.replicate]
  · exact fun hmem => htem _ hmem rfl

/-- The runtime selects the rank the ordered scan selects and raises where it raises. -/
theorem recognize_eq_scan (last : Nat) (isArray : ProbeOutcome) (c : Chain)
    (brand typed : Bool) (b : Chain) (ts : Targets) (hts : ts.Unknown) :
    outcome (recognize last isArray c brand typed b ts) =
      outcome (scanTrace last 0 (probes isArray c brand typed b ts)) := by
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
      · simp only [hplain, if_true, plain_probes c brand typed b ts hts hplain, List.replicate,
          outcome_scan_cons, outcome_scan_nil, outcome_selectAt]
        (repeat' split) <;> first | rfl | omega
      · simp only [hplain, Bool.false_eq_true, if_false]

/-- Targets that occur in none of the examples' chains. -/
def absent : Targets :=
  { temporal := [], url := .other 1000, params := .other 1001, shared := [.other 1002] }

/-- A buffer of this environment: its chain holds `ArrayBuffer.prototype`. -/
def localBuffer : Chain := { protos := [.builtin 4, .object], raises := false }

/-- A buffer whose prototype is `null`, as from another environment's view the chain says. -/
def foreignBuffer : Chain := { protos := [], raises := false }

/-- A buffer whose prototype's prototype read throws. -/
def raisingBuffer : Chain := { protos := [.other 1003], raises := true }

-- A plain object and a `null`-prototype object take the fallback.
example : outcome (recognize 10 .miss { protos := [.object], raises := false } false false
      localBuffer absent) = (some 10, none) := rfl
example : outcome (recognize 10 .miss { protos := [], raises := false } false false
      localBuffer absent) = (some 10, none) := rfl
-- A typed array is recognized through `%TypedArray%.prototype`.
example : outcome (recognize 10 .miss { protos := [.other 7, .builtin 6, .object], raises := false }
      true true localBuffer absent) = (some 6, none) := rfl
-- So is a view over a `SharedArrayBuffer`.
example : outcome (recognize 10 .miss { protos := [.other 7, .builtin 6, .object], raises := false }
      true true { protos := [.other 1002, .object], raises := false } absent) = (some 6, none) := rfl
-- A typed array or a `DataView` whose prototype is `Object.prototype` or `null` takes the
-- fallback, without reading its buffer.
example : outcome (recognize 10 .miss { protos := [.object], raises := false } true true
      raisingBuffer absent) = (some 10, none) := rfl
example : outcome (recognize 10 .miss { protos := [], raises := false } true false raisingBuffer
      absent) = (some 10, none) := rfl
-- The typed-array brand decides: a `DataView` that inherits a typed array's prototype takes the
-- fallback, where the view brand alone would select a typed array it cannot copy.
example : outcome (recognize 10 .miss { protos := [.other 7, .builtin 6, .object], raises := false }
      true false localBuffer absent) = (some 10, none) := rfl
-- A typed array whose prototype was set to `DataView.prototype` is a `DataView` by its chain and
-- still holds the typed-array brand, so a `DataView`-kind copy reads it through the getters its
-- element type selects.
example : outcome (recognize 10 .miss { protos := [.builtin 5, .object], raises := false } true true
      localBuffer absent) = (some 5, none) := rfl
-- A typed array or a `DataView` over a buffer the environment does not recognize, such as one from
-- another environment, takes the fallback.
example : outcome (recognize 10 .miss { protos := [.other 7, .builtin 6, .object], raises := false }
      true true foreignBuffer absent) = (some 10, none) := rfl
example : outcome (recognize 10 .miss { protos := [.builtin 5, .object], raises := false } true false
      foreignBuffer absent) = (some 10, none) := rfl
-- A typed array over a buffer whose chain raises raises in the `DataView` probe, so a known-kind
-- check bounded there raises too, while one bounded before it does not read the buffer.
example : outcome (recognize 10 .miss { protos := [.other 7, .builtin 6, .object], raises := false }
      true true raisingBuffer absent) = (none, some 5) := rfl
example : outcome (recognize 5 .miss { protos := [.other 7, .builtin 6, .object], raises := false }
      true true raisingBuffer absent) = (none, some 5) := rfl
example : outcome (recognize 4 .miss { protos := [.other 7, .builtin 6, .object], raises := false }
      true true raisingBuffer absent) = (none, none) := rfl
-- A known-kind check bounded before the fallback rejects a plain object.
example : outcome (recognize 2 .miss { protos := [.object], raises := false } false false
      localBuffer absent) = (none, none) := rfl
-- A throwing first read is not plain; it raises as the scan does.
example : outcome (recognize 10 .miss { protos := [], raises := true } false false
      localBuffer absent) = (none, some 1) := rfl

/-- Counterexample for `Targets.Unknown`: were `URL` replaced by `Object`, `instanceof URL` would
hold for a plain object, which the runtime decides without asking. -/
example : outcome (recognize 10 .miss { protos := [.object], raises := false } false false
      localBuffer { absent with url := .object }) ≠
    outcome (scanTrace 10 0 (probes .miss { protos := [.object], raises := false } false false
      localBuffer { absent with url := .object })) := by
  decide

/-- Counterexample for reading the buffer of a plain view: were the `DataView` probe to walk the
buffer of every view, its walk for `DataView` missing, it would raise for a typed array whose
prototype is `Object.prototype` over a buffer whose chain raises, which the runtime decides plain
without reading the buffer. -/
example : outcome (recognize 10 .miss { protos := [.object], raises := false } true true
      raisingBuffer absent) ≠
    outcome (scanTrace 10 0 [.miss, .miss, .miss, .miss, .miss, bufferOutcome raisingBuffer absent,
      .miss, .miss, .miss, .miss]) := by
  decide

end Reconcile.Types.RecognitionPlain
