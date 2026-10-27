import Property.PropertyWrite
import Oracle.Protocol

/-! Oracles for the `PropertyWrite`, `PropertyConstructOn` and `PropertyThroughSetter` families:
single-key outcomes of `reconcileKey` over every descriptor case,
new-object writes by `constructFromOn`, and a recipe's assignment through an inherited setter
(`draftThroughSetter`). -/

namespace Reconcile.PropertyWriteOracle

open Reconcile.PropertyWrite Reconcile.Protocol Lean

private def bools : List Bool := [false, true]

private def attrs : List Attrs :=
  bools.flatMap fun w => bools.flatMap fun e => bools.map fun c => ⟨w, e, c⟩

private def owns : List (Option (Own Nat)) :=
  none :: ([0, 1].flatMap fun x => attrs.map fun a => some (.data x a)) ++
    ([0, 1].flatMap fun x => bools.flatMap fun st => bools.flatMap fun e =>
      bools.map fun c => some (.accessor x st e c))

private def inheriteds : List Inherited :=
  [.none, .data false, .data true, .accessor false, .accessor true]

/-- One own descriptor: `kind` is `none`, `data` or `accessor`; `value` is the data value or the
value an accessor's getter returns. -/
private structure Descriptor where
  kind : String
  value : Nat := 0
  writable : Bool := false
  enumerable : Bool := false
  configurable : Bool := false
  setter : Bool := false
  deriving ToJson

private def describe : Option (Own Nat) → Descriptor
  | none => { kind := "none" }
  | some (.data value a) =>
    { kind := "data", value, writable := a.writable, enumerable := a.enumerable,
      configurable := a.configurable }
  | some (.accessor value setter enumerable configurable) =>
    { kind := "accessor", value, setter, enumerable, configurable }

private def inheritedName : Inherited → String
  | .none => "none"
  | .data false => "readonly"
  | .data true => "data"
  | .accessor false => "getter"
  | .accessor true => "accessor"

private def statusName : Status → String
  | .done => "done"
  | .rejectedBeforeWriting => "rejectedBeforeWriting"
  | .rejectedAfterWriting => "rejectedAfterWriting"

private structure Observation where
  own : Descriptor
  inherited : String
  extensible : Bool
  proto : Bool
  value : Nat
  status : String
  after : Descriptor
  ownSetterCalls : Nat
  deriving ToJson

/-- The rows' own setters store the value they receive. -/
theorem storing_stores : Storing storing := by
  intro s v stored setter e c h
  simp [storing, h]

private def observe : Slot Nat × Nat × Bool → Observation
  | (slot, value, proto) =>
    let result := reconcileKey storing slot value proto
    { own := describe slot.own
      inherited := inheritedName slot.inherited
      extensible := slot.extensible
      proto
      value
      status := statusName result.status
      after := describe result.slot.own
      ownSetterCalls := result.events.count .ownSetter }

/-- Every own descriptor, inherited descriptor, extensibility and written value; `__proto__`
where an inherited accessor with a setter is what `Object.prototype` holds. No row runs an
inherited setter (`reconcileKey_no_inherited_setter`), so the rows leave the count out, and no row
is rejected after writing (`reconcileKey_rejected`, and `reconcileKey_complete` with
`storing_stores`). -/
def run : IO Unit :=
  emitCorpus (owns.flatMap fun own => inheriteds.flatMap fun inherited =>
    bools.flatMap fun extensible => [0, 1].flatMap fun value =>
      let protos := if own.isNone && inherited == .accessor true then bools else [false]
      protos.map ((⟨own, inherited, extensible⟩, value, ·))) observe

private structure GuardedConstruction where
  /-- `custom`, `null` or `object`: the new object's prototype. -/
  base : String
  /-- What the custom prototype or `Object.prototype` holds for the key. -/
  inherited : String
  proto : Bool
  value : Nat
  enumerable : Bool
  after : Descriptor
  deriving ToJson

private def construct : (String × Inherited × Bool) × Nat × Bool → GuardedConstruction
  | ((base, held, proto), value, enumerable) =>
    let slot : Slot Nat := ⟨none, if base == "null" then .none else held, true⟩
    let outcome := constructFromOn storing slot value (base != "custom") (held != .none) enumerable
    { base, inherited := inheritedName held, proto, value, enumerable
      after := describe outcome.slot.own }

/-- New-object writes on a custom prototype holding each inherited descriptor, on a null
prototype, and on `Object.prototype` holding each descriptor for the key, or its own `__proto__`
accessor; each from an enumerable and a non-enumerable source property. Every write succeeds and
runs no setter (`constructFromOn_data`, `constructFromOn_fresh`), so the rows give the property it
creates. -/
def runConstructOn : IO Unit :=
  let bases : List (String × Inherited × Bool) :=
    (inheriteds.map fun i => ("custom", i, false)) ++ [("null", .none, false)] ++
      (inheriteds.map fun i => ("object", i, false)) ++ [("object", .accessor true, true)]
  emitCorpus (bases.flatMap fun base => [0, 1].flatMap fun value => bools.map (base, value, ·))
    construct

private structure SetterWrite where
  /-- `nothing`, or what the setter defines: `data` with its attributes. -/
  defines : String
  writable : Bool := false
  enumerable : Bool := false
  configurable : Bool := false
  extensible : Bool
  value : Nat
  ok : Bool
  after : Descriptor
  objectOk : Bool
  objectAfter : Descriptor
  deriving ToJson

private def assign : Defines Nat × Bool → SetterWrite
  | (d, extensible) =>
    let slot : Slot Nat := ⟨none, .accessor true, extensible⟩
    -- A draft follows its object's extensibility, so a non-extensible object's draft refuses a
    -- new key as the object does (`draftSet_eq`).
    let draft := draftThroughSetter slot d
    let object := throughSetter slot d
    let (name, value, a) := match d with
      | .nothing => ("nothing", 0, plain)
      | .data v a => ("data", v, a)
    { defines := name, writable := a.writable, enumerable := a.enumerable
      configurable := a.configurable, extensible, value, ok := draft.ok
      after := describe draft.slot.own, objectOk := object.ok
      objectAfter := describe object.slot.own }

/-- A recipe's assignment of a key the object lacks through an inherited setter that defines
nothing or defines the key with each set of attributes, on an extensible and a non-extensible
object: the draft's outcome and the object's (`draftThroughSetter_eq`, `_refused`). -/
def runThroughSetter : IO Unit :=
  let defines : List (Defines Nat) :=
    .nothing :: ([0, 1].flatMap fun v => attrs.map fun a => .data v a)
  emitCorpus (defines.flatMap fun d => bools.map (d, ·)) assign

end Reconcile.PropertyWriteOracle
