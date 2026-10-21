import Property.PropertyWrite
import Lean

/-! Oracles for the `PropertyWrite`, `PropertyConstructOn` and `PropertyThroughSetter` families:
single-key outcomes of `reconcileKey` and the alternative rule over every descriptor case,
new-object writes by `constructFromOn`, and a recipe's assignment through an inherited setter
(`draftThroughSetter`). -/

namespace Reconcile.PropertyWriteOracle

open Reconcile.PropertyWrite Lean

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
  inheritedSetterCalls : Nat
  previousStatus : String
  previousAfter : Descriptor
  previousInheritedSetterCalls : Nat
  deriving ToJson

/-- Every own descriptor, inherited descriptor, extensibility and written value; `__proto__`
where an inherited accessor with a setter is what `Object.prototype` holds. -/
def run : IO Unit := do
  let cases := owns.flatMap fun own => inheriteds.flatMap fun inherited =>
    bools.flatMap fun extensible => [0, 1].flatMap fun value =>
      let protos := if own.isNone && inherited == .accessor true then bools else [false]
      protos.map fun proto => (⟨own, inherited, extensible⟩, value, proto)
  IO.println cases.length
  for (slot, value, proto) in cases do
    let result := reconcileKey storing slot value proto
    let previous := reconcileOld storing slot value proto
    if Event.inheritedSetter ∈ result.events then
      throw (IO.userError "PropertyWrite oracle ran an inherited setter")
    if result.status == .rejectedAfterWriting then
      throw (IO.userError "PropertyWrite oracle failed a readback with storing setters")
    let observation : Observation :=
      { own := describe slot.own
        inherited := inheritedName slot.inherited
        extensible := slot.extensible
        proto
        value
        status := statusName result.status
        after := describe result.slot.own
        ownSetterCalls := result.events.count .ownSetter
        inheritedSetterCalls := result.events.count .inheritedSetter
        previousStatus := statusName previous.status
        previousAfter := describe previous.slot.own
        previousInheritedSetterCalls := previous.events.count .inheritedSetter }
    IO.println (toJson observation).compress

private structure GuardedConstruction where
  /-- `custom`, `null` or `object`: the new object's prototype. -/
  base : String
  /-- What the custom prototype or `Object.prototype` holds for the key. -/
  inherited : String
  proto : Bool
  value : Nat
  enumerable : Bool
  ok : Bool
  after : Descriptor
  setterCalls : Nat
  deriving ToJson

/-- New-object writes on a custom prototype holding each inherited descriptor, on a null
prototype, and on `Object.prototype` holding each descriptor for the key, or its own `__proto__`
accessor; each from an enumerable and a non-enumerable source property
(`constructFromOn_fresh`). -/
def runConstructOn : IO Unit := do
  let bases : List (String × Inherited × Bool) :=
    (inheriteds.map fun i => ("custom", i, false)) ++ [("null", .none, false)] ++
      (inheriteds.map fun i => ("object", i, false)) ++ [("object", .accessor true, true)]
  let cases := bases.flatMap fun b => [0, 1].flatMap fun value => bools.map fun e => (b, value, e)
  IO.println cases.length
  for ((base, held, proto), value, enumerable) in cases do
    let standard := base != "custom"
    let slot : Slot Nat := ⟨none, if base == "null" then .none else held, true⟩
    let outcome := constructFromOn storing slot value standard (held != .none) enumerable
    let observation : GuardedConstruction :=
      { base, inherited := inheritedName held, proto, value, enumerable, ok := outcome.ok
        after := describe outcome.slot.own, setterCalls := outcome.events.length }
    IO.println (toJson observation).compress

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

/-- A recipe's assignment of a key the object lacks through an inherited setter that defines
nothing or defines the key with each set of attributes, on an extensible and a non-extensible
object: the draft's outcome and the object's (`draftThroughSetter_eq`, `_refused`). -/
def runThroughSetter : IO Unit := do
  let defines : List (Defines Nat) :=
    .nothing :: ([0, 1].flatMap fun v => attrs.map fun a => .data v a)
  let cases := defines.flatMap fun d => bools.map fun extensible => (d, extensible)
  IO.println cases.length
  for (d, extensible) in cases do
    let slot : Slot Nat := ⟨none, .accessor true, extensible⟩
    -- A draft accepts a new key by assignment whatever its object's extensibility, since its
    -- result is a new object, so its slot is extensible.
    let draft := draftThroughSetter { slot with extensible := true } d
    let object := throughSetter slot d
    let (name, value, a) := match d with
      | .nothing => ("nothing", 0, plain)
      | .data v a => ("data", v, a)
    let observation : SetterWrite :=
      { defines := name, writable := a.writable, enumerable := a.enumerable
        configurable := a.configurable, extensible, value, ok := draft.ok
        after := describe draft.slot.own, objectOk := object.ok
        objectAfter := describe object.slot.own }
    IO.println (toJson observation).compress

end Reconcile.PropertyWriteOracle
