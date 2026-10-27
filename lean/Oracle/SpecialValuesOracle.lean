import Produce.SpecialValues
import Lean

/-! Oracle for the `SpecialDecision` and `SpecialValues` families.

`SpecialDecision` (`runDecision`) is `Produce.SpecialValues.choose` on every combination of
facts, with whether `specialFacts` can produce it (`Reachable`). `SpecialValues` (`run`) generates scenarios of `produce` over special values: a date, a
standalone `URLSearchParams` and a Temporal value alone; a buffer with a `Uint8Array` and a
`DataView` over it, and a view the recipe makes over the buffer's copy; a URL with its
`searchParams`, in both index orders. Each scenario reads every subset of the values in index
order (and both orders of a URL and its `searchParams`), changes each copy, changes and restores
it, or leaves it, and holds the values in the result's slots by one of several patterns. Each row
gives every slot's object and that object's dependency under `resolve` and `depOf`. -/

namespace Reconcile.SpecialValuesOracle

open Reconcile.SpecialValues Lean

private def originName : Origin → String
  | .base => "base"
  | .copy => "copy"
  | .untracked => "untracked"

private def decisionName : Decision → String
  | .base => "base"
  | .copy => "copy"
  | .fresh => "fresh"
  | .source => "source"

private structure DecisionRow where
  origin : String
  forced : Bool
  dependenciesStable : Bool
  equivalent : Bool
  decision : String
  reachable : Bool
  deriving ToJson

/-- `choose` on all 24 combinations of facts, and which of them are reachable. -/
def runDecision : IO Unit := do
  let origins : List Origin := [.base, .copy, .untracked]
  let bools := [false, true]
  let rows := origins.flatMap fun origin => bools.flatMap fun forced =>
    bools.flatMap fun dependenciesStable => bools.map fun equivalent =>
      (⟨origin, forced, dependenciesStable, equivalent⟩ : Facts)
  IO.println rows.length
  for f in rows do
    let row : DecisionRow :=
      { origin := originName f.origin, forced := f.forced,
        dependenciesStable := f.dependenciesStable, equivalent := f.equivalent,
        decision := decisionName (choose f), reachable := Reachable f }
    IO.println (toJson row).compress

/-- How the recipe leaves a copy: unchanged, changed, or changed and restored. -/
inductive Change where
  | none
  | edit
  | touch
  deriving DecidableEq

/-- One value as the bridge builds it: the native constructor and the model's value. -/
structure Built where
  native : String
  value : Value
  touch : Bool

/-- A slot of the result, by its key. -/
structure Slot where
  key : String
  ref : Ref
  deriving DecidableEq

/-- A scenario: its values, the order the recipe reads them, and the result's slots. -/
structure Case where
  shape : String
  values : List Built
  reads : List Nat
  slots : List Slot

private def kindOf : String → Kind
  | "date" => .date
  | "buffer" => .buffer
  | "uint8" => .view
  | "dataview" => .view
  | "authored" => .view
  | "url" => .url
  | "params" => .params
  | _ => .temporal

private def built (native : String) (dep : Option Nat) (read : Bool) (change : Change) : Built :=
  ⟨native, ⟨kindOf native, dep, native == "authored", read, change == .edit⟩, change == .touch⟩

private def scenario (c : Case) : Scenario := c.values.map (·.value)

private def changes (copied : Bool) (native : String) : List Change :=
  if copied && native != "temporal" && native != "uint8" && native != "dataview" then
    [.none, .edit, .touch]
  else [.none]

/-- The slot patterns: every value at its key in `current` (current-backed); plus each copy at a
key of its own; each copied value only as its copy; only the values that have a dependency, or
only those without; every value also at a key of its own (not current-backed). A value the recipe
makes is always held at its own key. -/
private def patterns (s : Scenario) : List (List Slot) :=
  let indices := List.range s.length
  let own := indices.filter fun i => (val s i).authored
  let current := indices.filter fun i => !(val s i).authored
  let backed (is : List Nat) := is.map fun i => (⟨s!"v{i}", .value i⟩ : Slot)
  let made := own.map fun i => (⟨s!"a{i}", .value i⟩ : Slot)
  let copies (is : List Nat) :=
    (is.filter (copied s)).map fun i => (⟨s!"c{i}", .copy i⟩ : Slot)
  let refs := current.map fun i => (⟨s!"r{i}", .value i⟩ : Slot)
  [backed current ++ made,
    backed current ++ made ++ copies current,
    backed (current.filter fun i => !copied s i) ++ made ++ copies current,
    backed (current.filter fun i => (val s i).dep.isSome) ++ made,
    backed (current.filter fun i => (val s i).dep.isNone) ++ made,
    backed current ++ made ++ refs]

/-- Whether a slot is current-backed: a value of `current` at its own key. -/
private def backed (slot : Slot) : Bool := slot.key.startsWith "v"

private def subsets : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => let rest := subsets xs; rest ++ rest.map (x :: ·)

private def withSlots (shape : String) (values : List Built) (reads : List Nat) : List Case :=
  let s : Scenario := values.map (·.value)
  (patterns s).eraseDups.filterMap fun slots =>
    if slots.isEmpty then none else some ⟨shape, values, reads, slots⟩

/-- A date, a standalone `URLSearchParams` or a Temporal value. -/
private def singles : List Case :=
  ["date", "params", "temporal"].flatMap fun native =>
    [false, true].flatMap fun read =>
      (changes read native).flatMap fun change =>
        withSlots native [built native none read change] (if read then [0] else [])

/-- A buffer with a `Uint8Array` and a `DataView` over it, read by every subset, and a view the
recipe makes over the buffer's copy. -/
private def binary : List Case :=
  (subsets [0, 1, 2]).flatMap fun reads =>
    let copiedBuffer := !reads.isEmpty
    (changes copiedBuffer "buffer").flatMap fun change =>
      (if copiedBuffer then [false, true] else [false]).flatMap fun made =>
        let values :=
          [built "buffer" none (reads.contains 0) change,
            built "uint8" (some 0) (reads.contains 1) .none,
            built "dataview" (some 0) (reads.contains 2) .none] ++
          (if made then [built "authored" (some 0) false .none] else [])
        withSlots "binary" values reads

/-- A URL with its `searchParams`, at indices `u` and `p`, read by every subset in both orders. -/
private def urls (u p : Nat) : List Case :=
  let orders := [[], [u], [p], [u, p], [p, u]]
  orders.flatMap fun reads =>
    (changes (reads.contains u) "url").flatMap fun urlChange =>
      (changes (!reads.isEmpty) "params").flatMap fun paramsChange =>
        let pair :=
          [(u, built "url" (some p) (reads.contains u) urlChange),
            (p, built "params" none (reads.contains p) paramsChange)]
        let values := (pair.mergeSort (fun a b => a.1 ≤ b.1)).map (·.2)
        withSlots "url" values reads

/-- Every scenario. -/
def cases : List Case := singles ++ binary ++ urls 0 1 ++ urls 1 0

private structure ObjJson where
  tag : String
  index : Nat
  deriving ToJson

private def objJson : Obj → ObjJson
  | .value i => ⟨"value", i⟩
  | .copy i => ⟨"copy", i⟩
  | .fresh i => ⟨"fresh", i⟩

private structure ValueJson where
  native : String
  dep : Option Nat
  read : Bool
  edit : Bool
  touch : Bool
  deriving ToJson

private structure SlotJson where
  key : String
  ref : String
  index : Nat
  obj : ObjJson
  dep : Option ObjJson
  deriving ToJson

private structure Row where
  shape : String
  values : List ValueJson
  reads : List Nat
  slots : List SlotJson
  deriving ToJson

/-- Every scenario with each slot's object and that object's dependency. A scenario outside `WF`
is a corpus error. -/
def run : IO Unit := do
  IO.println cases.length
  for c in cases do
    let s := scenario c
    unless check s do throw (IO.userError s!"scenario outside WF: {c.shape}")
    let held (i : Nat) : Bool := c.slots.any fun slot => slot.ref.index == i
    let slots := c.slots.map fun slot =>
      let obj := resolve s held slot.ref (backed slot)
      let (ref, index) := match slot.ref with
        | .value i => ("value", i)
        | .copy i => ("copy", i)
      ({ key := slot.key, ref, index, obj := objJson obj,
         dep := (depOf s held obj).map objJson } : SlotJson)
    let values := c.values.map fun b =>
      ({ native := b.native, dep := b.value.dep, read := b.value.read, edit := b.value.edit,
         touch := b.touch } : ValueJson)
    IO.println (toJson ({ shape := c.shape, values, reads := c.reads, slots } : Row)).compress

end Reconcile.SpecialValuesOracle
