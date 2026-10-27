import Types.NativeWrites
import Lean

/-! Oracle for the `NativeValue` family: for each fixture pair, publication under
`Types.NativeWrites`: whether the preflight keeps the current value, whether `produce` may reuse
it, whether a kept value is written, and a parameter list's entries afterwards. -/

namespace Reconcile.NativeValueOracle
open Lean Types.NativeWrites

structure InputPayload where
  kind : String
  constructor : Nat := 0
  values : List String := []
  entries : List (String × String) := []
  deriving FromJson

structure Input where
  current : InputPayload
  desired : InputPayload
  deriving FromJson

def temporalKinds : List String :=
  ["Instant", "Duration", "PlainDate", "PlainTime", "PlainDateTime", "PlainYearMonth",
    "PlainMonthDay", "ZonedDateTime"]

/-- A URL by its `href`, a parameter list by its text, a Temporal value by its class and
constructor label and its observed fields. -/
def decode (input : InputPayload) : Except String Native := do
  match input.kind, input.values with
  | "URL", [href] => pure (.url href)
  | "URL", _ => throw "URL requires one href label"
  | "URLSearchParams", [text] => pure (.parameters text)
  | "URLSearchParams", _ => throw "URLSearchParams requires its text"
  | kind, values =>
    if temporalKinds.contains kind then pure (.temporal s!"{kind}/{input.constructor}" values)
    else throw "Unknown native kind"

def evaluate (input : Input) : Except String Json := do
  let current ← decode input.current
  let desired ← decode input.desired
  let (unchanged, entries) := match publish current desired with
    | .keep writes =>
      (some writes.isEmpty, entriesAfter writes input.current.entries input.desired.entries)
    | .replace => (none, input.current.entries)
  pure (Json.mkObj [
    ("compatible", toJson (compatible current desired)),
    ("reusable", toJson (reusable current desired)),
    ("unchanged", toJson unchanged),
    ("entries", toJson entries)])

def run (input : String) : IO Unit := do
  let json ← IO.ofExcept (Json.parse input)
  let inputs ← IO.ofExcept (fromJson? (α := Array Input) json)
  let results ← IO.ofExcept (inputs.mapM evaluate)
  (← IO.getStdout).putStrLn (toJson results).compress

end Reconcile.NativeValueOracle
