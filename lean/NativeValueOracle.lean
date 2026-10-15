import Types.NativeValue
import Lean

namespace Reconcile.NativeValueOracle
open Lean Types.NativeValue

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

def temporalKind : String → Except String TemporalKind
  | "Instant" => pure .instant
  | "Duration" => pure .duration
  | "PlainDate" => pure .plainDate
  | "PlainTime" => pure .plainTime
  | "PlainDateTime" => pure .plainDateTime
  | "PlainYearMonth" => pure .plainYearMonth
  | "PlainMonthDay" => pure .plainMonthDay
  | "ZonedDateTime" => pure .zonedDateTime
  | _ => throw "Unknown native kind"

def decode (input : InputPayload) : Except String Payload := do
  match input.kind with
  | "URL" =>
    match input.values with
    | [href] => pure (.url href)
    | _ => throw "URL requires one href label"
  | "URLSearchParams" => pure (.parameters input.entries)
  | kind => pure (.temporal (← temporalKind kind) input.constructor input.values)

def evaluate (input : Input) : Except String Json := do
  let current ← decode input.current
  let desired ← decode input.desired
  pure (Json.mkObj [
    ("compatible", toJson (compatible current desired)),
    ("reusable", toJson (reusable current desired)),
    ("published", toJson ((publish current desired).isSome)),
    ("entries", toJson (appendEntries [] input.desired.entries))])

def run (input : String) : IO Unit := do
  let json ← IO.ofExcept (Json.parse input)
  let inputs ← IO.ofExcept (fromJson? (α := Array Input) json)
  let results ← IO.ofExcept (inputs.mapM evaluate)
  (← IO.getStdout).putStrLn (toJson results).compress

end Reconcile.NativeValueOracle
