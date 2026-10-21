import Produce.DraftRead
import Lean

/-! Oracle for the `DraftRead` family: the source `DraftRead.read` takes each read from, before and
after the first write, for an owned and a not owned key. -/

namespace Reconcile.DraftReadOracle

open Reconcile.DraftRead Lean

private structure Observation where
  copied : Bool
  owned : Bool
  source : String
  deriving ToJson

private def sourceName : Source → String
  | .own => "own"
  | .prototype => "prototype"
  | .wrapper => "wrapper"

/-- Every read, before and after the first write, of an owned and a not owned key, with the source
the draft takes it from. -/
def run : IO Unit := do
  IO.println 4
  for copied in [false, true] do
    for owned in [false, true] do
      let row : Observation := { copied, owned, source := sourceName (read copied owned) }
      IO.println (toJson row).compress

end Reconcile.DraftReadOracle
