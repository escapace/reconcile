import Oracle.SerializationOracle
import Oracle.SerializationCollectionOracle
import Oracle.OwnedNativeChildOracle
import Oracle.NativeValueOracle
import Oracle.ContractOracle
import Oracle.PolicyOracle
import Oracle.PropertyOrderOracle
import Oracle.PropertyWriteOracle
import Oracle.PropertyPlacementOracle
import Oracle.KeyOrderOracle
import Oracle.AtomsOracle
import Oracle.RecognitionPlainOracle
import Oracle.IngressOracle
import Oracle.SettledChildrenOracle
import Oracle.WriteFreeReadbackOracle
import Oracle.DraftSurfaceOracle
import Oracle.DraftClassOracle
import Oracle.DraftIterationOracle
import Oracle.DraftReadOracle
import Oracle.DraftMembersOracle
import Oracle.DraftSetMethodsOracle
import Oracle.CopyPrototypeOracle
import Oracle.SeededRequirementsOracle
import Oracle.CompactImmutableOracle
import Oracle.FactRenamingOracle
import Oracle.DeferredOrderOracle
import Oracle.SelectionUnwindOracle
import Oracle.PrunedOracle

/-! Sequential JSON-line requests share one imported Lean environment.
Oracle output remains unchanged. A record-separator line terminates each response;
JSON strings cannot contain that unescaped control character. -/
namespace Reconcile.RuntimeOracle

open Lean

private structure Request where
  family : String
  args : List String := []
  input : String := ""
  deriving FromJson

private def dispatch (request : Request) : IO Unit := do
  match request.family with
  | "Serialization" => SerializationOracle.run request.input
  | "SerializationCollection" => SerializationCollectionOracle.run request.input
  | "OwnedNativeChild" => OwnedNativeChildOracle.run request.input
  | "NativeValue" => NativeValueOracle.run request.input
  | "Contract" =>
    if (← ContractOracle.run request.args) != 0 then throw (IO.userError "Contract oracle failed")
  | "Policy" =>
    if (← PolicyOracle.run request.args) != 0 then throw (IO.userError "Policy oracle failed")
  | "PropertyOrder" => PropertyOrderOracle.run
  | "PropertyWrite" => PropertyWriteOracle.run
  | "PropertyConstructOn" => PropertyWriteOracle.runConstructOn
  | "PropertyThroughSetter" => PropertyWriteOracle.runThroughSetter
  | "PropertyPlacement" => PropertyPlacementOracle.run
  | "KeyOrder" => KeyOrderOracle.run
  | "Atoms" => AtomsOracle.run
  | "RecognitionPlain" => RecognitionPlainOracle.run
  | "Ingress" => IngressOracle.run
  | "WriteFreeReadback" => WriteFreeReadbackOracle.run
  | "DraftSurface" => DraftSurfaceOracle.run
  | "DraftClass" => DraftClassOracle.run
  | "DraftIteration" => DraftIterationOracle.run
  | "DraftRead" => DraftReadOracle.run
  | "SettledChildren" => SettledChildrenOracle.run
  | "DraftMembers" => DraftMembersOracle.run
  | "DraftSetMethods" => DraftSetMethodsOracle.run
  | "CopyPrototype" => CopyPrototypeOracle.run
  | "SeededRequirements" => SeededRequirementsOracle.run request.args
  | "CompactImmutable" => CompactImmutableOracle.run request.args
  | "FactRenaming" => FactRenamingOracle.run request.args
  | "DeferredOrder" => DeferredOrderOracle.run request.input
  | "SelectionUnwind" => SelectionUnwindOracle.run request.input
  | "Pruned" =>
    if (← PrunedOracle.run request.args) != 0 then throw (IO.userError "Pruned oracle failed")
  | _ => throw (IO.userError s!"Unknown oracle family: {request.family}")

private def finish (error : Option String) : IO Unit := do
  let output ← IO.getStdout
  output.putStrLn (String.singleton (Char.ofNat 30) ++ (toJson error).compress)
  output.flush

def serve : IO Unit := do
  let input ← IO.getStdin
  finish none
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    try
      let request ← IO.ofExcept (Json.parse line >>= fromJson? (α := Request))
      dispatch request
      finish none
    catch error => finish (some error.toString)

end Reconcile.RuntimeOracle
