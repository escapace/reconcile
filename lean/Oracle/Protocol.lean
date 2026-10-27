import Property.PropertyOrder
import Lean

/-! How the oracle families answer the bridges. `RuntimeOracle` passes each family the request's
`input` text, and the family writes its answer as lines of compact JSON (`line`): a generated
corpus as its case count, which its bridge freezes, then one row per case (`emitCorpus`); a served
request, whose input is a JSON array, as the array of each element's answer (`serveArray`). A
property key crosses as one number (`keyCode`).

An oracle does not re-check what a theorem proves of its data. It checks the premises its
theorems need of each input a bridge sends, and of each generated case whose construction does not
ensure them; a failed check fails the request. -/

namespace Reconcile.Protocol

open Lean Reconcile.PropertyOrder

/-- One line of output. `Json.compress` leaves U+2028 and U+2029 raw in strings, and the bridges'
reader, `node:readline`, also ends a line at each, so both are escaped. A text whose byte and
character counts agree, both cached, is ASCII and holds neither. -/
def line (json : Json) : String :=
  let text := json.compress
  if text.utf8ByteSize == text.length then text
  else (text.replace "\u2028" "\\u2028").replace "\u2029" "\\u2029"

/-- Writes a generated corpus: its case count, then each case's row on a line of its own. A case
that fails a check fails the request. Each row is computed as it is written: a list of rows that
depends on nothing is a closed term, which the compiler evaluates when the oracle starts. -/
def emitCheckedCorpus {κ α : Type} [ToJson α] (cases : List κ) (row : κ → Except String α) :
    IO Unit := do
  IO.println cases.length
  for case in cases do IO.println (line (toJson (← IO.ofExcept (row case))))

/-- Writes a generated corpus whose cases need no check (`emitCheckedCorpus`). -/
def emitCorpus {κ α : Type} [ToJson α] (cases : List κ) (row : κ → α) : IO Unit :=
  emitCheckedCorpus cases fun case => pure (row case)

/-- Answers a request whose input is a JSON array with the array of each element's answer. -/
def serveArray {α β : Type} [FromJson α] [ToJson β] (input : String)
    (answer : α → Except String β) : IO Unit := do
  let requests ← IO.ofExcept (Json.parse input >>= fromJson? (α := Array α))
  IO.println (line (toJson (← IO.ofExcept (requests.mapM answer))))

/-- A property key's number: three times its label, plus 0 for an integer key, 1 for a name and 2
for a symbol. -/
def keyCode : Key → Nat
  | .index label => 3 * label
  | .name label => 3 * label + 1
  | .symbol label => 3 * label + 2

/-- The key a number stands for; every number stands for one. -/
def keyOfCode (code : Nat) : Key :=
  match code % 3 with
  | 0 => .index (code / 3)
  | 1 => .name (code / 3)
  | _ => .symbol (code / 3)

theorem keyOfCode_keyCode (key : Key) : keyOfCode (keyCode key) = key := by
  cases key <;> simp [keyCode, keyOfCode] <;> omega

end Reconcile.Protocol
