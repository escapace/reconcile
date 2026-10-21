import Heap.Defs

/-! The test-only runtime Cell module declares one own slot named "value". Its native premise is
faithful observation and publication of that slot. The constructor and registration predicate
stay outside Lean; this encoding witness introduces no new node kind or solver rule. -/

namespace Reconcile.Types.Cell

variable {A ι : Type}

def key : PropertyKey := ⟨0⟩
def prototype : ProtoLabel := ⟨0⟩

def encode (value : Value A ι) : Node A ι :=
  .plainObject prototype [⟨key, value⟩]

theorem encode_injective : Function.Injective (encode (A := A) (ι := ι)) := by
  intro a b h
  simpa [encode] using h

theorem fields_well_formed (value : Value A ι) :
    ObjFieldsWF [⟨key, value⟩] := by
  simp [ObjFieldsWF, List.NodupKeys]

theorem child_refs (value : Value A ι) :
    (encode value).childRefs = (match value with | .atom _ => [] | .ref node => [node]) := by
  cases value <;> rfl

theorem existing_kind (value : Value A ι) : (encode value).kind = .plainObject := rfl

end Reconcile.Types.Cell
