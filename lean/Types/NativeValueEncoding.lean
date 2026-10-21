import Types.Cell
import Types.NativeValue

/-! Encodes a native value as a heap node that holds its payload as an atom in one slot
(`Types.Cell`), and a bigint as an atom, both injectively. -/

namespace Reconcile.Types.NativeValue

/-- Each native identity remains a heap node; its payload is an atom in one slot.
    This is an encoding witness, not a claim that native objects are JS records. -/
def encode {ι : Type} (payload : Payload) : Node Payload ι :=
  Cell.encode (.atom payload)

theorem encode_injective {ι : Type} : Function.Injective (encode (ι := ι)) := by
  intro a b h
  have h' := Cell.encode_injective h
  exact Value.atom.inj h'

theorem no_child_refs {ι : Type} (payload : Payload) :
    (encode (ι := ι) payload).childRefs = [] := rfl

theorem fields_well_formed (payload : Payload) :
    ObjFieldsWF (ι := Nat) [⟨Cell.key, .atom payload⟩] :=
  Cell.fields_well_formed _

/-- Primitive bigint needs no heap node or new kind. Native bigint equality must
    correspond to equality of this mathematical integer label. -/
def bigint {ι : Type} (value : Int) : Value Int ι := .atom value

theorem bigint_injective {ι : Type} : Function.Injective (bigint (ι := ι)) := by
  intro a b h
  exact Value.atom.inj h

end Reconcile.Types.NativeValue
