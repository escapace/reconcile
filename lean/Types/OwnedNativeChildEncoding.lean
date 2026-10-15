import Defs
import Types.OwnedNativeChild

namespace Reconcile.OwnedNativeChild

variable {A ι : Type}

/-- Unlike the scalar native-payload witness, an owned native object has an
    explicit child reference in the existing graph language. -/
def ownerFields (payload : A) (child : ι) : ObjFields A ι :=
  [⟨⟨0⟩, .atom payload⟩, ⟨⟨1⟩, .ref child⟩]

def encodeOwner (payload : A) (child : ι) : Node A ι :=
  .plainObject ⟨1⟩ (ownerFields payload child)

theorem owner_child_refs (payload : A) (child : ι) :
    (encodeOwner payload child).childRefs = [child] := rfl

theorem owner_fields_well_formed (payload : A) (child : ι) :
    ObjFieldsWF (ownerFields payload child) := by
  simp [ObjFieldsWF, ownerFields, List.NodupKeys]

theorem owner_encoding_injective :
    Function.Injective (fun pair : A × ι => encodeOwner pair.1 pair.2) := by
  intro a b h
  have equal : a.1 = b.1 ∧ a.2 = b.2 := by
    simpa [encodeOwner, ownerFields] using h
  exact Prod.ext equal.1 equal.2

end Reconcile.OwnedNativeChild
