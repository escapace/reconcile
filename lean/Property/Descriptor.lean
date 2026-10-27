/-! # Own property descriptors

The descriptors of own properties, shared by the one-key write model (`PropertyWrite`) and the
specification graphs (`Spec.Graph`): the attributes of a data property, the attributes an
assignment or a copy gives a new property, and an own property, data or accessor, with the value a
read returns. The accessor's setter is a parameter: `PropertyWrite.Own` records only whether there
is one, since it takes the setter's effect as application code, and `Spec.Slot` records whether
it is absent, stores what it receives, or drops it. -/

namespace Reconcile

/-- The attributes of a data property. -/
structure Attrs where
  writable : Bool
  enumerable : Bool
  configurable : Bool
  deriving DecidableEq, Repr, Inhabited

/-- The attributes an assignment, or `defineData`, gives a new property. -/
def Attrs.plain : Attrs := ⟨true, true, true⟩

/-- The attributes of a property `reconcile` adds, or a new object copies, from a source property
with this enumerability: writable and configurable, with the source's enumerability. -/
def Attrs.copied (enumerable : Bool) : Attrs := ⟨true, enumerable, true⟩

/-- An own property: data with attributes, or an accessor whose getter returns `value`, with a
setter described by `S`, and its enumerability and configurability. -/
inductive OwnProperty (V S : Type) where
  | data (value : V) (attrs : Attrs)
  | accessor (value : V) (setter : S) (enumerable configurable : Bool)
  deriving DecidableEq, Repr, Inhabited

namespace OwnProperty

variable {V S : Type}

/-- The value a read of the property returns, `[[Get]]`. -/
def value : OwnProperty V S → V
  | .data v _ => v
  | .accessor v .. => v

def enumerable : OwnProperty V S → Bool
  | .data _ a => a.enumerable
  | .accessor _ _ e _ => e

def configurable : OwnProperty V S → Bool
  | .data _ a => a.configurable
  | .accessor _ _ _ c => c

end OwnProperty

end Reconcile
