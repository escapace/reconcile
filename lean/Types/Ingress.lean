import Types.Atoms
import Types.RecognitionPlain

/-!
# One prototype read per object at ingress

Built-in ingress (`recognize` in `src/adapters/recognition.ts`, given a `PrototypeRead`) reads an
object's prototype once and decides both its kind (`Types.RecognitionPlain.recognize`) and, for
the plain-object fallback, whether it is an atom (`Types.Atoms.classify`), from that one read; a
separate atom split reads it again. The callers that meet the object first, capture, the snapshot
walk and draft creation, then hand the same prototype to its later readers before the first write:
discovery, the preflight's inherited-accessor check, the Vue marker walk and a draft's target.

Both classifiers take the chain as input, so sharing the first read changes no decision; this
module states that the shared ingress decides as the two separate ones and counts the reads it
saves. That a later read would answer as the first did is the runtime's stability obligation.
-/

namespace Reconcile.Types.Ingress

open Reconcile.Types

/-- One prototype as the two classifiers label it. -/
structure Proto where
  atom : Atoms.Proto
  recognition : RecognitionPlain.Proto

/-- The chain an object's prototype reads return, from its own prototype on. -/
structure Chain where
  protos : List Proto
  raises : Bool

def atoms (c : Chain) : Atoms.Chain := c.protos.map (·.atom)

def recognition (c : Chain) : RecognitionPlain.Chain := ⟨c.protos.map (·.recognition), c.raises⟩

/-- The outcome of ingress: a structural rank, the plain-object kind, an atom, or a raised read. -/
inductive Outcome where
  | structural (rank : Nat)
  | object
  | atom
  | raised
  deriving DecidableEq, Repr

/-- Recognition, then the atom split of the fallback rank 10 (`Atoms.ingress`). The split takes
the chain as input, so it decides the same whether it reads the prototype again or not. -/
def ingress (isArray : Recognition.ProbeOutcome) (c : Chain) (brand : Bool)
    (ts : RecognitionPlain.Targets) : Outcome :=
  match
    RecognitionPlain.outcome (RecognitionPlain.recognize 10 isArray (recognition c) brand ts) with
  | (some rank, _) =>
    match Atoms.ingress 10 rank (atoms c) with
    | .structural r => .structural r
    | .object => .object
    | .atom => .atom
  | (none, _) => .raised

/-- Reads of the object itself: recognition's one read, and for the plain-object fallback of an
object that is not an array, the atom split's own read unless it is shared. -/
def ownReads (shared : Bool) (isArray : Recognition.ProbeOutcome) (c : Chain) (brand : Bool)
    (ts : RecognitionPlain.Targets) : Nat :=
  if isArray = .hit then 0
  else 1 + (if !shared && ingress isArray c brand ts ∈ [.object, .atom] then 1 else 0)

/-- The atom split's reads of prototypes after the object's own: the walk `Atoms.classify`
makes past its first read. -/
def walkReads (c : Chain) : Nat := (Atoms.classify (atoms c)).2 - 1

/-- Sharing the first read reads the object once; a separate atom split read it twice for the
fallback. The walk over its prototypes is the same either way. -/
theorem ownReads_shared (isArray : Recognition.ProbeOutcome) (c : Chain) (brand : Bool)
    (ts : RecognitionPlain.Targets) (h : isArray ≠ .hit) :
    ownReads true isArray c brand ts = 1 ∧
      ownReads false isArray c brand ts =
        1 + (if ingress isArray c brand ts ∈ [.object, .atom] then 1 else 0) := by
  simp [ownReads, h]

/-- The atom split's walk past the first read is one read per prototype it passes. -/
theorem walkReads_eq (c : Chain) (h : (atoms c).head? ≠ some .array) :
    walkReads c = ((atoms c).takeWhile Atoms.walksOn).length := by
  unfold walkReads
  rw [Atoms.classify_reads _ h]
  omega

/-- A plain object: one shared read decides it, and it is not an atom. -/
example : ingress .miss ⟨[⟨.object, .object⟩], false⟩ false RecognitionPlain.absent = .object :=
  by decide

/-- A `RegExp`: recognition falls back, and the atom split finds its listed prototype. -/
example : ingress .miss ⟨[⟨.listed 0, .other 7⟩, ⟨.object, .object⟩], false⟩ false
    RecognitionPlain.absent = .atom := by decide

/-- A `Map`: recognition selects rank 2 and the atom split keeps it. -/
example : ingress .miss ⟨[⟨.data 3, .builtin 2⟩, ⟨.object, .object⟩], false⟩ false
    RecognitionPlain.absent = .structural 2 := by decide

end Reconcile.Types.Ingress
