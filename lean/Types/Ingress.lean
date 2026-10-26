import Types.Atoms
import Types.RecognitionPlain

/-!
# One prototype read per object at ingress

Built-in ingress (`recognize` in `src/adapters/recognition.ts`, given a `PrototypeRead`) reads an
object's prototype once and decides both its kind (`Types.RecognitionPlain.recognize`) and, for
the plain-object fallback, whether it is an atom (`Types.Atoms.classify`), from that one read; a
separate atom split reads it again. The callers that meet the object first, capture, the snapshot
walk and draft creation, then hand the same prototype to its later readers before the first write:
discovery, the preflight's inherited-accessor check and a draft's target.

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
the chain as input, so it decides the same whether it reads the prototype again or not. A branded
object is a typed array over a buffer the environment recognizes. -/
def ingress (isArray : Recognition.ProbeOutcome) (c : Chain) (brand : Bool)
    (ts : RecognitionPlain.Targets) : Outcome :=
  match RecognitionPlain.outcome
      (RecognitionPlain.recognize 10 isArray (recognition c) brand brand false ts) with
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

/-! ## One read of a view's element type and of a copied buffer's prototype

A view's element type (`viewElement` in `src/types/shared/binary-native.ts`, absent for a
`DataView`) selects the getters that read its buffer, offset and length; a buffer's copy
(`copyBuffer`) reads the buffer's prototype to decide whether it is shared and to give the copy
that prototype. Recognition and the copies read each once and pass the answer on. The traces below
list the built-in reads before and after: every getter the earlier code called is still called,
each once. That a repeated read answers as the first, so the answer stands for the reads it
replaces, is the stability obligation above; no application code runs during these reads. -/

/-- A built-in read of a view or a buffer: a view's element type; its buffer, offset or length
through the typed-array getters (`true`) or the `DataView` ones; an object's prototype; a buffer's
byte length, resizability and maximum length. -/
inductive Read where
  | element
  | buffer (typed : Bool)
  | offset (typed : Bool)
  | length (typed : Bool)
  | prototype
  | byteLength
  | resizable
  | maximum
  deriving DecidableEq, Repr

/-- Recognition's reads of a view (`builtinRemainingMatch`): before, the buffer's getter and the
typed-array brand test each read the element type, which answers `typed`. -/
def recognitionEach (typed : Bool) : List Read :=
  [.element, .buffer typed] ++ (if typed then [.element] else [])

def recognitionOnce (typed : Bool) : List Read := [.element, .buffer typed]

theorem recognition_once (typed : Bool) :
    recognitionOnce typed = (recognitionEach typed).eraseDups := by
  cases typed <;> decide

/-- A view's copy (`copyTypedArray`, `copyDataView`): before, the element type was read again for
each of the offset and length of a `DataView`-kind copy, then the prototype. A typed-array-kind
copy (`dataView` false) is of a value with the typed-array brand, so `typed` holds for it. -/
def viewCopyEach (typed dataView : Bool) : List Read :=
  if dataView then [.element, .offset typed, .element, .length typed, .prototype]
  else [.element, .offset typed, .length typed, .prototype]

/-- The copy now reads the prototype and the element type once, as default arguments, and both
getters on that answer. -/
def viewCopyOnce (typed : Bool) : List Read :=
  [.prototype, .element, .offset typed, .length typed]

theorem viewCopy_once (typed dataView : Bool) :
    (viewCopyOnce typed).Perm (viewCopyEach typed dataView).eraseDups := by
  cases typed <;> cases dataView <;> decide

/-- The snapshot walk's view copy, after recognition: before, it read the buffer through a fresh
element read, then copied as `viewCopyEach`. -/
def snapshotViewEach (typed dataView : Bool) : List Read :=
  [.element, .buffer typed] ++ viewCopyEach typed dataView

/-- Now it reads the element type once, for the buffer and both getters, and takes the prototype
recognition read (Ingress). -/
def snapshotViewOnce (typed : Bool) : List Read :=
  [.element, .buffer typed, .offset typed, .length typed]

theorem snapshotView_once (typed dataView : Bool) :
    snapshotViewOnce typed = ((snapshotViewEach typed dataView).eraseDups).erase .prototype := by
  cases typed <;> cases dataView <;> decide

/-- A buffer's copy: before, `isShared` read the prototype, `bufferByteLength` read it again
through `isShared`, and the copy's prototype was a third read. A shared buffer is its own copy. -/
def bufferCopyEach (shared resizable : Bool) : List Read :=
  if shared then [.prototype]
  else
    [.prototype, .prototype, .byteLength, .resizable] ++ (if resizable then [.maximum] else []) ++
      [.prototype]

/-- Now the prototype is read once, or taken from the snapshot walk's recognition read. -/
def bufferCopyOnce (shared resizable : Bool) : List Read :=
  if shared then [.prototype]
  else [.prototype, .byteLength, .resizable] ++ (if resizable then [.maximum] else [])

theorem bufferCopy_once (shared resizable : Bool) :
    bufferCopyOnce shared resizable = (bufferCopyEach shared resizable).eraseDups := by
  cases shared <;> cases resizable <;> decide

/-- Counterexample: a `DataView`-kind copy of a typed array (whose prototype was set to
`DataView.prototype`) must take the typed-array getters its element type selects; the `DataView`
getters would be the wrong reads. -/
example : viewCopyOnce true ≠ [.prototype, .element, .offset false, .length false] := by decide

end Reconcile.Types.Ingress
