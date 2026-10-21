import Heap.Publication

/-! Successful reconciliation of a captured graph. Selection and runtime adapters supply local
obligations; global graph correctness is proved from publication. -/

namespace Reconcile

/-- Namespace embedding for the primitive boundary's direct `return next`.
    The right summand here does not imply a runtime allocation. -/
def nextRootImage {A : Type} : Value A NextId → Value A ResId :=
  Value.remap fun n => .inr ⟨n.val⟩

/-- Binary extent lookup; validity of captured binary layouts is an adapter obligation. -/
def bufferExtent {A I : Type} [DecidableEq I] (heap : Heap A I) (i : I) : Option Nat :=
  match heap.lookup i with
  | some (.arrayBuffer bytes) => some bytes.length
  | _ => none

/-- Missing/non-buffer dependencies are invalid captured view shapes. -/
def matchingBufferExtents {A : Type} (curHeap : Heap A CurId) (nextHeap : Heap A NextId)
    (cb : CurId) (nb : NextId) : Bool :=
  match bufferExtent curHeap cb, bufferExtent nextHeap nb with
  | some a, some b => decide (a = b)
  | _, _ => false

/-- The shape-only part of retention. Backing identity is checked separately. -/
def compatibleShape {A : Type} (curHeap : Heap A CurId) (nextHeap : Heap A NextId)
    (cur : Node A CurId) (next : Node A NextId) : Bool :=
  match cur, next with
  | .arrayBuffer a, .arrayBuffer b => decide (a.length = b.length)
  | .dataView cb co cl, .dataView nb no nl =>
    decide (co = no ∧ cl = nl) && matchingBufferExtents curHeap nextHeap cb nb
  | .typedArray ct cb co cl _, .typedArray nt nb no nl _ =>
    decide (ct = nt ∧ co = no ∧ cl = nl) && matchingBufferExtents curHeap nextHeap cb nb
  | a, b => decide (a.kind = b.kind)

inductive PublicationFailure where
  | incompatibleRoot
  | missingRoot
  | failedPublication
  deriving DecidableEq, Repr

/-- Preflight root dispatch for captured inputs. Success is provisional until
    publication/readback succeeds. Failure carries no rollback guarantee. -/
def execReconcileRoot {A : Type} (curHeap : Heap A CurId) (nextHeap : Heap A NextId)
    (current : Value A CurId) (next : Value A NextId) :
    Except PublicationFailure (Value A ResId) :=
  match current, next with
  | .atom _, _ => .ok (nextRootImage next)
  | .ref _, .atom a => .ok (.atom a)
  | .ref cr, .ref nr =>
    match curHeap.lookup cr, nextHeap.lookup nr with
    | some cn, some nn =>
      if compatibleShape curHeap nextHeap cn nn then .ok (.ref (.inl cr))
      else .error .incompatibleRoot
    | _, _ => .error .missingRoot

/-- Retained plain objects keep their current prototype. Fresh objects use next's. -/
def publicationProto {A : Type} (curHeap : Heap A CurId) (image : NextId → ResId)
    (n : NextId) (p : ProtoLabel) : ProtoLabel :=
  match image n with
  | .inl c => match curHeap.lookup c with
    | some (.plainObject cp _) => cp
    | _ => p
  | .inr _ => p

/-- One selected image and its finite-domain feasibility conditions. The ordered
    candidate relation and storage labels come from capture/selection adapters.
    This does not claim completeness or optimality of the runtime search. -/
structure ReconcileWitness {A : Type} (curHeap : Heap A CurId) (nextHeap : Heap A NextId) where
  image : NextId → ResId
  storage : ResId → Nat
  candidates : NextId → CurId → Prop
  fixed : NextId → Option CurId
  /-- Distinct captured nodes cannot own the same backing identity. -/
  storageDistinct : ∀ n₁ ∈ nextHeap.keys, ∀ n₂ ∈ nextHeap.keys,
    storage (image n₁) = storage (image n₂) → n₁ = n₂
  fixedImage : ∀ n c, fixed n = some c → image n = .inl c
  retainedCandidate : ∀ n c, image n = .inl c → n ∈ nextHeap.keys →
    candidates n c ∨ fixed n = some c
  retainedShape : ∀ n c nn, image n = .inl c → nextHeap.lookup n = some nn →
    ∃ cn, curHeap.lookup c = some cn ∧ compatibleShape curHeap nextHeap cn nn = true
  /-- An existing view cannot change which buffer it references. -/
  retainedBuffer : ∀ n c nn cn nb cb,
    image n = .inl c → nextHeap.lookup n = some nn → curHeap.lookup c = some cn →
    (match nn with | .dataView b .. | .typedArray _ b .. => some b | _ => none) = some nb →
    (match cn with | .dataView b .. | .typedArray _ b .. => some b | _ => none) = some cb →
    image nb = .inl cb

/-- Successful output: one witness is tied to the root and every observed payload.
    `SurfaceEq`, cycles, and no-collapse are conclusions, not fields. -/
structure ReconcileSpec {A : Type} (curHeap : Heap A CurId) (nextHeap : Heap A NextId)
    (resultHeap : Heap A ResId) (curRoot : Value A CurId) (nextRoot : Value A NextId)
    (resultRoot : Value A ResId) where
  witness : ReconcileWitness curHeap nextHeap
  nextWF : HeapWF nextHeap
  nextRootWF : RootWF nextHeap nextRoot
  rootSpec : execReconcileRoot curHeap nextHeap curRoot nextRoot = .ok resultRoot
  rootImage : nextRoot.remap witness.image = resultRoot
  published : Published nextHeap resultHeap witness.image (publicationProto curHeap witness.image)

/-- Runtime failure is allowed after partial writes. Only success is certified.
    This relation does not imply all feasible requests eventually succeed. -/
inductive ReconcileOutcome {A : Type} (curHeap : Heap A CurId) (nextHeap : Heap A NextId)
    (curRoot : Value A CurId) (nextRoot : Value A NextId) :
    Heap A ResId → Except PublicationFailure (Value A ResId) → Prop where
  | success {heap root} : ReconcileSpec curHeap nextHeap heap curRoot nextRoot root →
      ReconcileOutcome curHeap nextHeap curRoot nextRoot heap (.ok root)
  | failure (heap) (reason) : ReconcileOutcome curHeap nextHeap curRoot nextRoot heap (.error reason)

/-- Construct a success certificate from the pure publication algorithm. -/
def reconcileFromRecords {A : Type} (curHeap : Heap A CurId) (nextHeap : Heap A NextId)
    (before : Heap A ResId) (curRoot : Value A CurId) (nextRoot : Value A NextId)
    (resultRoot : Value A ResId) (w : ReconcileWitness curHeap nextHeap)
    (hw : HeapWF nextHeap) (hr : RootWF nextHeap nextRoot)
    (hroot : execReconcileRoot curHeap nextHeap curRoot nextRoot = .ok resultRoot)
    (himage : nextRoot.remap w.image = resultRoot)
    (records : List (NextId × Node A NextId))
    (covers : ∀ i nd, nextHeap.lookup i = some nd → (i, nd) ∈ records)
    (unique : records.Pairwise (fun a b => w.image a.1 ≠ w.image b.1)) :
    ReconcileSpec curHeap nextHeap
      (publishRecords w.image (publicationProto curHeap w.image) records before)
      curRoot nextRoot resultRoot where
  witness := w
  nextWF := hw
  nextRootWF := hr
  rootSpec := hroot
  rootImage := himage
  published := publishRecords_published nextHeap w.image _ records before covers unique

/-- Executable ownership check over the finite captured record list. Labels
    must distinguish writable storage; this does not discover hidden aliases. -/
def checkOwnership {A : Type} (records : List (NextId × Node A NextId))
    (image : NextId → ResId) (storage : ResId → Nat) : Bool :=
  decide (records.Pairwise (fun a b => storage (image a.1) ≠ storage (image b.1)))

/-- Accepted ownership supplies the identity separation needed by publication. -/
theorem checkOwnership_images {A : Type} (records : List (NextId × Node A NextId))
    (image : NextId → ResId) (storage : ResId → Nat)
    (h : checkOwnership records image storage = true) :
    records.Pairwise (fun a b => image a.1 ≠ image b.1) := by
  have hpair : records.Pairwise (fun a b => storage (image a.1) ≠ storage (image b.1)) :=
    of_decide_eq_true h
  exact hpair.imp (fun hne he => hne (congrArg storage he))

end Reconcile
