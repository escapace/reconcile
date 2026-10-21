import Reconcile.ReconcileSoundness

/-! Identical-occupant pruning. A captured next heap is surrounded by pinned boundary nodes:
current objects found at the same position of the aligned current node. Pinned nodes carry no
captured payload and receive no writes. The unconditional contract is stated over the captured
heap; `FullCapture` states when the pruned publication coincides with publishing the hypothetical
full next heap. -/

namespace Reconcile

variable {A : Type}

/-- The buffer a view depends on, if the node is a view. -/
def viewBuffer {ι : Type} : Node A ι → Option ι
  | .dataView b .. => some b
  | .typedArray _ b .. => some b
  | _ => none

theorem viewBuffer_eq {ι : Type} (nd : Node A ι) :
    viewBuffer nd = (match nd with | .dataView b .. | .typedArray _ b .. => some b | _ => none) := by
  cases nd <;> rfl

theorem viewBuffer_mem {ι : Type} {nd : Node A ι} {b : ι} (h : viewBuffer nd = some b) :
    b ∈ nd.childRefs := by
  cases nd <;> simp only [viewBuffer, Option.some.injEq, reduceCtorEq] at h
  all_goals subst h; simp [Node.childRefs]

/-- Captured nodes may reference pinned boundary nodes, which have no captured payload. -/
def PrunedHeapWF (capHeap : Heap A NextId) (pinned : NextId → Option CurId) : Prop :=
  ∀ id ∈ capHeap.keys, ∀ node, capHeap.lookup id = some node →
    ∀ r ∈ node.childRefs, r ∈ capHeap.keys ∨ (pinned r).isSome

/-- A reconcile witness over the captured heap, extended by the pinned boundary. A pinned
    node is a domain with one retained choice, so `fixed` already expresses its image. -/
structure PrunedWitness (curHeap : Heap A CurId) (capHeap : Heap A NextId)
    extends ReconcileWitness curHeap capHeap where
  pinned : NextId → Option CurId
  /-- Boundary nodes are outside the captured heap. -/
  pinnedOutside : ∀ b c, pinned b = some c → b ∉ capHeap.keys
  pinnedImage : ∀ b c, pinned b = some c → image b = .inl c
  /-- A pinned occupant's storage is claimed; no captured node may select it. -/
  pinnedUnclaimed : ∀ n ∈ capHeap.keys, ∀ b c, pinned b = some c →
    storage (image n) ≠ storage (.inl c)
  /-- Captured views keep their buffers captured, so buffer extents are observed. -/
  capturedBuffers : ∀ n nn, capHeap.lookup n = some nn → ∀ nb,
    viewBuffer nn = some nb → nb ∈ capHeap.keys

/-- Successful pruned output. The root is never pinned. -/
structure PrunedReconcileSpec (curHeap : Heap A CurId) (capHeap : Heap A NextId)
    (resultHeap : Heap A ResId) (curRoot : Value A CurId) (nextRoot : Value A NextId)
    (resultRoot : Value A ResId) where
  witness : PrunedWitness curHeap capHeap
  capWF : PrunedHeapWF capHeap witness.pinned
  rootWF : RootWF capHeap nextRoot
  rootSpec : execReconcileRoot curHeap capHeap curRoot nextRoot = .ok resultRoot
  rootImage : nextRoot.remap witness.image = resultRoot
  published : Published capHeap resultHeap witness.image (publicationProto curHeap witness.image)

section Unconditional

variable {curHeap : Heap A CurId} {capHeap : Heap A NextId} {resultHeap : Heap A ResId}
  {curRoot : Value A CurId} {nextRoot : Value A NextId} {resultRoot : Value A ResId}

/-- Object/object success returns the existing root (retains `reconcile_root_retained`). -/
theorem pruned_root_retained {cr nr}
    (h : execReconcileRoot curHeap capHeap (.ref cr) (.ref nr) = .ok resultRoot) :
    resultRoot = .ref (.inl cr) := reconcile_root_retained h

/-- Publication writes nothing at a pinned occupant: its payload is the current payload. -/
theorem pruned_untouched (w : PrunedWitness curHeap capHeap)
    (records : List (NextId × Node A NextId)) (before : Heap A ResId)
    (keys : ∀ e ∈ records, e.1 ∈ capHeap.keys) {b c} (hb : w.pinned b = some c) :
    (publishRecords w.image (publicationProto curHeap w.image) records before).lookup (.inl c) =
      before.lookup (.inl c) :=
  publishRecords_frame _ _ records before _ fun e he hi =>
    w.pinnedUnclaimed e.1 (keys e he) b c hb (congrArg w.storage hi)

/-- Distinct captured nodes keep distinct images. -/
theorem pruned_no_collapse (w : PrunedWitness curHeap capHeap)
    {n₁ n₂} (h₁ : n₁ ∈ capHeap.keys) (h₂ : n₂ ∈ capHeap.keys) (hne : n₁ ≠ n₂) :
    w.image n₁ ≠ w.image n₂ := reconcile_no_collapse w.toReconcileWitness h₁ h₂ hne

/-- A captured node and a pinned occupant never share an image. -/
theorem pruned_separate (w : PrunedWitness curHeap capHeap)
    {n b c} (hn : n ∈ capHeap.keys) (hb : w.pinned b = some c) : w.image n ≠ .inl c :=
  fun h => w.pinnedUnclaimed n hn b c hb (congrArg w.storage h)

/-- Captured cycles are published as cycles. -/
theorem pruned_cycle_preservation
    (spec : PrunedReconcileSpec curHeap capHeap resultHeap curRoot nextRoot resultRoot) {n}
    (hc : Relation.TransGen (edge capHeap) n n) :
    Relation.TransGen (edge resultHeap) (spec.witness.image n) (spec.witness.image n) :=
  spec.published.path hc

/-- Captured ordered fields are published at the selected identity; edges to pinned
    occupants resolve to those occupants. -/
theorem pruned_object_payload
    (spec : PrunedReconcileSpec curHeap capHeap resultHeap curRoot nextRoot resultRoot)
    {n p fs} (hn : capHeap.lookup n = some (.plainObject p fs)) :
    resultHeap.lookup (spec.witness.image n) =
      some (.plainObject (publicationProto curHeap spec.witness.image n p)
        (remapFields spec.witness.image fs)) := spec.published n _ hn

end Unconditional

section Extents

theorem bufferExtent_remap {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    {src : Heap A ι} {dst : Heap A κ} {f : ι → κ} {proto : ProtoLabel → ProtoLabel} {b : ι}
    (h : dst.lookup (f b) = (src.lookup b).map fun nd => nd.remap f proto) :
    bufferExtent dst (f b) = bufferExtent src b := by
  unfold bufferExtent
  rw [h]
  cases src.lookup b with
  | none => rfl
  | some nd => cases nd <;> simp [Node.remap]

/-- Shape compatibility depends on the next heap only through view buffer extents. -/
theorem compatibleShape_congr {curHeap : Heap A CurId} {h₁ h₂ : Heap A NextId}
    (cn : Node A CurId) (nn : Node A NextId)
    (hb : ∀ b, viewBuffer nn = some b → bufferExtent h₁ b = bufferExtent h₂ b) :
    compatibleShape curHeap h₁ cn nn = compatibleShape curHeap h₂ cn nn := by
  cases nn with
  | dataView nb no nl =>
    have hx := hb nb rfl
    cases cn <;> simp only [compatibleShape, matchingBufferExtents, hx]
  | typedArray nt nb no nl ne =>
    have hx := hb nb rfl
    cases cn <;> simp only [compatibleShape, matchingBufferExtents, hx]
  | plainObject p fs => cases cn <;> rfl
  | array es => cases cn <;> rfl
  | date ms => cases cn <;> rfl
  | map es => cases cn <;> rfl
  | set vs => cases cn <;> rfl
  | arrayBuffer bs => cases cn <;> rfl

/-- A node is shape-compatible with its own embedding when its buffer extent is observed. -/
theorem compatibleShape_remap {curHeap : Heap A CurId} {nextHeap : Heap A NextId}
    (f : NextId → CurId) (nn : Node A NextId)
    (hb : ∀ b, viewBuffer nn = some b →
      bufferExtent curHeap (f b) = bufferExtent nextHeap b ∧ (bufferExtent nextHeap b).isSome) :
    compatibleShape curHeap nextHeap (nn.remap f fun p => p) nn = true := by
  cases nn with
  | dataView nb no nl =>
    obtain ⟨he, hs⟩ := hb nb rfl
    simp only [Node.remap, compatibleShape, matchingBufferExtents, he]
    cases h : bufferExtent nextHeap nb with
    | none => simp [h] at hs
    | some len => simp
  | typedArray nt nb no nl ne =>
    obtain ⟨he, hs⟩ := hb nb rfl
    simp only [Node.remap, compatibleShape, matchingBufferExtents, he]
    cases h : bufferExtent nextHeap nb with
    | none => simp [h] at hs
    | some len => simp
  | plainObject p fs => simp [Node.remap, compatibleShape]
  | array es => simp [Node.remap, compatibleShape]
  | date ms => simp [Node.remap, compatibleShape]
  | map es => simp [Node.remap, compatibleShape]
  | set vs => simp [Node.remap, compatibleShape]
  | arrayBuffer bs => simp [Node.remap, compatibleShape]

end Extents

/-- The hypothetical full capture of a pruned call: the pruned closure of `nextHeap` is
    embedded in the current heap, is closed and separate from the captured nodes, and
    publication writes nothing inside it. These premises are not checked at runtime. -/
structure FullCapture (curHeap : Heap A CurId) (capHeap nextHeap : Heap A NextId)
    (w : PrunedWitness curHeap capHeap) where
  embed : NextId → CurId
  extends_ : ∀ n nd, capHeap.lookup n = some nd → nextHeap.lookup n = some nd
  nextWF : HeapWF nextHeap
  /-- A pinned boundary node is embedded at its occupant. -/
  boundary : ∀ b c, w.pinned b = some c → embed b = c ∧ b ∈ nextHeap.keys
  /-- Pruned nodes carry the payload of their current embedding. -/
  embedded : ∀ p ∈ nextHeap.keys, p ∉ capHeap.keys → ∀ nd, nextHeap.lookup p = some nd →
    curHeap.lookup (embed p) = some (nd.remap embed fun q => q)
  /-- The pruned closure is closed and separate from the captured nodes. -/
  closed : ∀ p ∈ nextHeap.keys, p ∉ capHeap.keys → ∀ nd, nextHeap.lookup p = some nd →
    ∀ r ∈ nd.childRefs, r ∉ capHeap.keys
  /-- Pruned views have observed buffer extents. -/
  prunedViews : ∀ p ∈ nextHeap.keys, p ∉ capHeap.keys → ∀ nd, nextHeap.lookup p = some nd →
    ∀ b, viewBuffer nd = some b → (bufferExtent nextHeap b).isSome
  /-- Publication writes nothing in the pruned closure. -/
  writtenDisjoint : ∀ n ∈ capHeap.keys, ∀ p ∈ nextHeap.keys, p ∉ capHeap.keys →
    w.storage (w.image n) ≠ w.storage (.inl (embed p))
  /-- Distinct pruned nodes have distinct storage. -/
  embedStorage : ∀ p₁ ∈ nextHeap.keys, p₁ ∉ capHeap.keys →
    ∀ p₂ ∈ nextHeap.keys, p₂ ∉ capHeap.keys →
    w.storage (.inl (embed p₁)) = w.storage (.inl (embed p₂)) → p₁ = p₂

namespace FullCapture

variable {curHeap : Heap A CurId} {capHeap nextHeap : Heap A NextId}
  {w : PrunedWitness curHeap capHeap}

/-- The full image: captured nodes keep their selected image, pruned nodes embed. -/
def image (f : FullCapture curHeap capHeap nextHeap w) (n : NextId) : ResId :=
  if n ∈ capHeap.keys then w.image n else .inl (f.embed n)

theorem image_captured (f : FullCapture curHeap capHeap nextHeap w) {n : NextId}
    (h : n ∈ capHeap.keys) : f.image n = w.image n := by simp [image, h]

theorem image_pruned (f : FullCapture curHeap capHeap nextHeap w) {n : NextId}
    (h : n ∉ capHeap.keys) : f.image n = .inl (f.embed n) := by simp [image, h]

theorem image_pinned (f : FullCapture curHeap capHeap nextHeap w) {b : NextId} {c : CurId}
    (hb : w.pinned b = some c) : f.image b = w.image b := by
  rw [f.image_pruned (w.pinnedOutside b c hb), w.pinnedImage b c hb, (f.boundary b c hb).1]

theorem image_child (f : FullCapture curHeap capHeap nextHeap w)
    (hwf : PrunedHeapWF capHeap w.pinned) {n : NextId} {nd : Node A NextId}
    (hn : capHeap.lookup n = some nd) {r : NextId} (hr : r ∈ nd.childRefs) :
    f.image r = w.image r := by
  rcases hwf n (Finmap.mem_keys.mpr (Finmap.mem_of_lookup_eq_some hn)) nd hn r hr with h | h
  · exact f.image_captured h
  · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
    exact f.image_pinned hc

theorem lookup_captured (f : FullCapture curHeap capHeap nextHeap w) {n : NextId}
    {nd : Node A NextId} (hn : n ∈ capHeap.keys) (h : nextHeap.lookup n = some nd) :
    capHeap.lookup n = some nd := by
  obtain ⟨nd', hd'⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp hn)
  have he := f.extends_ n nd' hd'
  rw [h, Option.some.injEq] at he
  subst he
  exact hd'

theorem extent_captured (f : FullCapture curHeap capHeap nextHeap w) {b : NextId}
    (hb : b ∈ capHeap.keys) : bufferExtent capHeap b = bufferExtent nextHeap b := by
  obtain ⟨nb, hnb⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp hb)
  simp only [bufferExtent, hnb, f.extends_ b nb hnb]

theorem extent_pruned (f : FullCapture curHeap capHeap nextHeap w) {b : NextId}
    (hb : b ∈ nextHeap.keys) (hc : b ∉ capHeap.keys) :
    bufferExtent curHeap (f.embed b) = bufferExtent nextHeap b := by
  apply bufferExtent_remap (proto := fun p => p)
  cases hnb : nextHeap.lookup b with
  | none => exact absurd (Finmap.mem_keys.mp hb) (Finmap.lookup_eq_none.mp hnb)
  | some nb => simpa using f.embedded b hb hc nb hnb

/-- The reconcile witness of the full next heap induced by a pruned witness. -/
def witness (f : FullCapture curHeap capHeap nextHeap w) : ReconcileWitness curHeap nextHeap where
  image := f.image
  storage := w.storage
  candidates := w.candidates
  fixed n := if n ∈ capHeap.keys then w.fixed n else some (f.embed n)
  storageDistinct := by
    intro n₁ h₁ n₂ h₂ he
    by_cases c₁ : n₁ ∈ capHeap.keys <;> by_cases c₂ : n₂ ∈ capHeap.keys
    · rw [f.image_captured c₁, f.image_captured c₂] at he
      exact w.storageDistinct n₁ c₁ n₂ c₂ he
    · rw [f.image_captured c₁, f.image_pruned c₂] at he
      exact absurd he (f.writtenDisjoint n₁ c₁ n₂ h₂ c₂)
    · rw [f.image_pruned c₁, f.image_captured c₂] at he
      exact absurd he.symm (f.writtenDisjoint n₂ c₂ n₁ h₁ c₁)
    · rw [f.image_pruned c₁, f.image_pruned c₂] at he
      exact f.embedStorage n₁ h₁ c₁ n₂ h₂ c₂ he
  fixedImage := by
    intro n c h
    by_cases hc : n ∈ capHeap.keys
    · simp only [hc, if_true] at h
      rw [f.image_captured hc]
      exact w.fixedImage n c h
    · simp only [hc, if_false, Option.some.injEq] at h
      rw [f.image_pruned hc, h]
  retainedCandidate := by
    intro n c hi hn
    by_cases hc : n ∈ capHeap.keys
    · rw [f.image_captured hc] at hi
      simp only [hc, if_true]
      exact w.retainedCandidate n c hi hc
    · rw [f.image_pruned hc] at hi
      simp only [hc, if_false]
      exact Or.inr (congrArg some (Sum.inl.inj hi))
  retainedShape := by
    intro n c nn hi hn
    by_cases hc : n ∈ capHeap.keys
    · rw [f.image_captured hc] at hi
      have hcap := f.lookup_captured hc hn
      obtain ⟨cn, hcn, hshape⟩ := w.retainedShape n c nn hi hcap
      refine ⟨cn, hcn, ?_⟩
      rw [← compatibleShape_congr cn nn fun b hb => f.extent_captured (w.capturedBuffers n nn hcap b hb)]
      exact hshape
    · rw [f.image_pruned hc] at hi
      obtain rfl := Sum.inl.inj hi
      have hp : n ∈ nextHeap.keys := Finmap.mem_keys.mpr (Finmap.mem_of_lookup_eq_some hn)
      refine ⟨nn.remap f.embed fun p => p, f.embedded n hp hc nn hn, ?_⟩
      apply compatibleShape_remap
      intro b hb
      have hbn : b ∈ nextHeap.keys := f.nextWF n hp nn hn b (viewBuffer_mem hb)
      have hbc : b ∉ capHeap.keys := f.closed n hp hc nn hn b (viewBuffer_mem hb)
      exact ⟨f.extent_pruned hbn hbc, f.prunedViews n hp hc nn hn b hb⟩
  retainedBuffer := by
    intro n c nn cn nb cb hi hn hc hnb hcb
    have hnb' : viewBuffer nn = some nb := by cases nn <;> exact hnb
    have hcb' : viewBuffer cn = some cb := by cases cn <;> exact hcb
    by_cases hcap : n ∈ capHeap.keys
    · rw [f.image_captured hcap] at hi
      have hcapn := f.lookup_captured hcap hn
      rw [f.image_captured (w.capturedBuffers n nn hcapn nb hnb')]
      exact w.retainedBuffer n c nn cn nb cb hi hcapn hc hnb hcb
    · rw [f.image_pruned hcap] at hi
      obtain rfl := Sum.inl.inj hi
      have hp : n ∈ nextHeap.keys := Finmap.mem_keys.mpr (Finmap.mem_of_lookup_eq_some hn)
      have hemb := f.embedded n hp hcap nn hn
      rw [hc, Option.some.injEq] at hemb
      subst hemb
      have hbc : nb ∉ capHeap.keys := f.closed n hp hcap nn hn nb (viewBuffer_mem hnb')
      rw [f.image_pruned hbc]
      congr 1
      cases nn <;> simp only [viewBuffer, Node.remap, Option.some.injEq, reduceCtorEq] at hnb' hcb'
      all_goals subst hnb'; exact hcb'

end FullCapture

section Equivalence

variable {curHeap : Heap A CurId} {capHeap nextHeap : Heap A NextId} {resultHeap : Heap A ResId}
  {curRoot : Value A CurId} {nextRoot : Value A NextId} {resultRoot : Value A ResId}

/-- Under the full-capture premises, the pruned publication is a publication of the
    full next heap: exactly the result full capture would certify. -/
def pruned_full_equivalence
    (spec : PrunedReconcileSpec curHeap capHeap resultHeap curRoot nextRoot resultRoot)
    (f : FullCapture curHeap capHeap nextHeap spec.witness)
    (records : List (NextId × Node A NextId)) (before : Heap A ResId)
    (hres : resultHeap = publishRecords spec.witness.image
      (publicationProto curHeap spec.witness.image) records before)
    (keys : ∀ e ∈ records, e.1 ∈ capHeap.keys)
    (beforeCur : ∀ c, before.lookup (.inl c) =
      (curHeap.lookup c).map fun nd => nd.remap Sum.inl fun p => p) :
    ReconcileSpec curHeap nextHeap resultHeap curRoot nextRoot resultRoot where
  witness := f.witness
  nextWF := f.nextWF
  nextRootWF := by
    cases nextRoot with
    | atom => trivial
    | ref r =>
      have hw : r ∈ capHeap.keys := spec.rootWF
      obtain ⟨nd, hd⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp hw)
      exact Finmap.mem_keys.mpr (Finmap.mem_of_lookup_eq_some (f.extends_ r nd hd))
  rootSpec := by
    have h := spec.rootSpec
    cases curRoot with
    | atom a => exact h
    | ref cr =>
      cases nextRoot with
      | atom a => exact h
      | ref nr =>
        simp only [execReconcileRoot] at h ⊢
        rcases hcur : curHeap.lookup cr with _ | cn
        · simp [hcur] at h
        · rcases hcap : capHeap.lookup nr with _ | nn
          · simp [hcur, hcap] at h
          · rw [f.extends_ nr nn hcap]
            simp only [hcur, hcap] at h ⊢
            rw [← compatibleShape_congr cn nn fun b hb =>
              f.extent_captured (spec.witness.capturedBuffers nr nn hcap b hb)]
            exact h
  rootImage := by
    have h := spec.rootImage
    cases nextRoot with
    | atom a => exact h
    | ref r =>
      have hw : r ∈ capHeap.keys := spec.rootWF
      calc Value.remap f.image (.ref r) = Value.remap spec.witness.image (.ref r) := by
            simp only [Value.remap, f.image_captured hw]
        _ = resultRoot := h
  published := by
    intro n nd hn
    change resultHeap.lookup (f.image n) = some (nd.remap f.image (publicationProto curHeap f.image n))
    by_cases hc : n ∈ capHeap.keys
    · have hcap := f.lookup_captured hc hn
      have hproto : publicationProto curHeap f.image n =
          publicationProto curHeap spec.witness.image n := by
        funext p
        simp only [publicationProto, f.image_captured hc]
      rw [f.image_captured hc, spec.published n nd hcap, hproto]
      exact congrArg some (Node.remap_congr nd _ _ _ fun r hr =>
        (f.image_child spec.capWF hcap hr).symm)
    · have hp : n ∈ nextHeap.keys := Finmap.mem_keys.mpr (Finmap.mem_of_lookup_eq_some hn)
      have hframe : resultHeap.lookup (.inl (f.embed n)) = before.lookup (.inl (f.embed n)) :=
        (congrArg (fun heap : Heap A ResId => heap.lookup (.inl (f.embed n))) hres).trans
          (publishRecords_frame _ _ records before _ fun e he hi =>
            f.writtenDisjoint e.1 (keys e he) n hp hc (congrArg spec.witness.storage hi))
      rw [f.image_pruned hc, hframe, beforeCur, f.embedded n hp hc nd hn, Option.map_some,
        Node.remap_comp]
      congr 1
      have hchild : ∀ r ∈ nd.childRefs, (Sum.inl ∘ f.embed) r = f.image r := fun r hr =>
        (f.image_pruned (f.closed n hp hc nd hn r hr)).symm
      rw [Node.remap_congr nd _ _ _ hchild]
      cases nd with
      | plainObject q fs =>
        simp [Node.remap, publicationProto, f.image_pruned hc, f.embedded n hp hc _ hn]
      | array es => rfl
      | date ms => rfl
      | map es => rfl
      | set vs => rfl
      | arrayBuffer bs => rfl
      | dataView b o l => rfl
      | typedArray t b o l es => rfl

/-- Soundness of the pruned result against the full next heap, under the same premises. -/
theorem pruned_full_soundness [AtomEq A]
    (spec : PrunedReconcileSpec curHeap capHeap resultHeap curRoot nextRoot resultRoot)
    (f : FullCapture curHeap capHeap nextHeap spec.witness)
    (records : List (NextId × Node A NextId)) (before : Heap A ResId)
    (hres : resultHeap = publishRecords spec.witness.image
      (publicationProto curHeap spec.witness.image) records before)
    (keys : ∀ e ∈ records, e.1 ∈ capHeap.keys)
    (beforeCur : ∀ c, before.lookup (.inl c) =
      (curHeap.lookup c).map fun nd => nd.remap Sum.inl fun p => p) :
    SurfaceEq nextHeap resultHeap nextRoot resultRoot :=
  reconcile_soundness (pruned_full_equivalence spec f records before hres keys beforeCur)

end Equivalence

end Reconcile
