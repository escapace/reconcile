/-
  Patch draft layer — compact implementation-facing finalization coherence.

  This module is the permanent Lean boundary for the extra finalization facts
  the TypeScript `patch` implementation needs. It intentionally stays small.

  It adds only:

  - grounded supported-surface final-path lookup and absence in the finalized
    next graph,
  - one compact proof-facing witness for repeated-ref / moved-ref /
    collection-captured finalization coherence,
  - one compact wrapper sitting on top of `DraftExecSpec`.

  Scope discipline:

  - This is not a proxy-trap model.
  - This is not callback semantics.
  - This is not an operation-record calculus.
  - This is not an executable finalization algorithm.

  Its purpose is to constrain what the implementation must make true about the
  finalized next graph before calling `reconcile(current, next)`.
-/

import PatchDraftSpec

namespace Reconcile

/-- Proof-friendly list lookup by ordinal position. -/
def listNth? {α : Type} (xs : List α) (i : Nat) : Option α :=
  (List.drop i xs).head?

/-- Supported-surface interpretation of a final draft path in the finalized next
    graph. The relation is rooted at a specific next value and follows the
    supported path forms only: object keys, array indices, map entry positions,
    and set entry positions. For maps, `mapEntry i` denotes the value component
    of the `i`th entry. -/
inductive FinalPathValueSpec {A : Type}
    (nextHeap : Heap A NextId) :
    Value A NextId → DraftPath → Value A NextId → Prop where
  | here {v : Value A NextId} :
      FinalPathValueSpec nextHeap v [] v
  | objectKey {r : NextId} {proto : ProtoLabel} {fields : ObjFields A NextId}
      {k : PropertyKey} {child v : Value A NextId} {rest : DraftPath} :
      nextHeap.lookup r = some (.plainObject proto fields) →
      List.dlookup k fields = some child →
      FinalPathValueSpec nextHeap child rest v →
      FinalPathValueSpec nextHeap (.ref r) (DraftPathElem.objectKey k :: rest) v
  | arrayIndex {r : NextId} {entries : List (Option (Value A NextId))}
      {i : Nat} {child v : Value A NextId} {rest : DraftPath} :
      nextHeap.lookup r = some (.array entries) →
      listNth? entries i = some (some child) →
      FinalPathValueSpec nextHeap child rest v →
      FinalPathValueSpec nextHeap (.ref r) (DraftPathElem.arrayIndex i :: rest) v
  | mapEntry {r : NextId} {entries : List (Value A NextId × Value A NextId)}
      {i : Nat} {key child v : Value A NextId} {rest : DraftPath} :
      nextHeap.lookup r = some (.map entries) →
      listNth? entries i = some (key, child) →
      FinalPathValueSpec nextHeap child rest v →
      FinalPathValueSpec nextHeap (.ref r) (DraftPathElem.mapEntry i :: rest) v
  | setEntry {r : NextId} {values : List (Value A NextId)}
      {i : Nat} {child v : Value A NextId} {rest : DraftPath} :
      nextHeap.lookup r = some (.set values) →
      listNth? values i = some child →
      FinalPathValueSpec nextHeap child rest v →
      FinalPathValueSpec nextHeap (.ref r) (DraftPathElem.setEntry i :: rest) v

/-- Supported-surface absence relation for final draft paths in the finalized
    next graph. Absence is intentionally modest: it captures the cases needed
    for object-key deletion, array holes / out-of-range access, missing map
    entry positions, and missing set entry positions. -/
inductive FinalPathAbsentSpec {A : Type}
    (nextHeap : Heap A NextId) :
    Value A NextId → DraftPath → Prop where
  | objectKeyMissing {r : NextId} {proto : ProtoLabel} {fields : ObjFields A NextId}
      {k : PropertyKey} {rest : DraftPath} :
      nextHeap.lookup r = some (.plainObject proto fields) →
      List.dlookup k fields = none →
      FinalPathAbsentSpec nextHeap (.ref r) (DraftPathElem.objectKey k :: rest)
  | objectKeyDeep {r : NextId} {proto : ProtoLabel} {fields : ObjFields A NextId}
      {k : PropertyKey} {child : Value A NextId} {rest : DraftPath} :
      nextHeap.lookup r = some (.plainObject proto fields) →
      List.dlookup k fields = some child →
      FinalPathAbsentSpec nextHeap child rest →
      FinalPathAbsentSpec nextHeap (.ref r) (DraftPathElem.objectKey k :: rest)
  | arrayIndexMissing {r : NextId} {entries : List (Option (Value A NextId))}
      {i : Nat} {rest : DraftPath} :
      nextHeap.lookup r = some (.array entries) →
      listNth? entries i = none →
      FinalPathAbsentSpec nextHeap (.ref r) (DraftPathElem.arrayIndex i :: rest)
  | arrayIndexHole {r : NextId} {entries : List (Option (Value A NextId))}
      {i : Nat} {rest : DraftPath} :
      nextHeap.lookup r = some (.array entries) →
      listNth? entries i = some none →
      FinalPathAbsentSpec nextHeap (.ref r) (DraftPathElem.arrayIndex i :: rest)
  | arrayIndexDeep {r : NextId} {entries : List (Option (Value A NextId))}
      {i : Nat} {child : Value A NextId} {rest : DraftPath} :
      nextHeap.lookup r = some (.array entries) →
      listNth? entries i = some (some child) →
      FinalPathAbsentSpec nextHeap child rest →
      FinalPathAbsentSpec nextHeap (.ref r) (DraftPathElem.arrayIndex i :: rest)
  | mapEntryMissing {r : NextId} {entries : List (Value A NextId × Value A NextId)}
      {i : Nat} {rest : DraftPath} :
      nextHeap.lookup r = some (.map entries) →
      listNth? entries i = none →
      FinalPathAbsentSpec nextHeap (.ref r) (DraftPathElem.mapEntry i :: rest)
  | mapEntryDeep {r : NextId} {entries : List (Value A NextId × Value A NextId)}
      {i : Nat} {key child : Value A NextId} {rest : DraftPath} :
      nextHeap.lookup r = some (.map entries) →
      listNth? entries i = some (key, child) →
      FinalPathAbsentSpec nextHeap child rest →
      FinalPathAbsentSpec nextHeap (.ref r) (DraftPathElem.mapEntry i :: rest)
  | setEntryMissing {r : NextId} {values : List (Value A NextId)}
      {i : Nat} {rest : DraftPath} :
      nextHeap.lookup r = some (.set values) →
      listNth? values i = none →
      FinalPathAbsentSpec nextHeap (.ref r) (DraftPathElem.setEntry i :: rest)
  | setEntryDeep {r : NextId} {values : List (Value A NextId)}
      {i : Nat} {child : Value A NextId} {rest : DraftPath} :
      nextHeap.lookup r = some (.set values) →
      listNth? values i = some child →
      FinalPathAbsentSpec nextHeap child rest →
      FinalPathAbsentSpec nextHeap (.ref r) (DraftPathElem.setEntry i :: rest)

/-- Minimal proof-facing witness for the extra finalization cases the
    implementation must resolve before publication.

    This witness is intentionally compact and implementation-neutral. It is the
    permanent semantic boundary for finalization coherence, not proof-search
    scaffolding. -/
structure FinalizationResolutionWitness {A : Type}
    (nextHeap : Heap A NextId) (nextRoot : Value A NextId)
    (sharedOriginAt : DraftPath → DraftPath → Prop)
    (movedOriginTo : DraftPath → DraftPath → Prop)
    (capturedDraftValueAt : DraftPath → Prop) where
  /-- Shared-image coherence over grounded final-path lookup. -/
  sharedImage : ∀ p₁ p₂,
      sharedOriginAt p₁ p₂ →
      ∃ v, FinalPathValueSpec nextHeap nextRoot p₁ v ∧
        FinalPathValueSpec nextHeap nextRoot p₂ v
  /-- Move coherence over grounded final-path lookup/absence. -/
  movedImage : ∀ pOld pNew,
      movedOriginTo pOld pNew →
      FinalPathAbsentSpec nextHeap nextRoot pOld ∧
      ∃ v, FinalPathValueSpec nextHeap nextRoot pNew v
  /-- Collection-captured-draft finalization over grounded final-path lookup. -/
  capturedImage : ∀ p,
      capturedDraftValueAt p →
      ∃ v, FinalPathValueSpec nextHeap nextRoot p v

/-- Compact proof-facing coherence layer above `DraftExecSpec`.

    The central patch factorization remains unchanged. This wrapper exists only
    so Lean can state the extra finalized-next obligations that matter for the
    implementation:

    - shared final-image coherence,
    - moved-reference final placement,
    - collection-captured draft-value finalization.

    Final value/absence claims are grounded in the finalized next graph, and
    the extra coherence obligations are bundled into one subordinate witness. -/
structure FinalizeCoherenceSpec {A : Type} [AtomEq A]
    (curHeap : Heap A CurId) (curRoot : Value A CurId)
    (nextHeap : Heap A NextId) (nextRoot : Value A NextId) where
  /-- Base draft-finalization contract. -/
  draftSpec : DraftExecSpec curHeap curRoot nextHeap nextRoot
  /-- `sharedOriginAt p₁ p₂` means the two final paths denote the same
      draft-originating value. -/
  sharedOriginAt : DraftPath → DraftPath → Prop
  /-- `movedOriginTo pOld pNew` means a draft-originating value that was
      associated with `pOld` is present instead at final path `pNew`. -/
  movedOriginTo : DraftPath → DraftPath → Prop
  /-- `capturedDraftValueAt p` means the final collection position denoted by
      `p` contains a draft-originating value at recipe end and therefore needs
      finalization to resolve it into the next graph. -/
  capturedDraftValueAt : DraftPath → Prop
  /-- Bundled witness for finalization resolution of the extra coherence cases.
      This remains proof-facing and abstract, but it narrows the semantic gap:
      the exported coherence theorems now derive from one witness layer rather
      than projecting three unrelated wrapper fields directly. -/
  resolutionWitness : FinalizationResolutionWitness nextHeap nextRoot
    sharedOriginAt movedOriginTo capturedDraftValueAt

abbrev FinalizeCoherenceSpec.finalValueAt {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {curRoot : Value A CurId}
    {nextHeap : Heap A NextId} {nextRoot : Value A NextId}
    (_spec : FinalizeCoherenceSpec curHeap curRoot nextHeap nextRoot) :
    DraftPath → Value A NextId → Prop :=
  FinalPathValueSpec (A := A) nextHeap nextRoot

abbrev FinalizeCoherenceSpec.finalValueAbsentAt {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {curRoot : Value A CurId}
    {nextHeap : Heap A NextId} {nextRoot : Value A NextId}
    (_spec : FinalizeCoherenceSpec curHeap curRoot nextHeap nextRoot) :
    DraftPath → Prop :=
  FinalPathAbsentSpec (A := A) nextHeap nextRoot

end Reconcile
