import Types.OwnedNativeChildEncoding
import Types.NativeValueEncoding
import Snapshot.SnapshotSpec
import Reconcile.ReconcileSoundness
import Heap.ReuseClosure
import RecipePublication.RecipePublicationSoundness
import Produce.ProduceFinalizeCoherenceSoundness

/-! Examples and counterexamples for the specifications, checked by the kernel rather than only
by executable assertions. Examples show that a specification's premises can hold; counterexamples
show why a premise is needed. -/

namespace Reconcile.ContractTest

instance : AtomEq Nat where
  eq := Eq
  eq_dec := inferInstance
  eq_refl _ := rfl

abbrev currentNode : Node Nat CurId := .plainObject ⟨7⟩ [⟨⟨0⟩, .ref ⟨0⟩⟩]
abbrev nextNode : Node Nat NextId := .plainObject ⟨9⟩ [⟨⟨0⟩, .ref ⟨0⟩⟩]
abbrev current : Heap Nat CurId := Finmap.singleton ⟨0⟩ currentNode
abbrev next : Heap Nat NextId := Finmap.singleton ⟨0⟩ nextNode

def selfWitness : ReconcileWitness current next where
  image n := .inl ⟨n.val⟩
  storage := Sum.elim CurId.val FreshId.val
  candidates _ _ := False
  fixed n := some ⟨n.val⟩
  storageDistinct := by intro a ha b hb he; cases a; cases b; simpa using he
  fixedImage := by intro n c h; cases h; rfl
  retainedCandidate := by intro n c h hn; cases h; exact Or.inr rfl
  retainedShape := by
    intro n c nn hi hn
    have hn0 : n = ⟨0⟩ := by
      have := Finmap.mem_of_lookup_eq_some hn
      simpa using this
    subst n
    cases hi
    simp only [Finmap.lookup_singleton_eq, Option.some.injEq] at hn
    subst nn
    exact ⟨currentNode, by simp, by decide⟩
  retainedBuffer := by
    intro n c nn cn nb cb hi hn hc hnb hcb
    have hn0 : n = ⟨0⟩ := by
      have := Finmap.mem_of_lookup_eq_some hn
      simpa using this
    subst n
    simp only [Finmap.lookup_singleton_eq, Option.some.injEq] at hn
    subst nn
    cases hnb

/-- This retained-root specification is inhabited, including a self-cycle and a
    different next-side prototype. -/
def selfSuccess : ReconcileSpec current next
    (publishRecords selfWitness.image (publicationProto current selfWitness.image)
      [(⟨0⟩, nextNode)] ∅)
    (.ref ⟨0⟩) (.ref ⟨0⟩) (.ref (.inl ⟨0⟩)) :=
  reconcileFromRecords current next ∅ (.ref ⟨0⟩) (.ref ⟨0⟩) (.ref (.inl ⟨0⟩))
    selfWitness
    (by
      intro i hi nd hn
      have he : i = ⟨0⟩ := by simpa using hi
      subst i
      simp only [Finmap.lookup_singleton_eq, Option.some.injEq] at hn
      subst nd
      intro r hr
      simpa [Node.childRefs] using hr)
    (by simp [RootWF])
    (by simp [execReconcileRoot, compatibleShape])
    rfl
    [(⟨0⟩, nextNode)]
    (by
      intro i nd hn
      have he : i = ⟨0⟩ := by
        have := Finmap.mem_of_lookup_eq_some hn
        simpa using this
      subst i
      simp only [Finmap.lookup_singleton_eq, Option.some.injEq] at hn
      subst nd
      simp)
    (by simp)

/-- An inhabited explicit replacement execution. Root observations are admitted;
    container effects and the current/next relation remain conditional, not proxy semantics. -/
def replacementTouches : DraftTouchWitness Nat where
  accessed p := p = []
  childDraftAt p := p = []
  pureReadAt p := p = []
  pathNode p c := p = [] ∧ c = ⟨0⟩
  unchangedRegion _ := False
  unchangedPath _ := False
  modifiedNode _ := False
  copiedNode _ := False
  parentOf _ _ := False
  deletedPathAt _ := False
  assignedUndefinedAt _ := False
  arrayLengthAt _ := none
  arrayOpsAt _ := []

def replacementDraft : DraftExecSpec current (.ref ⟨0⟩) next (.ref ⟨0⟩) where
  returnMode := .replaced (.ref ⟨0⟩)
  touches := replacementTouches
  finalizeWitness := ⟨Finmap.singleton ⟨0⟩ ⟨0⟩⟩
  nextHeapWF := selfSuccess.nextWF
  nextRootWF := selfSuccess.nextRootWF
  returnModeSpec := rfl
  lazyChildDrafts := by intro p h; exact h
  readOnly := True
  readNonInterference := by intro p c _ _ _; exact ⟨id, id⟩
  copyOnWrite := by intro c; rfl
  parentPropagation := by intro c p h; cases h
  deleteNotUndefinedAssign := by intro p h; cases h
  undefinedAssignNotDelete := by intro p h; cases h
  untouchedPreserved := by intro c n _ h; cases h
  objectEffects := by
    intro p c n pCur pNext curFields nextFields _ _ _ _
    exact {
      deletedKeyAbsent := by intro k h; cases h
      untouchedKeyPreserved := by intro k cv _ h; cases h
    }
  arrayEffects := by
    intro p c n curEntries nextEntries hPath _ hCur _
    have hc := hPath.2
    subst c
    simp [current, currentNode] at hCur
  mapEffects := by
    intro p c n curEntries nextEntries hPath _ hCur _
    have hc := hPath.2
    subst c
    simp [current, currentNode] at hCur
  setEffects := by
    intro p c n curValues nextValues hPath _ hCur _
    have hc := hPath.2
    subst c
    simp [current, currentNode] at hCur

/-- Shared and moved origins have actual, nonempty grounded path witnesses. -/
def replacementCoherence : FinalizeCoherenceSpec current (.ref ⟨0⟩) next (.ref ⟨0⟩) where
  draftSpec := replacementDraft
  sharedOriginAt p q := p = [] ∧ q = [.objectKey ⟨0⟩]
  movedOriginTo p q := p = [.objectKey ⟨1⟩] ∧ q = [.objectKey ⟨0⟩]
  capturedDraftValueAt _ := False
  resolutionWitness := {
    sharedImage := by
      intro p q ⟨hp, hq⟩
      subst p; subst q
      exact ⟨.ref ⟨0⟩, .here, .objectKey (proto := ⟨9⟩)
        (fields := [⟨⟨0⟩, .ref ⟨0⟩⟩]) (by simp [next, nextNode]) (by simp) .here⟩
    movedImage := by
      intro p q ⟨hp, hq⟩
      subst p; subst q
      exact ⟨.objectKeyMissing (proto := ⟨9⟩) (fields := [⟨⟨0⟩, .ref ⟨0⟩⟩])
        (by simp [next, nextNode]) (by simp),
        .ref ⟨0⟩, .objectKey (proto := ⟨9⟩) (fields := [⟨⟨0⟩, .ref ⟨0⟩⟩])
        (by simp [next, nextNode]) (by simp) .here⟩
    capturedImage := by intro p h; cases h
  }

example : ∃ v, replacementCoherence.finalValueAt [] v ∧
    replacementCoherence.finalValueAt [.objectKey ⟨0⟩] v :=
  draft_shared_finalized_image_coherence replacementCoherence ⟨rfl, rfl⟩

/-- Next-side identities are not automatically the current publication root. -/
example : nextRootImage (.ref ⟨0⟩ : Value Nat NextId) ≠ .ref (.inl ⟨0⟩) := by decide

def selfRecipePublication : RecipePublicationSpecCore current
    (publishRecords selfWitness.image (publicationProto current selfWitness.image)
      [(⟨0⟩, nextNode)] ∅) (.ref ⟨0⟩) (.ref (.inl ⟨0⟩)) where
  nextHeap := next
  nextRoot := .ref ⟨0⟩
  draftSpec := replacementDraft
  reconcileSpec := selfSuccess

example : execReconcileRoot current next (.ref ⟨0⟩) (.ref ⟨0⟩) =
    .ok (.ref (.inl ⟨0⟩)) :=
  recipe_publication_root_replacement_publication selfRecipePublication rfl

example : SurfaceEq next
    (publishRecords selfWitness.image (publicationProto current selfWitness.image)
      [(⟨0⟩, nextNode)] ∅)
    (.ref ⟨0⟩) (.ref (.inl ⟨0⟩)) := reconcile_soundness selfSuccess

example : execReconcileRoot
    (Finmap.singleton (CurId.mk 0) (.arrayBuffer [1] : Node Nat CurId))
    (Finmap.singleton (NextId.mk 0) (.arrayBuffer [1, 2] : Node Nat NextId))
    (.ref ⟨0⟩) (.ref ⟨0⟩) = .error .incompatibleRoot := by simp [execReconcileRoot, compatibleShape]

example : execReconcileRoot current
    (Finmap.singleton (NextId.mk 0) (.array [] : Node Nat NextId))
    (.ref ⟨0⟩) (.ref ⟨0⟩) = .error .incompatibleRoot := by simp [execReconcileRoot, compatibleShape]

example : execReconcileRoot current next (.atom 1) (.ref ⟨0⟩) =
    .ok (nextRootImage (.ref ⟨0⟩)) := rfl

example : execReconcileRoot current next (.ref ⟨0⟩) (.atom 0) = .ok (.atom 0) := rfl

/-- A two-node cycle plus an unrelated branch. -/
def parents : Nat → List Nat
  | 0 => [1]
  | 1 => [0]
  | _ => []

example : reuseSurvivors parents [0] {0, 1, 2} = {2} := by simp [reuseSurvivors, parents]
example : reuseSurvivors parents [] {0, 1, 2} = {0, 1, 2} := by simp [reuseSurvivors]
example : reuseSurvivors parents [0, 0, 1] {0, 1, 2} = {2} := by simp [reuseSurvivors, parents]

/-- Readback must reject the wrong root back-edge, even with the right root payload shape. -/
example : checkPublication selfWitness.image (publicationProto current selfWitness.image)
    [(⟨0⟩, nextNode)]
    (Finmap.singleton (Sum.inl (CurId.mk 0))
      (.plainObject ⟨7⟩ [⟨⟨0⟩, .ref (.inr ⟨0⟩)⟩])) = false := by decide

example : checkPublication selfWitness.image (publicationProto current selfWitness.image)
    [(⟨0⟩, nextNode)]
    (publishRecords selfWitness.image (publicationProto current selfWitness.image)
      [(⟨0⟩, nextNode)] ∅) = true := by decide

def kinds : List (NextId × Node Nat NextId) :=
  [(⟨0⟩, .plainObject ⟨3⟩ [⟨⟨2⟩, .ref ⟨1⟩⟩, ⟨⟨1⟩, .ref ⟨2⟩⟩]),
   (⟨1⟩, .array [some (.ref ⟨0⟩), none, some (.atom 0)]),
   (⟨2⟩, .map [(.ref ⟨1⟩, .ref ⟨3⟩), (.atom 2, .ref ⟨1⟩)]),
   (⟨3⟩, .set [.ref ⟨1⟩, .ref ⟨4⟩]),
   (⟨4⟩, .arrayBuffer [1, 2, 3, 4]),
   (⟨5⟩, .dataView ⟨4⟩ 0 4),
   (⟨6⟩, .typedArray ⟨0⟩ ⟨4⟩ 0 4 [.atom 1, .atom 2, .atom 3, .atom 4]),
   (⟨7⟩, .date 123)]

def kindImage (n : NextId) : ResId := if n.val = 7 then .inr ⟨7⟩ else .inl ⟨n.val⟩
def kindStorage : ResId → Nat := Sum.elim CurId.val (fun f => 100 + f.val)
def kindResult : Heap Nat ResId := publishRecords kindImage (fun _ => id) kinds ∅

example : checkOwnership kinds kindImage kindStorage = true := by decide
example : checkOwnership kinds (fun _ => .inl ⟨0⟩) kindStorage = false := by decide
example : checkOwnership kinds kindImage (fun _ => 0) = false := by decide
example : checkPublication kindImage (fun _ => id) kinds kindResult = true := by decide

-- Mutations that preserve most values but violate the observable contract.
example : checkPublication kindImage (fun _ => id) kinds
    (kindResult.insert (.inl ⟨1⟩) (.array
      [some (.ref (.inl ⟨0⟩)), some (.atom 0), some (.atom 0)])) = false := by decide
example : checkPublication kindImage (fun _ => id) kinds
    (kindResult.insert (.inl ⟨0⟩) (.plainObject ⟨3⟩
      [⟨⟨1⟩, .ref (.inl ⟨2⟩)⟩, ⟨⟨2⟩, .ref (.inl ⟨1⟩)⟩])) = false := by decide
example : checkPublication kindImage (fun _ => id) kinds
    (kindResult.insert (.inl ⟨2⟩) (.map
      [(.atom 2, .ref (.inl ⟨1⟩)), (.ref (.inl ⟨1⟩), .ref (.inl ⟨3⟩))])) = false := by decide
example : checkPublication kindImage (fun _ => id) kinds
    (kindResult.insert (.inl ⟨3⟩) (.set [.ref (.inl ⟨4⟩), .ref (.inl ⟨1⟩)])) = false := by decide
example : checkPublication kindImage (fun _ => id) kinds
    (kindResult.insert (.inl ⟨5⟩) (.dataView (.inr ⟨4⟩) 0 4)) = false := by decide

-- View extent/constructor changes are not representable at the retained root.
def shapeCurrent : Heap Nat CurId := Finmap.singleton ⟨0⟩ (.arrayBuffer [1, 2, 3, 4])
def shapeNext : Heap Nat NextId := Finmap.singleton ⟨0⟩ (.arrayBuffer [1, 2, 3, 4])
example : compatibleShape shapeCurrent shapeNext
    (.dataView ⟨0⟩ 0 2) (.dataView ⟨0⟩ 1 2) = false := by decide
example : compatibleShape shapeCurrent shapeNext
    (.typedArray ⟨0⟩ ⟨0⟩ 0 1 [.atom 1])
    (.typedArray ⟨1⟩ ⟨0⟩ 0 1 [.atom 1]) = false := by decide
example : compatibleShape shapeCurrent shapeNext
    (.dataView ⟨0⟩ 0 4) (.dataView ⟨0⟩ 0 4) = true := by decide
example : compatibleShape shapeCurrent
    (Finmap.singleton (NextId.mk 0) (.arrayBuffer [1, 2]))
    (.dataView ⟨0⟩ 0 2) (.dataView ⟨0⟩ 0 2) = false := by decide

-- Surface readback alone cannot reject collapse of equal-payload distinct nodes.
def equalNodes : List (NextId × Node Nat NextId) :=
  [(⟨0⟩, .plainObject ⟨0⟩ []), (⟨1⟩, .plainObject ⟨0⟩ [])]
example : checkPublication (fun _ => (.inl ⟨0⟩ : ResId)) (fun _ => id) equalNodes
    (Finmap.singleton (Sum.inl (CurId.mk 0)) (.plainObject ⟨0⟩ [])) = true := by decide
example : checkOwnership equalNodes (fun _ => .inl ⟨0⟩) kindStorage = false := by decide

namespace SnapshotSeparation

abbrev source : Heap Nat Nat := (Finmap.singleton 0 (.date 0)).insert 1 (.date 0)
abbrev swapped : Finmap (fun _ : Nat => Nat) := (Finmap.singleton 0 1).insert 1 0
abbrev fresh : Finmap (fun _ : Nat => Nat) := (Finmap.singleton 0 2).insert 1 3
abbrev detached : Heap Nat Nat := (Finmap.singleton 2 (.date 0)).insert 3 (.date 0)

private theorem lookup_pair {a b r r' : Nat} :
    ((Finmap.singleton 0 a : Finmap (fun _ : Nat => Nat)).insert 1 b).lookup r = some r' ↔
      (r = 0 ∧ r' = a) ∨ (r = 1 ∧ r' = b) := by
  constructor
  · intro h
    have hr : r = 1 ∨ r = 0 := by
      simpa using Finmap.mem_of_lookup_eq_some h
    rcases hr with rfl | rfl <;> simp_all
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

/-- The old specification admits exchanging two equal source nodes. -/
theorem swapped_spec : SnapshotMemoSpec source source swapped := by
  constructor
  · intro r₁ r₂ r' h₁ h₂
    rcases lookup_pair.mp h₁ with ⟨rfl, h₁⟩ | ⟨rfl, h₁⟩ <;>
      rcases lookup_pair.mp h₂ with ⟨rfl, h₂⟩ | ⟨rfl, h₂⟩ <;> omega
  · intro r r' hm nd hn
    rcases lookup_pair.mp hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals
      have he : nd = .date 0 := by simpa [source] using hn.symm
      subst nd
      exact ⟨.date 0, by decide, .date⟩
  · intro r r' hm
    rcases lookup_pair.mp hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact ⟨.date 0, by decide⟩
  · intro r r' hm
    rcases lookup_pair.mp hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

example : SnapshotSpec source (.ref 0) source (.ref 1) :=
  ⟨swapped, .memoHit (by decide), swapped_spec⟩

example : ¬ SnapshotMemoDisjoint source swapped := by
  intro h
  have := h 0 1 (by decide)
  simp [source] at this

/-- Detached copies inhabit the stronger contract; it does not exclude ordinary snapshots. -/
theorem fresh_spec : DetachedSnapshotSpec source (.ref 0) detached (.ref 2) := by
  refine ⟨fresh, .memoHit (by decide), ?_, ?_⟩
  · constructor
    · intro r₁ r₂ r' h₁ h₂
      rcases lookup_pair.mp h₁ with ⟨rfl, h₁⟩ | ⟨rfl, h₁⟩ <;>
        rcases lookup_pair.mp h₂ with ⟨rfl, h₂⟩ | ⟨rfl, h₂⟩ <;> omega
    · intro r r' hm nd hn
      rcases lookup_pair.mp hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals
        have he : nd = .date 0 := by simpa [source] using hn.symm
        subst nd
        exact ⟨.date 0, by decide, .date⟩
    · intro r r' hm
      rcases lookup_pair.mp hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact ⟨.date 0, by decide⟩
    · intro r r' hm
      rcases lookup_pair.mp hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · intro r r' hm
    rcases lookup_pair.mp hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

example : source.lookup 2 = none := detachedSnapshot_root_disjoint fresh_spec

end SnapshotSeparation

end Reconcile.ContractTest

namespace Reconcile.ContractTest.NativeValue
open Reconcile.Types.NativeValue

-- Inhabited immutable reuse.
example : reusable (.temporal .instant 0 ["0"]) (.temporal .instant 0 ["0"]) = true := rfl
-- Equal text does not erase native class differences.
example : compatible (.temporal .plainDate 0 ["x"]) (.temporal .plainTime 0 ["x"]) = false := rfl
-- Identity labels remain distinct independently of payload labels.
-- The runtime must establish the existing graph witness to obtain no-collapse.
example : (Value.ref 0 : Value Payload Nat) ≠ .ref 1 := by decide
example : bigint (ι := Nat) 9007199254740993 ≠ bigint 9007199254740992 := by decide
example : appendEntries [] [("a", "1"), ("a", "2")] =
    [("a", "1"), ("a", "2")] := rfl
end Reconcile.ContractTest.NativeValue

namespace Reconcile.ContractTest.OwnedNativeChild
open Reconcile.OwnedNativeChild
example : admit (fun n => n + 1) 4 5 = true := rfl
example : admit (fun n => n + 1) 4 6 = false := rfl
end Reconcile.ContractTest.OwnedNativeChild
