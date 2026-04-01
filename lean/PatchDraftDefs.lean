/-
  Patch draft layer — proof-facing draft definitions.

  This file introduces the abstract vocabulary for the replacement patch model:

    draft execution → draft finalization to one next graph → one root reconcile

  The goal is not to formalize JavaScript proxies or engine behavior.
  The goal is to expose the proof-relevant structure needed by the new patch
  semantics:

  - paths accessed and touched during draft execution
  - lazy child-draft creation
  - copy-on-write bookkeeping
  - explicit delete vs assignment-of-undefined distinction
  - abstract native collection mutation logs
  - a current→next preservation witness for finalization
-/

import Defs
import WF

namespace Reconcile

/-- A proof-facing path element inside a draft. -/
inductive DraftPathElem where
  | objectKey (k : PropertyKey)
  | arrayIndex (i : Nat)
  | mapEntry (i : Nat)
  | setEntry (i : Nat)
deriving DecidableEq, Repr

/-- A proof-facing path inside a draft. -/
abbrev DraftPath := List DraftPathElem

/-- Root patch return mode.
    `finalized` means the draft tree is finalized into the next graph.
    `replaced v` means the recipe returned an explicit non-draft root `v`. -/
inductive DraftReturnMode (A : Type) (ι : Type) where
  | finalized
  | replaced (value : Value A ι)
deriving Repr

/-- Abstract draft-level array effects. These are proof-facing semantic events,
    not the user-facing API. -/
inductive ArrayDraftOp (A : Type) (ι : Type) where
  | write (index : Nat) (value : Value A ι)
  | hole (index : Nat)
  | truncate (length : Nat)
deriving Repr

/-- Abstract draft-level map effects. -/
inductive MapDraftOp (A : Type) (ι : Type) where
  | set (key : Value A ι) (value : Value A ι)
  | delete (key : Value A ι)
  | clear
deriving Repr

/-- Abstract draft-level set effects. -/
inductive SetDraftOp (A : Type) (ι : Type) where
  | add (value : Value A ι)
  | delete (value : Value A ι)
  | clear
deriving Repr

/-- Proof-facing witness of draft access, touch, and mutation bookkeeping. -/
structure DraftTouchWitness (A : Type) where
  /-- Paths observed during draft execution. -/
  accessed : DraftPath → Prop
  /-- Paths at which a child draft exists. -/
  childDraftAt : DraftPath → Prop
  /-- Paths that were read in a pure read-only way. -/
  pureReadAt : DraftPath → Prop
  /-- Which current node a path denotes, when relevant. -/
  pathNode : DraftPath → CurId → Prop
  /-- Paths directly touched by mutation. -/
  touchedPath : DraftPath → Prop
  /-- Current nodes directly touched by mutation. -/
  touchedNode : CurId → Prop
  /-- Current nodes marked modified. -/
  modifiedNode : CurId → Prop
  /-- Current nodes whose copy-on-write working copy was allocated. -/
  copiedNode : CurId → Prop
  /-- Parent relation between current nodes in the draft tree. -/
  parentOf : CurId → CurId → Prop
  /-- Paths deleted explicitly. -/
  deletedPathAt : DraftPath → Prop
  /-- Paths assigned the ordinary value `undefined`.
      The semantic model stays JS-free, so this is an abstract marker rather
      than a concrete atom test. -/
  assignedUndefinedAt : DraftPath → Prop
  /-- Abstract native array mutation log at a path. -/
  arrayOpsAt : DraftPath → List (ArrayDraftOp A NextId)
  /-- Abstract native map mutation log at a path. -/
  mapOpsAt : DraftPath → List (MapDraftOp A NextId)
  /-- Abstract native set mutation log at a path. -/
  setOpsAt : DraftPath → List (SetDraftOp A NextId)

/-- Cross-graph witness for draft finalization.
    `preserve(c) = n` means the finalized next graph contains a node `n`
    corresponding to current node `c` under finalization. -/
structure FinalizeWitness where
  preserve : Finmap (fun _ : CurId => NextId)

end Reconcile
