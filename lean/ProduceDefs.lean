/-
  Produce draft layer — proof-facing draft definitions.

  This file introduces the abstract vocabulary for standalone next-value production:

    draft execution → draft finalization to one next graph

  A caller may subsequently reconcile that graph; production does not require it.
  JavaScript proxy behavior, recipe isolation, original-current cancellation and
  getter sealing remain native correspondence obligations. The finite vocabulary covers:

  - paths accessed and regions unchanged during draft execution
  - lazy child-draft creation
  - copy-on-write bookkeeping
  - explicit delete vs assignment-of-undefined distinction
  - abstract array effects and final slot outcomes
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

/-- Recipe return mode for next-value production.
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
deriving Repr

/-- Proof-facing witness of draft access, touch, and mutation bookkeeping. -/
structure DraftTouchWitness (A : Type) where
  /-- Paths observed during draft execution. -/
  accessed : DraftPath → Prop
  /-- Paths at which a child draft exists. -/
  childDraftAt : DraftPath → Prop
  /-- Paths read during execution. A read alone does not prohibit later writes. -/
  pureReadAt : DraftPath → Prop
  /-- Which current node a path denotes, when relevant. -/
  pathNode : DraftPath → CurId → Prop
  /-- Regions certified unchanged, including descendants and writes through aliases. -/
  unchangedRegion : CurId → Prop
  /-- Paths whose entire reachable value is certified unchanged. -/
  unchangedPath : DraftPath → Prop
  /-- Abstract dependency-propagated modification requirement. -/
  modifiedNode : CurId → Prop
  /-- Abstract copy requirement; not a concrete runtime allocation event. -/
  copiedNode : CurId → Prop
  /-- Parent relation between current nodes in the draft tree. -/
  parentOf : CurId → CurId → Prop
  /-- Paths whose final effective slot outcome is deletion, not historical deletes. -/
  deletedPathAt : DraftPath → Prop
  /-- Paths whose final effective slot outcome is assignment of `undefined`.
      The semantic model stays JS-free, so this is an abstract marker rather
      than a concrete atom test. -/
  assignedUndefinedAt : DraftPath → Prop
  /-- Last effective length constraint, after all array operations. -/
  arrayLengthAt : DraftPath → Option Nat
  /-- Abstract native array mutation log at a path. -/
  arrayOpsAt : DraftPath → List (ArrayDraftOp A NextId)

/-- Cross-graph witness for draft finalization.
    `preserve(c) = n` means the finalized next graph contains a node `n`
    corresponding to current node `c` under finalization. -/
structure FinalizeWitness where
  preserve : Finmap (fun _ : CurId => NextId)

end Reconcile
