import Graph.ActiveDemands
import Graph.ForcedGroups

/-! Selected-prefix backtracking restoration.
Retained because individual undo and their composition describe the current selector's
demand trail, owner set, forced followers and score. The bridge executes reference
transitions with native incoming-demand updates, not a production bulk tier exit.
The reverted retention-capacity tier exit is not modeled; no retained-capacity producer is imported. -/

namespace Reconcile.SelectionUnwind

open Policy

/-- A selected choice and only the forced followers installed by that choice. -/
structure Frame where
  node : Nat
  choice : Choice
  followers : Finset Nat

structure State where
  demands : ActiveDemands.State
  owners : Finset Nat
  forced : Finset Nat
  retained : Nat

def empty : State := ⟨(ActiveDemands.empty, []), ∅, ∅, 0⟩

def assign (state : State) (frame : Frame) : State where
  demands := (ActiveDemands.forward frame.node frame.choice).foldl ActiveDemands.push state.demands
  owners := insert frame.choice.storage state.owners
  forced := state.forced ∪ frame.followers
  retained := state.retained + if frame.choice.retained then 1 else 0

/-- This follows the existing backtrack: followers, reverse demand trail, owner, score. -/
def unassign (problem : ForcedGroups.Problem) (state : State) (frame : Frame) : State where
  demands := ActiveDemands.undo (ActiveDemands.forward frame.node frame.choice).length state.demands
  owners := state.owners.erase frame.choice.storage
  forced := ForcedGroups.clearOwners problem state.forced frame.followers
  retained := state.retained - if frame.choice.retained then 1 else 0

def Available (problem : ForcedGroups.Problem) (state : State) (frame : Frame) : Prop :=
  frame.choice.storage ∉ state.owners ∧
    ∀ old ∈ state.forced, ∀ member ∈ frame.followers, problem.owner old ≠ problem.owner member

instance (problem : ForcedGroups.Problem) (state : State) (frame : Frame) :
    Decidable (Available problem state frame) := by
  unfold Available
  infer_instance

/-- No empty-state assumption: undo restores older demands, owners, forces and score. -/
theorem unassign_assign (problem : ForcedGroups.Problem) (state : State) (frame : Frame)
    (h : Available problem state frame) :
    unassign problem (assign state frame) frame = state := by
  have hd := ActiveDemands.undo_fold (ActiveDemands.forward frame.node frame.choice) state.demands
  have hf := ForcedGroups.clear_after_assign problem state.forced frame.followers h.2
  have ho := Finset.erase_insert h.1
  cases state
  simp only [unassign, assign] at hd hf ho ⊢
  rw [hd, hf, ho, Nat.add_sub_cancel]

/-- The ordinary admission guards establish this incrementally along a prefix. -/
inductive Admitted (problem : ForcedGroups.Problem) : State → List Frame → Prop
  | nil (state : State) : Admitted problem state []
  | cons {state : State} {frame : Frame} {rest : List Frame}
      (available : Available problem state frame)
      (tail : Admitted problem (assign state frame) rest) :
      Admitted problem state (frame :: rest)

def unwind (problem : ForcedGroups.Problem) (frames : List Frame) (state : State) : State :=
  frames.reverse.foldl (unassign problem) state

/-- A cold tier exit performs the very same reverse transitions as ordinary backtracking. -/
theorem unwind_assignments (problem : ForcedGroups.Problem) (state : State) (frames : List Frame)
    (h : Admitted problem state frames) :
    unwind problem frames (frames.foldl assign state) = state := by
  induction h with
  | nil => rfl
  | @cons state frame rest available tail ih =>
    simp only [unwind, List.reverse_cons, List.foldl_append, List.foldl] at ih ⊢
    rw [ih, unassign_assign problem state frame available]

theorem cut_tier_restores_empty (problem : ForcedGroups.Problem) (frames : List Frame)
    (h : Admitted problem empty frames) :
    unwind problem frames (frames.foldl assign empty) = empty :=
  unwind_assignments problem empty frames h

/-- Duplicated demands and a forced follower participate in an actual nonempty unwind. -/
def witness : List Frame := [
  ⟨0, ⟨7, 10, true, [⟨2, 7⟩, ⟨2, 7⟩]⟩, {1}⟩,
  ⟨1, ⟨8, 11, false, [⟨2, 8⟩]⟩, ∅⟩]

example : Admitted ForcedGroups.twoCycle empty witness := by
  apply Admitted.cons
  · decide
  apply Admitted.cons
  · decide
  exact Admitted.nil _

example : (witness.foldl assign empty).demands.2.length = 3 ∧
    (witness.foldl assign empty).demands.1 2 = .conflict ∧
    (unwind ForcedGroups.twoCycle witness (witness.foldl assign empty)).demands.2 = [] ∧
    (unwind ForcedGroups.twoCycle witness (witness.foldl assign empty)).forced = ∅ := by
  decide +kernel

-- Native frames are the selected prefix, not the attempted conflicting choice. Followers
-- contain exactly the entries installed by a leader; followers install none themselves.
-- Immutable requirement order recovers trail targets, including duplicates. Storage and
-- force admission provide Available. The runtime must finish this reverse walk before
-- the next preference callback and reset its cursor to node 0 / next[0] = 0. This finite
-- state theorem does not assert observation equivalence for arbitrary JavaScript objects.

end Reconcile.SelectionUnwind
