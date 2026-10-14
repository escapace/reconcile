import IncomingConsensus
import GraphPolicy

namespace Reconcile.ActiveDemands

open IncomingConsensus Policy

abbrev Table := Nat → Summary Nat
abbrev Frame := Nat × Summary Nat
abbrev State := Table × List Frame

def empty : Table := fun _ => .empty

def push (s : State) (edge : Requirement) : State :=
  (Function.update s.1 edge.node (combine (s.1 edge.node) (.one edge.identity)),
    (edge.node, s.1 edge.node) :: s.2)

def pop (s : State) : State :=
  match s.2 with
  | [] => s
  | (node, old) :: rest => (Function.update s.1 node old, rest)

def undo : Nat → State → State
  | 0, s => s
  | n + 1, s => pop (undo n s)

/-- A saved value restores even a conflicting or already-equal prior demand. -/
theorem pop_push (s : State) (edge : Requirement) : pop (push s edge) = s := by
  rcases s with ⟨table, trail⟩
  simp [pop, push, Function.update_idem]

/-- The reverse trail restores exactly the entry state, including an older trail. -/
theorem undo_fold (edges : List Requirement) (s : State) :
    undo edges.length (edges.foldl push s) = s := by
  induction edges generalizing s with
  | nil => rfl
  | cons edge rest ih =>
    simp only [List.length_cons, List.foldl, undo, ih, pop_push]

/-- Saved targets can be recovered from the reversed events instead of stored twice. -/
theorem trail_targets (edges : List Requirement) (s : State) :
    ((edges.foldl push s).2.map Prod.fst) =
      (edges.map Requirement.node).reverse ++ s.2.map Prod.fst := by
  induction edges generalizing s with
  | nil => simp
  | cons edge rest ih => simp [List.foldl, ih, push, List.reverse_cons, List.append_assoc]

/-- Querying an updated table adds only the requirement for that target. -/
theorem push_accepts (s : State) (edge : Requirement) (node identity : Nat) :
    accepts ((push s edge).1 node) identity ↔
      accepts (s.1 node) identity ∧ (edge.node = node → edge.identity = identity) := by
  by_cases h : edge.node = node
  · simp only [push, h, Function.update_self]
    rw [accepts_combine]
    simp [accepts]
  · simp [push, Function.update_of_ne (Ne.symm h), h]

theorem fold_accepts (edges : List Requirement) (s : State) (node identity : Nat) :
    accepts ((edges.foldl push s).1 node) identity ↔
      accepts (s.1 node) identity ∧
        ∀ edge ∈ edges, edge.node = node → edge.identity = identity := by
  induction edges generalizing s with
  | nil => simp
  | cons edge rest ih =>
    simp only [List.foldl, ih, push_accepts, List.mem_cons]
    aesop

/-- Only forward edges need maintenance: self and backward edges retain their outgoing check. -/
def forward (owner : Nat) (choice : Choice) : List Requirement :=
  choice.required.filter fun edge => owner < edge.node

def events (chosen : List (Nat × Choice)) : List Requirement :=
  chosen.flatMap fun entry => forward entry.1 entry.2

def maintained (chosen : List (Nat × Choice)) : State :=
  (events chosen).foldl push (empty, [])

/-- This is the old incoming scan restricted to the actually selected prefix choices. -/
def scanAccepts (chosen : List (Nat × Choice)) (node identity : Nat) : Prop :=
  ∀ entry ∈ chosen, entry.1 < node →
    ∀ edge ∈ entry.2.required, edge.node = node → edge.identity = identity

theorem maintained_iff_scan (chosen : List (Nat × Choice)) (node identity : Nat) :
    accepts ((maintained chosen).1 node) identity ↔ scanAccepts chosen node identity := by
  unfold maintained
  rw [fold_accepts]
  simp only [empty, accepts, true_and]
  simp [events, forward, scanAccepts]
  aesop

/-- Assignment is an incremental fold, not a reconstruction of the selected prefix. -/
theorem assign_eq (chosen : List (Nat × Choice)) (owner : Nat) (choice : Choice) :
    (forward owner choice).foldl push (maintained chosen) =
      maintained (chosen ++ [(owner, choice)]) := by
  simp [maintained, events, List.foldl_append]

theorem unassign_eq (chosen : List (Nat × Choice)) (owner : Nat) (choice : Choice) :
    undo (forward owner choice).length (maintained (chosen ++ [(owner, choice)])) =
      maintained chosen := by
  rw [← assign_eq, undo_fold]

-- Native correspondence: the chosen prefix contains exactly one selected choice for each
-- earlier node, in traversal order. Its private requirements remain immutable for
-- the stream. The runtime saves only old summaries, recovering each saved target
-- by reversing the same forward requirements on backtrack. Choice, storage, score,
-- outgoing support checks, tier preferences and generator suspension are unchanged.
-- These theorems do not assume a JavaScript evaluator or prove native observation laws.
example : undo 2 (([{ node := 2, identity := 7 }, { node := 2, identity := 8 }] :
    List Requirement).foldl push (empty, [])) = (empty, []) := by
  exact undo_fold [{ node := 2, identity := 7 }, { node := 2, identity := 8 }] (empty, [])
example : ¬ accepts ((([{ node := 2, identity := 7 }, { node := 2, identity := 8 }] :
    List Requirement).foldl push (empty, [])).1 2) 7 := by decide

end Reconcile.ActiveDemands
