import Mathlib.Data.List.Basic

/-!
Snapshot references own pending/ready writer state rather than indexing a separate
writer table. Canonical reference/label correspondence is a native adapter premise.
This model checks initialization and every resolution, including pending reads;
SnapshotStream separately proves delayed Map-key emission under intervening effects.
-/
namespace Reconcile.SnapshotOwner

inductive Cell (W : Type) where
  | pending
  | ready : W → Cell W

def cell {W : Type} : Option W → Cell W
  | none => .pending
  | some writer => .ready writer

def contents {W : Type} : Cell W → Option W
  | .pending => none
  | .ready writer => some writer

theorem cell_contents {W : Type} (writer : Option W) : contents (cell writer) = writer := by
  cases writer <;> rfl

structure Indexed (W : Type) where
  writers : Nat → Option W
  reads : List (Option W)

structure Owned (W : Type) where
  references : Nat → Cell W
  reads : List (Option W)

def project {W : Type} (state : Indexed W) : Owned W :=
  ⟨fun index => cell (state.writers index), state.reads⟩

inductive Event (W : Type) where
  | install : Nat → Option W → Event W
  | resolve : Nat → Event W

def indexedStep {W : Type} (state : Indexed W) : Event W → Indexed W
  | .install index writer =>
    { state with writers := fun key => if key = index then writer else state.writers key }
  | .resolve index => { state with reads := state.reads ++ [state.writers index] }

def ownedStep {W : Type} (state : Owned W) : Event W → Owned W
  | .install index writer =>
    { state with references := fun key => if key = index then cell writer else state.references key }
  | .resolve index => { state with reads := state.reads ++ [contents (state.references index)] }

theorem step_agreement {W : Type} (state : Indexed W) (event : Event W) :
    project (indexedStep state event) = ownedStep (project state) event := by
  cases event with
  | install index writer =>
    simp only [project, indexedStep, ownedStep, Owned.mk.injEq, and_true]
    funext key
    by_cases h : key = index <;> simp [h]
  | resolve index => simp [project, indexedStep, ownedStep, cell_contents]

theorem interleaved_agreement {W : Type} (state : Indexed W) (events : List (Event W)) :
    project (events.foldl indexedStep state) = events.foldl ownedStep (project state) := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
    simp only [List.foldl]
    rw [ih, step_agreement]

example : contents (Cell.pending : Cell Nat) = none := rfl
example : contents (Cell.ready 0) ≠ contents (Cell.pending : Cell Nat) := by decide

/-- Traversal returns an initialized memo value as an atom; a pending reference
    remains a node edge so cyclic construction can finish. -/
inductive MemoEdge (W : Type) where
  | node : Nat → MemoEdge W
  | atom : W → MemoEdge W
  deriving DecidableEq

def memoEdge {W : Type} (index : Nat) (writer : Option W) : MemoEdge W :=
  match writer with
  | none => .node index
  | some target => .atom target

/-- Under canonical installation, the inaccessible memo and owned reference
    select identical atom/node edges, including pending backedges. -/
theorem memo_edge_agreement {W : Type} (state : Indexed W) (index : Nat) :
    memoEdge index (state.writers index) =
      memoEdge index (contents ((project state).references index)) := by
  simp [project, cell_contents]

theorem interleaved_memo_agreement {W : Type} (state : Indexed W)
    (events : List (Event W)) (index : Nat) :
    memoEdge index ((events.foldl indexedStep state).writers index) =
      memoEdge index (contents ((events.foldl ownedStep (project state)).references index)) := by
  rw [← interleaved_agreement]
  exact memo_edge_agreement _ _

example : memoEdge 3 (none : Option Nat) = .node 3 := rfl
example : memoEdge 3 (some 7) = .atom 7 := rfl

end Reconcile.SnapshotOwner
