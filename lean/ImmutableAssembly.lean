import Std

/- Private record assembly refinement. Native reads and recursion order are premises. -/
namespace Reconcile.ImmutableAssembly

structure Row where
  edges : List Nat
  target : Nat
  payload : Option Nat
  settled : Option Bool
  deriving DecidableEq

def reserve (target : Nat) : Row := ⟨[], target, none, none⟩

def append (row : Row) (edge : Nat) : Row :=
  { row with edges := row.edges ++ [edge] }

def assemble (row : Row) (edges : List Nat) : Row := edges.foldl append row

def complete (row : Row) (payload target : Nat) (settled : Option Bool) : Row :=
  { row with payload := some payload, settled, target }

theorem append_keeps_target (row : Row) (edge : Nat) :
    (append row edge).target = row.target := rfl

theorem assemble_fields (row : Row) (edges : List Nat) :
    assemble row edges = { row with edges := row.edges ++ edges } := by
  induction edges generalizing row with
  | nil => simp [assemble]
  | cons edge rest ih =>
    simp only [assemble, List.foldl]
    rw [← assemble, ih]
    simp [append, List.append_assoc]

/-- Any cycle comparison during child collection sees the original target. -/
theorem pending_target (target : Nat) (children : List Nat) :
    (assemble (reserve target) children).target = target := by
  rw [assemble_fields]
  rfl

/-- Completion publishes exactly the old replacement record. The final target
    is supplied separately: a second native read must not be removed. -/
theorem completion_agreement (initial final payload : Nat) (settled : Option Bool)
    (edges : List Nat) :
    complete (assemble (reserve initial) edges) payload final settled =
      ⟨edges, final, some payload, settled⟩ := by
  rw [assemble_fields]
  rfl

example : (complete (assemble (reserve 1) [0, 0]) 7 2 (some true)).target = 2 := rfl
example : (complete (assemble (reserve 1) [0, 0]) 7 2 none).settled = none := rfl
example : (assemble (reserve 1) [0, 0]).target = 1 := rfl

end Reconcile.ImmutableAssembly
