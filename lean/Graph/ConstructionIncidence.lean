import Graph.ConstructionFrontier

/-! Reverse dependency incidences preserve multiplicity, including duplicate edges.
The finite builder and decrement loop below model the two indexed runtime passes;
they do not model JavaScript arrays or claim the full scheduler refinement yet. -/
namespace Reconcile.ConstructionIncidence

open Reconcile.ConstructionFrontier

abbrev Adjacency := Nat → List Nat
abbrev Counters := Nat → Nat

def push (table : Adjacency) (key value : Nat) : Adjacency :=
  fun index => if index = key then value :: table index else table index

def Transpose (forward reverse : Adjacency) : Prop :=
  ∀ parent dependency, (forward parent).count dependency = (reverse dependency).count parent

theorem transpose_empty : Transpose (fun _ => []) (fun _ => []) := by
  intro parent dependency
  rfl

theorem transpose_push {forward reverse : Adjacency} (h : Transpose forward reverse)
    (parent dependency : Nat) :
    Transpose (push forward parent dependency) (push reverse dependency parent) := by
  intro p d
  have counts := h p d
  by_cases hp : p = parent <;> by_cases hd : d = dependency <;>
    simp_all [push, eq_comm]

def build (state : Adjacency × Adjacency) (edge : Nat × Nat) : Adjacency × Adjacency :=
  (push state.1 edge.1 edge.2, push state.2 edge.2 edge.1)

theorem build_transpose (edges : List (Nat × Nat)) (state : Adjacency × Adjacency)
    (h : Transpose state.1 state.2) :
    Transpose (edges.foldl build state).1 (edges.foldl build state).2 := by
  induction edges generalizing state with
  | nil => exact h
  | cons edge rest ih =>
    exact ih (build state edge) (transpose_push h edge.1 edge.2)

def tick (counters : Counters) (parent : Nat) : Counters :=
  fun node => if node = parent then counters node - 1 else counters node

theorem ticks_count (parents : List Nat) (counters : Counters) (node : Nat) :
    (parents.foldl tick counters) node = counters node - parents.count node := by
  induction parents generalizing counters with
  | nil => simp
  | cons parent rest ih =>
    simp only [List.foldl_cons, ih]
    by_cases h : node = parent
    · subst node
      simp [tick, Nat.sub_sub, Nat.add_comm]
    · simp [tick, h, Ne.symm h]

theorem singleton_discharge (dependencies : List Nat) (known : Finset Nat)
    (dependency : Nat) (fresh : dependency ∉ known) :
    discharged dependencies known {dependency} = dependencies.count dependency := by
  induction dependencies with
  | nil => simp [discharged]
  | cons head rest ih =>
    by_cases h : head = dependency
    · subst head
      simp [discharged, fresh, ← ih]
    · simp [discharged, h, ← ih]

theorem reverse_release_exact {forward reverse : Adjacency}
    (transpose : Transpose forward reverse) (known : Finset Nat) (dependency : Nat)
    (fresh : dependency ∉ known) (node : Nat) :
    ((reverse dependency).foldl tick (fun parent => outstanding (forward parent) known)) node =
      outstanding (forward node) (insert dependency known) := by
  rw [ticks_count, ← transpose node dependency]
  rw [← singleton_discharge (forward node) known dependency fresh]
  simpa using decrement_exact (forward node) known {dependency}

def release (reverse : Adjacency) (counters : Counters) (dependency : Nat) : Counters :=
  (reverse dependency).foldl tick counters

theorem release_sequence_exact {forward reverse : Adjacency}
    (transpose : Transpose forward reverse) (known : Finset Nat) (nodes : List Nat)
    (unique : nodes.Nodup) (fresh : ∀ node ∈ nodes, node ∉ known) :
    nodes.foldl (release reverse) (fun parent => outstanding (forward parent) known) =
      fun parent => outstanding (forward parent) (known ∪ nodes.toFinset) := by
  induction nodes generalizing known with
  | nil => simp
  | cons dependency rest ih =>
    have single : release reverse (fun parent => outstanding (forward parent) known) dependency =
        fun parent => outstanding (forward parent) (insert dependency known) := by
      funext parent
      exact reverse_release_exact transpose known dependency (fresh dependency (by simp)) parent
    have remaining : ∀ node ∈ rest, node ∉ insert dependency known := by
      intro node hn
      simp only [Finset.mem_insert, not_or]
      refine ⟨?_, fresh node (by simp [hn])⟩
      intro he
      subst node
      exact (List.nodup_cons.mp unique).1 hn
    simp only [List.foldl_cons, single]
    rw [ih (insert dependency known) (List.nodup_cons.mp unique).2 remaining]
    simp [Finset.union_insert, Finset.insert_union]

theorem released_ready_iff {forward reverse : Adjacency}
    (transpose : Transpose forward reverse) (known : Finset Nat) (nodes : List Nat)
    (unique : nodes.Nodup) (fresh : ∀ node ∈ nodes, node ∉ known) (parent : Nat) :
    (nodes.foldl (release reverse) (fun node => outstanding (forward node) known)) parent = 0 ↔
      ∀ dependency ∈ forward parent, dependency ∈ known ∪ nodes.toFinset := by
  rw [release_sequence_exact transpose known nodes unique fresh]
  exact outstanding_zero_iff (forward parent) (known ∪ nodes.toFinset)

example : (List.foldl tick (fun _ => 3) [4, 4]) 4 = 1 := by decide

end Reconcile.ConstructionIncidence
