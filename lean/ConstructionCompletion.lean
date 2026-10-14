import ConstructionAdmission

/-! Completion through a drained notification frontier. Native allocation does not
participate: all statements concern the finite dependency problem. -/
namespace Reconcile.ConstructionCompletion

open Reconcile.Construction Reconcile.ConstructionFrontier
open Reconcile.ConstructionIncidence Reconcile.ConstructionAdmission

structure QueueState where
  processed : List Nat
  pending : List Nat
  counters : Counters

def QueueInvariant (reverse : Adjacency) (seeds : List Nat) (initial : Counters)
    (state : QueueState) : Prop :=
  state.processed ++ state.pending =
    seeds ++ notifications (state.processed.flatMap reverse) initial ∧
  state.counters = (state.processed.flatMap reverse).foldl tick initial

def processHead (reverse : Adjacency) (processed : List Nat) (head : Nat)
    (tail : List Nat) (counters : Counters) : QueueState :=
  { processed := processed ++ [head]
    pending := tail ++ notifications (reverse head) counters
    counters := (reverse head).foldl tick counters }

theorem initial_queue_invariant (reverse : Adjacency) (seeds : List Nat) (initial : Counters) :
    QueueInvariant reverse seeds initial ⟨[], seeds, initial⟩ := by
  simp [QueueInvariant, notifications]

theorem process_preserves_queue_invariant (reverse : Adjacency) (seeds : List Nat)
    (initial : Counters) (processed : List Nat) (head : Nat) (tail : List Nat)
    (counters : Counters)
    (h : QueueInvariant reverse seeds initial ⟨processed, head :: tail, counters⟩) :
    QueueInvariant reverse seeds initial (processHead reverse processed head tail counters) := by
  obtain ⟨queue, counts⟩ := h
  dsimp at queue counts
  simp only [QueueInvariant, processHead, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, notifications_append, List.foldl_append]
  constructor
  · simpa [List.append_assoc, counts] using
      congrArg (fun front => front ++ notifications (reverse head) counters) queue
  · rw [← counts]

theorem release_fold_flatMap (reverse : Adjacency) (nodes : List Nat) (counters : Counters) :
    nodes.foldl (release reverse) counters = (nodes.flatMap reverse).foldl tick counters := by
  induction nodes generalizing counters with
  | nil => rfl
  | cons node rest ih => simp [release, List.foldl_append, ih]

theorem drained_invariant (reverse : Adjacency) (seeds : List Nat) (initial : Counters)
    (processed : List Nat) (counters : Counters)
    (h : QueueInvariant reverse seeds initial ⟨processed, [], counters⟩) :
    ∀ node ∈ seeds ++ notifications (processed.flatMap reverse) initial,
      node ∈ processed.toFinset := by
  have queue := h.1
  dsimp at queue
  simp only [List.append_nil] at queue
  intro node hn
  rw [← queue] at hn
  exact List.mem_toFinset.mpr hn

def runQueue (reverse : Adjacency) : Nat → QueueState → QueueState
  | 0, state => state
  | fuel + 1, state => match state.pending with
    | [] => state
    | head :: tail => runQueue reverse fuel
        (processHead reverse state.processed head tail state.counters)

theorem run_preserves_invariant (reverse : Adjacency) (seeds : List Nat) (initial : Counters)
    (fuel : Nat) (state : QueueState) (h : QueueInvariant reverse seeds initial state) :
    QueueInvariant reverse seeds initial (runQueue reverse fuel state) := by
  induction fuel generalizing state with
  | zero => exact h
  | succ fuel ih =>
    rcases state with ⟨processed, pending, counters⟩
    cases pending with
    | nil => exact h
    | cons head tail =>
      exact ih _ (process_preserves_queue_invariant reverse seeds initial processed head tail counters h)

theorem queue_length_bound (reverse : Adjacency) (seeds : List Nat) (initial : Counters)
    (vertices : Finset Nat) (state : QueueState) (h : QueueInvariant reverse seeds initial state)
    (unique : seeds.Nodup) (ready : ∀ node ∈ seeds, initial node = 0)
    (seedBound : ∀ node ∈ seeds, node ∈ vertices)
    (reverseBound : ∀ dependency node, node ∈ reverse dependency → node ∈ vertices) :
    (state.processed ++ state.pending).length ≤ vertices.card := by
  rw [h.1]
  apply frontier_length_bound seeds (state.processed.flatMap reverse) initial vertices unique ready seedBound
  intro node hn
  obtain ⟨dependency, _, member⟩ := List.mem_flatMap.mp hn
  exact reverseBound dependency node member

theorem processed_nodup (reverse : Adjacency) (seeds : List Nat) (initial : Counters)
    (state : QueueState) (h : QueueInvariant reverse seeds initial state)
    (unique : seeds.Nodup) (ready : ∀ node ∈ seeds, initial node = 0) :
    state.processed.Nodup := by
  have full := seeded_frontier_nodup seeds (state.processed.flatMap reverse) initial unique ready
  rw [← h.1] at full
  exact full.of_append_left

theorem processed_counter_exact (forward reverse : Adjacency)
    (transpose : Transpose forward reverse) (known : Finset Nat) (seeds : List Nat)
    (state : QueueState)
    (h : QueueInvariant reverse seeds (fun node => outstanding (forward node) known) state)
    (unique : seeds.Nodup) (ready : ∀ node ∈ seeds, outstanding (forward node) known = 0)
    (fresh : ∀ node ∈ state.processed, node ∉ known) :
    state.counters = fun node => outstanding (forward node) (known ∪ state.processed.toFinset) := by
  rw [h.2, ← release_fold_flatMap]
  exact release_sequence_exact transpose known state.processed
    (processed_nodup reverse seeds _ state h unique ready) fresh

theorem run_drains (reverse : Adjacency) (seeds : List Nat) (initial : Counters)
    (vertices : Finset Nat) (unique : seeds.Nodup)
    (ready : ∀ node ∈ seeds, initial node = 0)
    (seedBound : ∀ node ∈ seeds, node ∈ vertices)
    (reverseBound : ∀ dependency node, node ∈ reverse dependency → node ∈ vertices)
    (fuel : Nat) (state : QueueState) (h : QueueInvariant reverse seeds initial state)
    (enough : vertices.card ≤ state.processed.length + fuel) :
    (runQueue reverse fuel state).pending = [] := by
  induction fuel generalizing state with
  | zero =>
    have bound := queue_length_bound reverse seeds initial vertices state h unique ready seedBound reverseBound
    simp only [List.length_append] at bound
    have empty : state.pending.length = 0 := by omega
    exact List.length_eq_zero_iff.mp empty
  | succ fuel ih =>
    rcases state with ⟨processed, pending, counters⟩
    cases pending with
    | nil => rfl
    | cons head tail =>
      apply ih _ (process_preserves_queue_invariant reverse seeds initial processed head tail counters h)
      simp only [processHead, List.length_append, List.length_singleton]
      dsimp at enough
      omega

theorem safe_contained_in_closed (deps : Dependencies) (initial known : Finset Nat)
    (vertices order : List Nat) (included : initial ⊆ known) (bounded : order ⊆ vertices)
    (safe : Safe deps initial order)
    (closed : ∀ node ∈ vertices, (∀ dependency ∈ deps node, dependency ∈ known) → node ∈ known) :
    ∀ node ∈ order, node ∈ known := by
  induction order generalizing initial with
  | nil => simp
  | cons head rest ih =>
    have hh : head ∈ known := closed head (bounded (by simp))
      (fun dependency hd => included (safe.1 dependency hd))
    have tail := ih (insert head initial) (Finset.insert_subset_iff.mpr ⟨hh, included⟩)
      (fun _ hn => bounded (by simp [hn])) safe.2
    intro node hn
    rcases List.mem_cons.mp hn with he | ht
    · simpa [he] using hh
    · exact tail node ht

theorem drained_zero_processed (seeds parents vertices : List Nat) (counters : Counters)
    (processed : Finset Nat)
    (seedComplete : ∀ node ∈ vertices, counters node = 0 → node ∈ seeds)
    (drained : ∀ node ∈ seeds ++ notifications parents counters, node ∈ processed)
    (node : Nat) (bounded : node ∈ vertices)
    (zero : (parents.foldl tick counters) node = 0) : node ∈ processed := by
  by_cases initialZero : counters node = 0
  · exact drained node (List.mem_append_left _ (seedComplete node bounded initialZero))
  · have notified : node ∈ notifications parents counters := by
      apply (notified_iff parents counters node).mpr
      rw [ticks_count] at zero
      constructor <;> omega
    exact drained node (List.mem_append_right _ notified)

theorem drained_frontier_closed (deps : Dependencies) (initial processed : Finset Nat)
    (vertices seeds parents : List Nat) (counters : Counters)
    (seedComplete : ∀ node ∈ vertices, counters node = 0 → node ∈ seeds)
    (drained : ∀ node ∈ seeds ++ notifications parents counters, node ∈ processed)
    (counts : ∀ node ∈ vertices, (parents.foldl tick counters) node =
      outstanding (deps node) (initial ∪ processed)) :
    ∀ node ∈ vertices, (∀ dependency ∈ deps node, dependency ∈ initial ∪ processed) →
      node ∈ initial ∪ processed := by
  intro node hn ready
  apply Finset.mem_union_right
  apply drained_zero_processed seeds parents vertices counters processed seedComplete drained node hn
  rw [counts node hn]
  exact (outstanding_zero_iff _ _).mpr ready

theorem drained_complete_if_safe (deps : Dependencies) (initial processed : Finset Nat)
    (vertices seeds parents : List Nat) (counters : Counters)
    (seedComplete : ∀ node ∈ vertices, counters node = 0 → node ∈ seeds)
    (drained : ∀ node ∈ seeds ++ notifications parents counters, node ∈ processed)
    (counts : ∀ node ∈ vertices, (parents.foldl tick counters) node =
      outstanding (deps node) (initial ∪ processed))
    (witness : ∃ order, Safe deps initial order ∧ order.Perm vertices) :
    ∀ node ∈ vertices, node ∈ initial ∪ processed := by
  obtain ⟨order, safe, permutation⟩ := witness
  have covered := safe_contained_in_closed deps initial (initial ∪ processed) vertices order
    Finset.subset_union_left (fun _ hn => permutation.mem_iff.mp hn) safe
    (drained_frontier_closed deps initial processed vertices seeds parents counters
      seedComplete drained counts)
  intro node hn
  exact covered node (permutation.mem_iff.mpr hn)

theorem unfinished_drained_has_no_schedule (deps : Dependencies) (initial processed : Finset Nat)
    (vertices seeds parents : List Nat) (counters : Counters)
    (seedComplete : ∀ node ∈ vertices, counters node = 0 → node ∈ seeds)
    (drained : ∀ node ∈ seeds ++ notifications parents counters, node ∈ processed)
    (counts : ∀ node ∈ vertices, (parents.foldl tick counters) node =
      outstanding (deps node) (initial ∪ processed))
    (unfinished : ∃ node ∈ vertices, node ∉ initial ∪ processed) :
    ¬ ∃ order, Safe deps initial order ∧ order.Perm vertices := by
  intro witness
  obtain ⟨node, hn, missing⟩ := unfinished
  exact missing (drained_complete_if_safe deps initial processed vertices seeds parents counters
    seedComplete drained counts witness node hn)

theorem frontier_counter_zero (reverse : Adjacency) (seeds : List Nat) (initial : Counters)
    (state : QueueState) (h : QueueInvariant reverse seeds initial state)
    (ready : ∀ node ∈ seeds, initial node = 0) (node : Nat)
    (member : node ∈ state.processed ++ state.pending) : state.counters node = 0 := by
  rw [h.1] at member
  rw [h.2, ticks_count]
  rcases List.mem_append.mp member with hs | hn
  · simp [ready node hs]
  · have notified := (notified_iff _ initial node).mp hn
    omega

theorem frontier_fresh (reverse : Adjacency) (seeds : List Nat) (initial : Counters)
    (state : QueueState) (h : QueueInvariant reverse seeds initial state) (known : Finset Nat)
    (seedFresh : ∀ node ∈ seeds, node ∉ known)
    (reverseFresh : ∀ dependency node, node ∈ reverse dependency → node ∉ known)
    (node : Nat) (member : node ∈ state.processed ++ state.pending) : node ∉ known := by
  rw [h.1] at member
  rcases List.mem_append.mp member with hs | hn
  · exact seedFresh node hs
  · obtain ⟨dependency, _, hd⟩ := List.mem_flatMap.mp (notifications_subset _ _ hn)
    exact reverseFresh dependency node hd

theorem run_processed_safe (forward reverse : Adjacency)
    (transpose : Transpose forward reverse) (known : Finset Nat) (seeds : List Nat)
    (unique : seeds.Nodup) (ready : ∀ node ∈ seeds, outstanding (forward node) known = 0)
    (seedFresh : ∀ node ∈ seeds, node ∉ known)
    (reverseFresh : ∀ dependency node, node ∈ reverse dependency → node ∉ known)
    (fuel : Nat) (state : QueueState)
    (h : QueueInvariant reverse seeds (fun node => outstanding (forward node) known) state)
    (safe : Safe forward known state.processed) :
    Safe forward known (runQueue reverse fuel state).processed := by
  induction fuel generalizing state with
  | zero => exact safe
  | succ fuel ih =>
    rcases state with ⟨processed, pending, counters⟩
    cases pending with
    | nil => exact safe
    | cons head tail =>
      apply ih _ (process_preserves_queue_invariant reverse seeds _ processed head tail counters h)
      apply safe_append safe
      have counts := processed_counter_exact forward reverse transpose known seeds
        ⟨processed, head :: tail, counters⟩ h unique ready
        (fun node hn => frontier_fresh reverse seeds _ _ h known seedFresh reverseFresh node
          (List.mem_append_left _ hn))
      have zero := frontier_counter_zero reverse seeds _ _ h ready head (by simp)
      have headReady : outstanding (forward head) (known ∪ processed.toFinset) = 0 := by
        have hc := congrFun counts head
        dsimp at hc
        exact hc.symm.trans zero
      exact ⟨(outstanding_zero_iff _ _).mp headReady, trivial⟩

theorem initial_run_safe (forward reverse : Adjacency)
    (transpose : Transpose forward reverse) (known : Finset Nat) (seeds : List Nat)
    (unique : seeds.Nodup) (ready : ∀ node ∈ seeds, outstanding (forward node) known = 0)
    (seedFresh : ∀ node ∈ seeds, node ∉ known)
    (reverseFresh : ∀ dependency node, node ∈ reverse dependency → node ∉ known)
    (fuel : Nat) :
    Safe forward known (runQueue reverse fuel
      ⟨[], seeds, fun node => outstanding (forward node) known⟩).processed := by
  exact run_processed_safe forward reverse transpose known seeds unique ready seedFresh
    reverseFresh fuel _ (initial_queue_invariant _ _ _) trivial

theorem run_complete_if_safe (forward reverse : Adjacency)
    (transpose : Transpose forward reverse) (known : Finset Nat) (vertices seeds : List Nat)
    (unique : seeds.Nodup) (ready : ∀ n ∈ seeds, outstanding (forward n) known = 0)
    (seedBound : ∀ n ∈ seeds, n ∈ vertices)
    (reverseBound : ∀ d n, n ∈ reverse d → n ∈ vertices)
    (freshVertices : ∀ n ∈ vertices, n ∉ known)
    (seedComplete : ∀ n ∈ vertices, outstanding (forward n) known = 0 → n ∈ seeds)
    (witness : ∃ order, Safe forward known order ∧ order.Perm vertices) :
    ∀ node ∈ vertices, node ∈ (runQueue reverse vertices.toFinset.card
      ⟨[], seeds, fun n => outstanding (forward n) known⟩).processed := by
  let initial : QueueState := ⟨[], seeds, fun n => outstanding (forward n) known⟩
  let state := runQueue reverse vertices.toFinset.card initial
  have inv := run_preserves_invariant reverse seeds _ vertices.toFinset.card initial
    (initial_queue_invariant _ _ _)
  have drained : state.pending = [] := by
    apply run_drains reverse seeds _ vertices.toFinset unique ready
      (fun n hn => List.mem_toFinset.mpr (seedBound n hn))
      (fun d n hn => List.mem_toFinset.mpr (reverseBound d n hn))
      vertices.toFinset.card initial (initial_queue_invariant _ _ _)
    simp [initial]
  have fresh : ∀ n ∈ state.processed, n ∉ known := by
    intro n hn
    exact frontier_fresh reverse seeds _ state inv known
      (fun n hn => freshVertices n (seedBound n hn))
      (fun d n hn => freshVertices n (reverseBound d n hn)) n
      (List.mem_append_left _ hn)
  have counts := processed_counter_exact forward reverse transpose known seeds state inv unique ready fresh
  have closure : ∀ n ∈ seeds ++ notifications (state.processed.flatMap reverse)
      (fun n => outstanding (forward n) known), n ∈ state.processed.toFinset := by
    intro n hn
    rw [← inv.1, drained, List.append_nil] at hn
    exact List.mem_toFinset.mpr hn
  have complete := drained_complete_if_safe forward known state.processed.toFinset vertices seeds
    (state.processed.flatMap reverse) (fun n => outstanding (forward n) known)
    seedComplete closure (fun n _ => by
      rw [← inv.2]
      exact congrFun counts n) witness
  intro node hn
  exact List.mem_toFinset.mp ((Finset.mem_union.mp (complete node hn)).resolve_left
    (freshVertices node hn))

theorem run_missing_rejects_safe (forward reverse : Adjacency)
    (transpose : Transpose forward reverse) (known : Finset Nat) (vertices seeds : List Nat)
    (unique : seeds.Nodup) (ready : ∀ n ∈ seeds, outstanding (forward n) known = 0)
    (seedBound : ∀ n ∈ seeds, n ∈ vertices)
    (reverseBound : ∀ d n, n ∈ reverse d → n ∈ vertices)
    (freshVertices : ∀ n ∈ vertices, n ∉ known)
    (seedComplete : ∀ n ∈ vertices, outstanding (forward n) known = 0 → n ∈ seeds)
    (missing : ∃ node ∈ vertices, node ∉ (runQueue reverse vertices.toFinset.card
      ⟨[], seeds, fun n => outstanding (forward n) known⟩).processed) :
    ¬ ∃ order, Safe forward known order ∧ order.Perm vertices := by
  intro witness
  obtain ⟨node, hn, absent⟩ := missing
  exact absent (run_complete_if_safe forward reverse transpose known vertices seeds unique ready
    seedBound reverseBound freshVertices seedComplete witness node hn)

end Reconcile.ConstructionCompletion
