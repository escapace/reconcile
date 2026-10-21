import Graph.ConstructionCompletion

/-! Fresh-node setup for the finite construction queue. Retained receivers are
already available; their outgoing construction edges are not scheduling obligations. -/
namespace Reconcile.ConstructionSetup

open Reconcile.Construction Reconcile.ConstructionFrontier

def freshNodes (retained : Finset Nat) (nodes : List Nat) : List Nat :=
  nodes.filter fun node => decide (node ∉ retained)

def freshDeps (deps : Dependencies) (retained : Finset Nat) : Dependencies :=
  fun node => if node ∈ retained then [] else deps node

def seeds (deps : Dependencies) (retained : Finset Nat) (nodes : List Nat) : List Nat :=
  (freshNodes retained nodes).filter (counterReady deps retained)

theorem fresh_mem (retained : Finset Nat) (nodes : List Nat) (node : Nat) :
    node ∈ freshNodes retained nodes ↔ node ∈ nodes ∧ node ∉ retained := by
  simp [freshNodes]

theorem seeds_mem (deps : Dependencies) (retained : Finset Nat) (nodes : List Nat) (node : Nat) :
    node ∈ seeds deps retained nodes ↔
      node ∈ freshNodes retained nodes ∧ outstanding (deps node) retained = 0 := by
  simp [seeds, counterReady]

theorem seeds_nodup (deps : Dependencies) (retained : Finset Nat) (nodes : List Nat)
    (unique : nodes.Nodup) : (seeds deps retained nodes).Nodup := by
  exact (unique.filter _).filter _

theorem seeds_complete (deps : Dependencies) (retained : Finset Nat) (nodes : List Nat)
    (node : Nat) (fresh : node ∈ freshNodes retained nodes)
    (ready : outstanding (deps node) retained = 0) : node ∈ seeds deps retained nodes := by
  exact (seeds_mem deps retained nodes node).mpr ⟨fresh, ready⟩

theorem seed_ready (deps : Dependencies) (retained : Finset Nat) (nodes : List Nat)
    (node : Nat) (member : node ∈ seeds deps retained nodes) :
    outstanding (deps node) retained = 0 :=
  ((seeds_mem deps retained nodes node).mp member).2

theorem freshDeps_agree (deps : Dependencies) (retained : Finset Nat) (node : Nat)
    (fresh : node ∉ retained) : freshDeps deps retained node = deps node := by
  simp [freshDeps, fresh]

theorem safe_congr (left right : Dependencies) (known : Finset Nat) (order : List Nat)
    (agree : ∀ node ∈ order, left node = right node) :
    Safe left known order ↔ Safe right known order := by
  induction order generalizing known with
  | nil => rfl
  | cons node rest ih =>
    simp only [Safe, agree node (by simp)]
    rw [ih (insert node known) (fun child hc => agree child (by simp [hc]))]

theorem retained_edges_irrelevant (deps : Dependencies) (retained known : Finset Nat)
    (order : List Nat) (fresh : ∀ node ∈ order, node ∉ retained) :
    Safe (freshDeps deps retained) known order ↔ Safe deps known order := by
  apply safe_congr
  intro node hn
  exact freshDeps_agree deps retained node (fresh node hn)

theorem fresh_queue_drains (deps reverse : Dependencies) (retained : Finset Nat)
    (nodes : List Nat) (unique : nodes.Nodup)
    (reverseBound : ∀ dependency node, node ∈ reverse dependency → node ∈ freshNodes retained nodes) :
    (Reconcile.ConstructionCompletion.runQueue reverse (freshNodes retained nodes).toFinset.card
      ⟨[], seeds deps retained nodes, fun node => outstanding (deps node) retained⟩).pending = [] := by
  apply Reconcile.ConstructionCompletion.run_drains reverse (seeds deps retained nodes)
    (fun node => outstanding (deps node) retained) (freshNodes retained nodes).toFinset
    (seeds_nodup deps retained nodes unique) (seed_ready deps retained nodes)
  · intro node hn
    exact List.mem_toFinset.mpr ((seeds_mem deps retained nodes node).mp hn).1
  · intro dependency node hn
    exact List.mem_toFinset.mpr (reverseBound dependency node hn)
  · exact Reconcile.ConstructionCompletion.initial_queue_invariant _ _ _
  · simp

-- Queue admission may include this node immediately; final level ordering must
-- still place empty shells before nonempty dependencies satisfied by retention.
example : seeds (fun node => if node = 1 then [0] else []) {0} [0, 1, 2] = [1, 2] := by decide
example : schedule (fun node => if node = 1 then [0] else []) {0} [0, 1, 2] = some [2, 1] := by decide

theorem freshDeps_seeds (deps : Dependencies) (retained : Finset Nat) (nodes : List Nat) :
    seeds (freshDeps deps retained) retained nodes = seeds deps retained nodes := by
  apply List.filter_congr
  intro node hn
  simp only [counterReady, freshDeps_agree deps retained node ((fresh_mem _ _ _).mp hn).2]

def freshRun (deps reverse : Dependencies) (retained : Finset Nat) (nodes : List Nat) :=
  Reconcile.ConstructionCompletion.runQueue reverse (freshNodes retained nodes).toFinset.card
    ⟨[], seeds (freshDeps deps retained) retained nodes,
      fun n => outstanding (freshDeps deps retained n) retained⟩

theorem freshRun_complete (deps reverse : Dependencies) (retained : Finset Nat)
    (nodes order : List Nat) (unique : nodes.Nodup)
    (transpose : Reconcile.ConstructionIncidence.Transpose (freshDeps deps retained) reverse)
    (reverseBound : ∀ d n, n ∈ reverse d → n ∈ freshNodes retained nodes)
    (success : schedule deps retained nodes = some order) :
    ∀ node ∈ freshNodes retained nodes, node ∈ (freshRun deps reverse retained nodes).processed := by
  apply Reconcile.ConstructionCompletion.run_complete_if_safe
    (freshDeps deps retained) reverse transpose retained (freshNodes retained nodes)
    (seeds (freshDeps deps retained) retained nodes)
    (seeds_nodup _ _ _ unique) (seed_ready _ _ _)
    (fun n hn => ((seeds_mem _ _ _ _).mp hn).1) reverseBound
    (fun n hn => ((fresh_mem _ _ _).mp hn).2) (seeds_complete _ _ _)
  refine ⟨order, ?_, schedule_perm success⟩
  apply (retained_edges_irrelevant deps retained retained order ?_).mpr (schedule_safe success)
  intro n hn
  exact ((fresh_mem retained nodes n).mp ((schedule_perm success).mem_iff.mp hn)).2

theorem freshRun_missing_rejects (deps reverse : Dependencies) (retained : Finset Nat)
    (nodes : List Nat) (unique : nodes.Nodup)
    (transpose : Reconcile.ConstructionIncidence.Transpose (freshDeps deps retained) reverse)
    (reverseBound : ∀ d n, n ∈ reverse d → n ∈ freshNodes retained nodes)
    (missing : ∃ node ∈ freshNodes retained nodes,
      node ∉ (freshRun deps reverse retained nodes).processed) :
    schedule deps retained nodes = none := by
  cases hs : schedule deps retained nodes with
  | none => rfl
  | some order =>
    obtain ⟨node, hn, absent⟩ := missing
    exact False.elim (absent (freshRun_complete deps reverse retained nodes order unique
      transpose reverseBound hs node hn))

theorem freshRun_success_of_complete (deps reverse : Dependencies) (retained : Finset Nat)
    (nodes : List Nat) (unique : nodes.Nodup)
    (transpose : Reconcile.ConstructionIncidence.Transpose (freshDeps deps retained) reverse)
    (reverseBound : ∀ d n, n ∈ reverse d → n ∈ freshNodes retained nodes)
    (complete : ∀ node ∈ freshNodes retained nodes,
      node ∈ (freshRun deps reverse retained nodes).processed) :
    ∃ order, schedule deps retained nodes = some order := by
  let state := freshRun deps reverse retained nodes
  have inv := Reconcile.ConstructionCompletion.run_preserves_invariant reverse
    (seeds (freshDeps deps retained) retained nodes)
    (fun n => outstanding (freshDeps deps retained n) retained)
    (freshNodes retained nodes).toFinset.card
    ⟨[], seeds (freshDeps deps retained) retained nodes,
      fun n => outstanding (freshDeps deps retained n) retained⟩
    (Reconcile.ConstructionCompletion.initial_queue_invariant _ _ _)
  change Reconcile.ConstructionCompletion.QueueInvariant reverse
    (seeds (freshDeps deps retained) retained nodes)
    (fun n => outstanding (freshDeps deps retained n) retained) state at inv
  have subset : ∀ n ∈ state.processed, n ∈ freshNodes retained nodes := by
    intro n hn
    have hf : n ∈ state.processed ++ state.pending := List.mem_append_left _ hn
    rw [inv.1] at hf
    rcases List.mem_append.mp hf with hs | he
    · exact ((seeds_mem _ _ _ _).mp hs).1
    · obtain ⟨d, _, hd⟩ := List.mem_flatMap.mp
        (Reconcile.ConstructionAdmission.notifications_subset _ _ he)
      exact reverseBound d n hd
  have processedUnique := Reconcile.ConstructionCompletion.processed_nodup reverse
    (seeds (freshDeps deps retained) retained nodes) _ state inv
    (seeds_nodup _ _ _ unique) (seed_ready _ _ _)
  have safe := Reconcile.ConstructionCompletion.initial_run_safe (freshDeps deps retained) reverse
    transpose retained (seeds (freshDeps deps retained) retained nodes)
    (seeds_nodup _ _ _ unique) (seed_ready _ _ _)
    (fun n hn => ((fresh_mem _ _ _).mp ((seeds_mem _ _ _ _).mp hn).1).2)
    (fun d n hn => ((fresh_mem _ _ _).mp (reverseBound d n hn)).2)
    (freshNodes retained nodes).toFinset.card
  apply schedule_complete
  refine ⟨state.processed, ?_, ?_⟩
  · exact (retained_edges_irrelevant deps retained retained state.processed
      (fun n hn => ((fresh_mem _ _ _).mp (subset n hn)).2)).mp safe
  · apply (List.perm_ext_iff_of_nodup processedUnique (unique.filter _)).mpr
    exact fun n => ⟨subset n, complete n⟩

theorem freshRun_count_complete (deps reverse : Dependencies) (retained : Finset Nat)
    (nodes : List Nat) (unique : nodes.Nodup)
    (reverseBound : ∀ d n, n ∈ reverse d → n ∈ freshNodes retained nodes) :
    (freshRun deps reverse retained nodes).processed.length = (freshNodes retained nodes).length ↔
      ∀ node ∈ freshNodes retained nodes, node ∈ (freshRun deps reverse retained nodes).processed := by
  let state := freshRun deps reverse retained nodes
  have inv := Reconcile.ConstructionCompletion.run_preserves_invariant reverse
    (seeds (freshDeps deps retained) retained nodes)
    (fun n => outstanding (freshDeps deps retained n) retained)
    (freshNodes retained nodes).toFinset.card
    ⟨[], seeds (freshDeps deps retained) retained nodes,
      fun n => outstanding (freshDeps deps retained n) retained⟩
    (Reconcile.ConstructionCompletion.initial_queue_invariant _ _ _)
  change Reconcile.ConstructionCompletion.QueueInvariant reverse
    (seeds (freshDeps deps retained) retained nodes)
    (fun n => outstanding (freshDeps deps retained n) retained) state at inv
  have subset : ∀ n ∈ state.processed, n ∈ freshNodes retained nodes := by
    intro n hn
    have hf : n ∈ state.processed ++ state.pending := List.mem_append_left _ hn
    rw [inv.1] at hf
    rcases List.mem_append.mp hf with hs | he
    · exact ((seeds_mem _ _ _ _).mp hs).1
    · obtain ⟨d, _, hd⟩ := List.mem_flatMap.mp
        (Reconcile.ConstructionAdmission.notifications_subset _ _ he)
      exact reverseBound d n hd
  have processedUnique := Reconcile.ConstructionCompletion.processed_nodup reverse
    (seeds (freshDeps deps retained) retained nodes) _ state inv
    (seeds_nodup _ _ _ unique) (seed_ready _ _ _)
  have sub : state.processed.toFinset ⊆ (freshNodes retained nodes).toFinset := by
    intro n hn
    exact List.mem_toFinset.mpr (subset n (List.mem_toFinset.mp hn))
  have freshUnique : (freshNodes retained nodes).Nodup := unique.filter _
  constructor
  · intro count
    have eqset := Finset.eq_of_subset_of_card_le sub (by
      rw [List.toFinset_card_of_nodup processedUnique, List.toFinset_card_of_nodup freshUnique]
      exact count.ge)
    intro node hn
    apply List.mem_toFinset.mp
    rw [eqset]
    exact List.mem_toFinset.mpr hn
  · intro complete
    have eqset : state.processed.toFinset = (freshNodes retained nodes).toFinset := by
      apply Finset.Subset.antisymm sub
      intro n hn
      exact List.mem_toFinset.mpr (complete n (List.mem_toFinset.mp hn))
    have hc := congrArg Finset.card eqset
    simpa only [List.toFinset_card_of_nodup processedUnique,
      List.toFinset_card_of_nodup freshUnique] using hc

end Reconcile.ConstructionSetup
