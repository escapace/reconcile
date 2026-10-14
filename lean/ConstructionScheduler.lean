import ConstructionRankUpdates
import ConstructionBuckets

/-! Assembly of the dependency-driven scheduler. Reverse adjacency is supplied with
its finite builder contract; native observations and allocation are outside scope. -/
namespace Reconcile.ConstructionScheduler

open Reconcile.Construction Reconcile.ConstructionSetup Reconcile.ConstructionFrontier
open Reconcile.ConstructionRankUpdates Reconcile.ConstructionIncidence

def rankedFreshRun (deps reverse : Dependencies) (retained : Finset Nat) (nodes : List Nat) :
    RankedQueue :=
  runRanked reverse (freshNodes retained nodes).toFinset.card
    ⟨⟨[], seeds (freshDeps deps retained) retained nodes,
      fun n => outstanding (freshDeps deps retained n) retained⟩,
      fun n => if (freshDeps deps retained n).isEmpty then 0 else 1⟩

theorem rankedFreshRun_queue (deps reverse : Dependencies) (retained : Finset Nat)
    (nodes : List Nat) :
    (rankedFreshRun deps reverse retained nodes).queue = freshRun deps reverse retained nodes := by
  exact runRanked_queue _ _ _

theorem completed_equations (deps reverse : Dependencies) (retained : Finset Nat)
    (nodes : List Nat) (unique : nodes.Nodup)
    (transpose : Transpose (freshDeps deps retained) reverse)
    (reverseBound : ∀ d n, n ∈ reverse d → n ∈ freshNodes retained nodes)
    (complete : ∀ n ∈ freshNodes retained nodes, n ∈ (freshRun deps reverse retained nodes).processed) :
    ∀ node ∈ freshNodes retained nodes,
      (rankedFreshRun deps reverse retained nodes).ranks node =
        Reconcile.ConstructionLevels.levelRule deps retained
          (rankedFreshRun deps reverse retained nodes).ranks node := by
  intro node hn
  have eqn := ranked_queue_level_equation (freshDeps deps retained) reverse transpose retained
    (seeds (freshDeps deps retained) retained nodes) (seeds_nodup _ _ _ unique)
    (seed_ready _ _ _) (fun n hs => ((fresh_mem _ _ _).mp ((seeds_mem _ _ _ _).mp hs).1).2)
    (fun d n hd => ((fresh_mem _ _ _).mp (reverseBound d n hd)).2)
    (freshNodes retained nodes).toFinset.card node (complete node hn)
  change (rankedFreshRun deps reverse retained nodes).ranks node =
    Reconcile.ConstructionLevels.levelRule (freshDeps deps retained) retained
      (rankedFreshRun deps reverse retained nodes).ranks node at eqn
  simpa only [Reconcile.ConstructionLevels.levelRule,
    freshDeps_agree deps retained node ((fresh_mem _ _ _).mp hn).2] using eqn

def scheduled (deps reverse : Dependencies) (retained : Finset Nat) (nodes : List Nat) :
    Option (List Nat) :=
  let result := rankedFreshRun deps reverse retained nodes
  if ∀ node ∈ freshNodes retained nodes, node ∈ result.queue.processed then
    some (Reconcile.ConstructionBuckets.scan
      (Reconcile.ConstructionBuckets.distribute result.ranks (freshNodes retained nodes) (fun _ => []))
      (nodes.length + 1) 0)
  else none

theorem scheduled_eq_schedule (deps reverse : Dependencies) (retained : Finset Nat)
    (nodes : List Nat) (unique : nodes.Nodup)
    (transpose : Transpose (freshDeps deps retained) reverse)
    (reverseBound : ∀ d n, n ∈ reverse d → n ∈ freshNodes retained nodes)
    (closed : ∀ node ∈ freshNodes retained nodes, ∀ d ∈ deps node,
      d ∈ retained ∨ d ∈ (freshNodes retained nodes).toFinset) :
    scheduled deps reverse retained nodes = schedule deps retained nodes := by
  unfold scheduled
  simp only [rankedFreshRun_queue]
  split
  · rename_i complete
    obtain ⟨order, hs⟩ := freshRun_success_of_complete deps reverse retained nodes unique
      transpose reverseBound complete
    rw [hs]
    congr 1
    exact (Reconcile.ConstructionBuckets.successful_schedule_eq_scan deps retained
      (rankedFreshRun deps reverse retained nodes).ranks nodes order closed
      (completed_equations deps reverse retained nodes unique transpose reverseBound complete) hs).symm
  · rename_i incomplete
    symm
    apply freshRun_missing_rejects deps reverse retained nodes unique transpose reverseBound
    push_neg at incomplete
    exact incomplete

def countedSchedule (deps reverse : Dependencies) (retained : Finset Nat) (nodes : List Nat) :
    Option (List Nat) :=
  let result := rankedFreshRun deps reverse retained nodes
  if result.queue.processed.length = (freshNodes retained nodes).length then
    some (Reconcile.ConstructionBuckets.scan
      (Reconcile.ConstructionBuckets.distribute result.ranks (freshNodes retained nodes) (fun _ => []))
      (nodes.length + 1) 0)
  else none

theorem countedSchedule_eq_schedule (deps reverse : Dependencies) (retained : Finset Nat)
    (nodes : List Nat) (unique : nodes.Nodup)
    (transpose : Transpose (freshDeps deps retained) reverse)
    (reverseBound : ∀ d n, n ∈ reverse d → n ∈ freshNodes retained nodes)
    (closed : ∀ node ∈ freshNodes retained nodes, ∀ d ∈ deps node,
      d ∈ retained ∨ d ∈ (freshNodes retained nodes).toFinset) :
    countedSchedule deps reverse retained nodes = schedule deps retained nodes := by
  rw [← scheduled_eq_schedule deps reverse retained nodes unique transpose reverseBound closed]
  simp only [countedSchedule, scheduled, rankedFreshRun_queue,
    freshRun_count_complete deps reverse retained nodes unique reverseBound]

end Reconcile.ConstructionScheduler
