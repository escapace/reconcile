import Graph.ConstructionLevels

/-! Pointwise semantics of the reverse-incidence level update. The dependency's
level is read before processing its parents, as in the current runtime loop. -/
namespace Reconcile.ConstructionRankUpdates

open Reconcile.ConstructionIncidence

abbrev Ranks := Nat → Nat

def raiseParent (contribution : Nat) (ranks : Ranks) (parent : Nat) : Ranks :=
  fun node => if node = parent then max (ranks node) contribution else ranks node

def raiseParents (parents : List Nat) (contribution : Nat) (ranks : Ranks) : Ranks :=
  parents.foldl (raiseParent contribution) ranks

theorem raiseParents_exact (parents : List Nat) (contribution : Nat)
    (ranks : Ranks) (node : Nat) :
    raiseParents parents contribution ranks node =
      if node ∈ parents then max (ranks node) contribution else ranks node := by
  induction parents generalizing ranks with
  | nil => simp [raiseParents]
  | cons parent rest ih =>
    change raiseParents rest contribution (raiseParent contribution ranks parent) node = _
    rw [ih]
    by_cases hp : node = parent <;> by_cases hr : node ∈ rest <;>
      simp [raiseParent, hp, hr]

def releaseRank (reverse : Adjacency) (ranks : Ranks) (dependency : Nat) : Ranks :=
  raiseParents (reverse dependency) (ranks dependency + 1) ranks

theorem releaseRank_exact (reverse : Adjacency) (ranks : Ranks) (dependency node : Nat) :
    releaseRank reverse ranks dependency node =
      if node ∈ reverse dependency then max (ranks node) (ranks dependency + 1)
      else ranks node := by
  exact raiseParents_exact _ _ _ _

theorem transpose_membership (forward reverse : Adjacency)
    (transpose : Transpose forward reverse) (parent dependency : Nat) :
    parent ∈ reverse dependency ↔ dependency ∈ forward parent := by
  have h := transpose parent dependency
  rw [← List.count_pos_iff, ← List.count_pos_iff, h]

theorem releaseRank_forward (forward reverse : Adjacency)
    (transpose : Transpose forward reverse) (ranks : Ranks) (dependency node : Nat) :
    releaseRank reverse ranks dependency node =
      if dependency ∈ forward node then max (ranks node) (ranks dependency + 1)
      else ranks node := by
  simp only [releaseRank_exact, transpose_membership forward reverse transpose]

theorem releaseRank_preserves (forward reverse : Adjacency)
    (transpose : Transpose forward reverse) (ranks : Ranks) (dependency node : Nat)
    (absent : dependency ∉ forward node) :
    releaseRank reverse ranks dependency node = ranks node := by
  simp [releaseRank_forward forward reverse transpose, absent]

theorem ready_rank_stable (forward reverse : Adjacency)
    (transpose : Transpose forward reverse) (ranks : Ranks) (known : Finset Nat)
    (dependency node : Nat) (fresh : dependency ∉ known)
    (ready : ∀ d ∈ forward node, d ∈ known) :
    releaseRank reverse ranks dependency node = ranks node := by
  apply releaseRank_preserves forward reverse transpose
  exact fun hd => fresh (ready dependency hd)

theorem releaseRank_bound (reverse : Adjacency) (ranks : Ranks) (dependency bound : Nat)
    (bounded : ∀ node, ranks node ≤ bound) :
    ∀ node, releaseRank reverse ranks dependency node ≤ bound + 1 := by
  intro node
  rw [releaseRank_exact]
  split
  · exact max_le (Nat.le_succ_of_le (bounded node))
      (Nat.add_le_add_right (bounded dependency) 1)
  · exact Nat.le_succ_of_le (bounded node)

theorem releaseSequence_bound (reverse : Adjacency) (ranks : Ranks)
    (dependencies : List Nat) (bound : Nat) (bounded : ∀ node, ranks node ≤ bound) :
    ∀ node, dependencies.foldl (releaseRank reverse) ranks node ≤ bound + dependencies.length := by
  induction dependencies generalizing ranks bound with
  | nil => simpa using bounded
  | cons dependency rest ih =>
    have h := ih (releaseRank reverse ranks dependency) (bound + 1)
      (releaseRank_bound reverse ranks dependency bound bounded)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem releaseSequence_preserves (forward reverse : Adjacency)
    (transpose : Transpose forward reverse) (ranks : Ranks) (dependencies : List Nat)
    (node : Nat) (absent : ∀ d ∈ dependencies, d ∉ forward node) :
    dependencies.foldl (releaseRank reverse) ranks node = ranks node := by
  induction dependencies generalizing ranks with
  | nil => rfl
  | cons dependency rest ih =>
    rw [List.foldl_cons, ih _ (fun d hd => absent d (by simp [hd]))]
    exact releaseRank_preserves forward reverse transpose ranks dependency node
      (absent dependency (by simp))

theorem ready_rank_stable_sequence (forward reverse : Adjacency)
    (transpose : Transpose forward reverse) (ranks : Ranks) (known : Finset Nat)
    (dependencies : List Nat) (node : Nat)
    (fresh : ∀ d ∈ dependencies, d ∉ known)
    (ready : ∀ d ∈ forward node, d ∈ known) :
    dependencies.foldl (releaseRank reverse) ranks node = ranks node := by
  apply releaseSequence_preserves forward reverse transpose
  intro d hd hforward
  exact fresh d hd (ready d hforward)

/-- Earlier safe nodes cannot depend on a later, distinct release. -/
theorem safe_dependency_precedes (forward : Adjacency) (known : Finset Nat)
    (front : List Nat) (dependency node : Nat)
    (safe : Reconcile.Construction.Safe forward known front)
    (fresh : dependency ∉ known) (later : dependency ∉ front) (member : node ∈ front) :
    dependency ∉ forward node := by
  induction front generalizing known with
  | nil => simp at member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | hm
    · exact fun hd => fresh (safe.1 dependency hd)
    · apply ih (insert head known) safe.2
      · simp only [Finset.mem_insert, not_or]
        exact ⟨fun he => later (by simp [he]), fresh⟩
      · exact fun hd => later (by simp [hd])
      · exact hm

theorem safe_front_ranks_stable (forward reverse : Adjacency)
    (transpose : Transpose forward reverse) (ranks : Ranks) (known : Finset Nat)
    (front later : List Nat) (safe : Reconcile.Construction.Safe forward known front)
    (fresh : ∀ d ∈ later, d ∉ known) (disjoint : List.Disjoint front later)
    (node : Nat) (member : node ∈ front) :
    later.foldl (releaseRank reverse) ranks node = ranks node := by
  apply releaseSequence_preserves forward reverse transpose
  intro d hd
  apply safe_dependency_precedes forward known front d node safe (fresh d hd)
  · exact fun hf => (List.disjoint_left.mp disjoint hf) hd
  · exact member

/-- Reference updates using a fixed table of dependency contributions. -/
def releaseWith (reverse : Adjacency) (contributions : Ranks)
    (ranks : Ranks) (dependency : Nat) : Ranks :=
  raiseParents (reverse dependency) (contributions dependency + 1) ranks

theorem releaseWith_accumulate (forward reverse : Adjacency)
    (transpose : Transpose forward reverse) (contributions ranks : Ranks)
    (released : List Nat) (node : Nat) :
    released.foldl (releaseWith reverse contributions) ranks node =
      Reconcile.ConstructionLevels.accumulate contributions
        (released.filter fun d => decide (d ∈ forward node)) (ranks node) := by
  induction released generalizing ranks with
  | nil => rfl
  | cons dependency rest ih =>
    rw [List.foldl_cons, ih]
    have update : releaseWith reverse contributions ranks dependency node =
        if dependency ∈ forward node then max (ranks node) (contributions dependency + 1)
        else ranks node := by
      simp only [releaseWith, raiseParents_exact, transpose_membership forward reverse transpose]
    by_cases hd : dependency ∈ forward node <;>
      simp [update, hd, Reconcile.ConstructionLevels.accumulate]

theorem releaseWith_eq_rule (forward reverse : Adjacency)
    (transpose : Transpose forward reverse) (retained : Finset Nat)
    (contributions : Ranks) (released : List Nat) (node : Nat)
    (complete : ∀ d ∈ forward node, d ∈ released ↔ d ∉ retained) :
    released.foldl (releaseWith reverse contributions)
      (fun n => if (forward n).isEmpty then 0 else 1) node =
      Reconcile.ConstructionLevels.levelRule forward retained contributions node := by
  rw [releaseWith_accumulate forward reverse transpose]
  apply Reconcile.ConstructionLevels.accumulate_eq_rule
  intro d
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hr, hf⟩
    exact ⟨hf, (complete d hf).mp hr⟩
  · rintro ⟨hf, hn⟩
    exact ⟨(complete d hf).mpr hn, hf⟩

theorem dynamic_eq_fixed (reverse : Adjacency) (contributions ranks : Ranks)
    (released : List Nat)
    (stable : ∀ front dependency rest, released = front ++ dependency :: rest →
      front.foldl (releaseRank reverse) ranks dependency = contributions dependency) :
    released.foldl (releaseRank reverse) ranks =
      released.foldl (releaseWith reverse contributions) ranks := by
  induction released generalizing ranks with
  | nil => rfl
  | cons dependency rest ih =>
    have hd := stable [] dependency rest rfl
    simp only [List.foldl_nil] at hd
    have step : releaseRank reverse ranks dependency =
        releaseWith reverse contributions ranks dependency := by
      simp only [releaseRank, releaseWith, hd]
    rw [List.foldl_cons, List.foldl_cons, ← step]
    apply ih
    intro front child tail he
    have hs := stable (dependency :: front) child tail (by simp [he])
    simpa only [List.foldl_cons] using hs

theorem safe_after_front (forward : Adjacency) (known : Finset Nat) (front rest : List Nat)
    (safe : Reconcile.Construction.Safe forward known (front ++ rest)) :
    Reconcile.Construction.Safe forward (known ∪ front.toFinset) rest := by
  induction front generalizing known with
  | nil => simpa using safe
  | cons head tail ih =>
    have h := ih (insert head known) safe.2
    simpa [Finset.insert_union, Finset.union_insert] using h

theorem rank_final_at_release (forward reverse : Adjacency)
    (transpose : Transpose forward reverse) (ranks : Ranks) (known : Finset Nat)
    (front : List Nat) (dependency : Nat) (rest : List Nat)
    (safe : Reconcile.Construction.Safe forward known (front ++ dependency :: rest))
    (unique : (front ++ dependency :: rest).Nodup)
    (fresh : ∀ d ∈ front ++ dependency :: rest, d ∉ known) :
    front.foldl (releaseRank reverse) ranks dependency =
      (front ++ dependency :: rest).foldl (releaseRank reverse) ranks dependency := by
  have ready := (safe_after_front forward known front (dependency :: rest) safe).1
  have disjoint := (List.nodup_append'.mp unique).2.2
  have absent : ∀ d ∈ dependency :: rest, d ∉ known ∪ front.toFinset := by
    intro d hd
    simp only [Finset.mem_union, List.mem_toFinset, not_or]
    exact ⟨fresh d (List.mem_append_right _ hd),
      fun hf => (List.disjoint_left.mp disjoint hf) hd⟩
  rw [List.foldl_append]
  exact (ready_rank_stable_sequence forward reverse transpose _ _ _ dependency absent ready).symm

theorem safe_dynamic_eq_final (forward reverse : Adjacency)
    (transpose : Transpose forward reverse) (ranks : Ranks) (known : Finset Nat)
    (released : List Nat) (safe : Reconcile.Construction.Safe forward known released)
    (unique : released.Nodup) (fresh : ∀ d ∈ released, d ∉ known) :
    released.foldl (releaseRank reverse) ranks =
      released.foldl (releaseWith reverse (released.foldl (releaseRank reverse) ranks)) ranks := by
  apply dynamic_eq_fixed
  intro front dependency rest he
  subst released
  exact rank_final_at_release forward reverse transpose ranks known front dependency rest
    safe unique fresh

theorem safe_release_level_equation (forward reverse : Adjacency)
    (transpose : Transpose forward reverse) (known : Finset Nat) (released : List Nat)
    (safe : Reconcile.Construction.Safe forward known released) (unique : released.Nodup)
    (fresh : ∀ d ∈ released, d ∉ known) (node : Nat)
    (complete : ∀ d ∈ forward node, d ∈ released ↔ d ∉ known) :
    let ranks := released.foldl (releaseRank reverse)
      (fun n => if (forward n).isEmpty then 0 else 1)
    ranks node = Reconcile.ConstructionLevels.levelRule forward known ranks node := by
  dsimp only
  have fixed := safe_dynamic_eq_final forward reverse transpose
    (fun n => if (forward n).isEmpty then 0 else 1) known released safe unique fresh
  calc
    _ = _ := congrFun fixed node
    _ = _ := releaseWith_eq_rule forward reverse transpose known _ released node complete

theorem queue_processed_level_equation (forward reverse : Adjacency)
    (transpose : Transpose forward reverse) (known : Finset Nat) (seeds : List Nat)
    (unique : seeds.Nodup)
    (ready : ∀ node ∈ seeds, Reconcile.ConstructionFrontier.outstanding (forward node) known = 0)
    (seedFresh : ∀ node ∈ seeds, node ∉ known)
    (reverseFresh : ∀ dependency node, node ∈ reverse dependency → node ∉ known)
    (fuel node : Nat)
    (member : node ∈ (Reconcile.ConstructionCompletion.runQueue reverse fuel
      ⟨[], seeds, fun n => Reconcile.ConstructionFrontier.outstanding (forward n) known⟩).processed) :
    let processed := (Reconcile.ConstructionCompletion.runQueue reverse fuel
      ⟨[], seeds, fun n => Reconcile.ConstructionFrontier.outstanding (forward n) known⟩).processed
    let ranks := processed.foldl (releaseRank reverse)
      (fun n => if (forward n).isEmpty then 0 else 1)
    ranks node = Reconcile.ConstructionLevels.levelRule forward known ranks node := by
  let initial : Reconcile.ConstructionCompletion.QueueState :=
    ⟨[], seeds, fun n => Reconcile.ConstructionFrontier.outstanding (forward n) known⟩
  let state := Reconcile.ConstructionCompletion.runQueue reverse fuel initial
  have invariant := Reconcile.ConstructionCompletion.run_preserves_invariant reverse seeds _
    fuel initial (Reconcile.ConstructionCompletion.initial_queue_invariant _ _ _)
  have fresh : ∀ n ∈ state.processed, n ∉ known := by
    intro n hn
    exact Reconcile.ConstructionCompletion.frontier_fresh reverse seeds _ state invariant
      known seedFresh reverseFresh n (List.mem_append_left _ hn)
  apply safe_release_level_equation forward reverse transpose known state.processed
    (Reconcile.ConstructionCompletion.initial_run_safe forward reverse transpose known seeds
      unique ready seedFresh reverseFresh fuel)
    (Reconcile.ConstructionCompletion.processed_nodup reverse seeds _ state invariant unique ready)
    fresh node
  have counts := Reconcile.ConstructionCompletion.processed_counter_exact forward reverse
    transpose known seeds state invariant unique ready fresh
  have zero := Reconcile.ConstructionCompletion.frontier_counter_zero reverse seeds _ state
    invariant ready node (List.mem_append_left _ member)
  have hc := congrFun counts node
  have dependencies := (Reconcile.ConstructionFrontier.outstanding_zero_iff _ _).mp
    (hc.symm.trans zero)
  intro d hd
  constructor
  · exact fresh d
  · intro hn
    exact List.mem_toFinset.mp ((Finset.mem_union.mp (dependencies d hd)).resolve_left hn)

open Reconcile.ConstructionCompletion

structure RankedQueue where
  queue : QueueState
  ranks : Ranks

def runRanked (reverse : Adjacency) : Nat → RankedQueue → RankedQueue
  | 0, state => state
  | fuel + 1, state => match state.queue.pending with
    | [] => state
    | head :: tail => runRanked reverse fuel
        ⟨processHead reverse state.queue.processed head tail state.queue.counters,
          releaseRank reverse state.ranks head⟩

theorem runRanked_queue (reverse : Adjacency) (fuel : Nat) (state : RankedQueue) :
    (runRanked reverse fuel state).queue = runQueue reverse fuel state.queue := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    rcases state with ⟨⟨processed, pending, counters⟩, ranks⟩
    cases pending with
    | nil => rfl
    | cons head tail => exact ih _

theorem runRanked_fold (reverse : Adjacency) (initial : Ranks) (fuel : Nat)
    (state : RankedQueue)
    (h : state.ranks = state.queue.processed.foldl (releaseRank reverse) initial) :
    (runRanked reverse fuel state).ranks =
      (runRanked reverse fuel state).queue.processed.foldl (releaseRank reverse) initial := by
  induction fuel generalizing state with
  | zero => exact h
  | succ fuel ih =>
    rcases state with ⟨⟨processed, pending, counters⟩, ranks⟩
    cases pending with
    | nil => exact h
    | cons head tail =>
      apply ih
      simpa only [processHead, List.foldl_append, List.foldl_cons, List.foldl_nil] using
        congrArg (fun table => releaseRank reverse table head) h

theorem initial_ranked_fold (reverse : Adjacency) (seeds : List Nat)
    (counters : Counters) (initial : Ranks) (fuel : Nat) :
    (runRanked reverse fuel ⟨⟨[], seeds, counters⟩, initial⟩).ranks =
      (runQueue reverse fuel ⟨[], seeds, counters⟩).processed.foldl (releaseRank reverse) initial := by
  rw [runRanked_fold reverse initial fuel _ rfl, runRanked_queue]

theorem ranked_queue_level_equation (forward reverse : Adjacency)
    (transpose : Transpose forward reverse) (known : Finset Nat) (seeds : List Nat)
    (unique : seeds.Nodup)
    (ready : ∀ n ∈ seeds, Reconcile.ConstructionFrontier.outstanding (forward n) known = 0)
    (seedFresh : ∀ n ∈ seeds, n ∉ known)
    (reverseFresh : ∀ d n, n ∈ reverse d → n ∉ known) (fuel node : Nat)
    (member : node ∈ (runQueue reverse fuel
      ⟨[], seeds, fun n => Reconcile.ConstructionFrontier.outstanding (forward n) known⟩).processed) :
    let result := runRanked reverse fuel
      ⟨⟨[], seeds, fun n => Reconcile.ConstructionFrontier.outstanding (forward n) known⟩,
        fun n => if (forward n).isEmpty then 0 else 1⟩
    result.ranks node = Reconcile.ConstructionLevels.levelRule forward known result.ranks node := by
  dsimp only
  rw [initial_ranked_fold]
  exact queue_processed_level_equation forward reverse transpose known seeds unique ready
    seedFresh reverseFresh fuel node member

end Reconcile.ConstructionRankUpdates
