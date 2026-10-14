import ConstructionSetup

/-! Level equations for stable construction waves. These characterize ordering;
ConstructionRankUpdates connects the queue's max updates to these equations. -/
namespace Reconcile.ConstructionLevels

open Reconcile.Construction

def height (values : List Nat) : Nat := values.foldr max 0

theorem height_le (values : List Nat) (bound : Nat) :
    height values ≤ bound ↔ ∀ value ∈ values, value ≤ bound := by
  induction values with
  | nil => simp [height]
  | cons value rest ih => simp [height, ← ih]

def levelRule (deps : Dependencies) (retained : Finset Nat) (rank : Nat → Nat)
    (node : Nat) : Nat :=
  if (deps node).isEmpty then 0 else
    max 1 (height (((deps node).filter fun d => decide (d ∉ retained)).map
      fun d => rank d + 1))

theorem level_zero_iff (deps : Dependencies) (retained : Finset Nat)
    (rank : Nat → Nat) (node : Nat) :
    levelRule deps retained rank node = 0 ↔ deps node = [] := by
  by_cases h : deps node = []
  · simp [levelRule, h]
  · simp [levelRule, h]

theorem level_le_successor (deps : Dependencies) (retained : Finset Nat)
    (rank : Nat → Nat) (node bound : Nat) :
    levelRule deps retained rank node ≤ bound + 1 ↔
      ∀ d ∈ deps node, d ∉ retained → rank d ≤ bound := by
  by_cases h : deps node = []
  · simp [levelRule, h]
  · simp only [levelRule, List.isEmpty_iff, h, ↓reduceIte, max_le_iff,
      height_le, List.forall_mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · intro hs d hd hn
      exact Nat.le_of_add_le_add_right (hs.2 d ⟨hd, hn⟩)
    · intro hs
      exact ⟨by omega, fun d hd => Nat.add_le_add_right (hs d hd.1 hd.2) 1⟩

def knownThrough (retained vertices : Finset Nat) (rank : Nat → Nat) (bound : Nat) :
    Finset Nat := retained ∪ vertices.filter fun node => rank node ≤ bound

theorem ready_iff_level (deps : Dependencies) (retained vertices : Finset Nat)
    (rank : Nat → Nat) (node bound : Nat)
    (closed : ∀ d ∈ deps node, d ∈ retained ∨ d ∈ vertices) :
    ready deps (knownThrough retained vertices rank bound) node = true ↔
      levelRule deps retained rank node ≤ bound + 1 := by
  rw [level_le_successor]
  simp only [ready, List.all_eq_true, decide_eq_true_eq, knownThrough,
    Finset.mem_union, Finset.mem_filter]
  constructor
  · intro h d hd hn
    exact ((h d hd).resolve_left hn).2
  · intro h d hd
    by_cases hr : d ∈ retained
    · exact Or.inl hr
    · exact Or.inr ⟨(closed d hd).resolve_left hr, h d hd hr⟩

theorem stable_wave_eq_bucket (deps : Dependencies) (retained vertices : Finset Nat)
    (rank : Nat → Nat) (pending : List Nat) (bound : Nat)
    (closed : ∀ node ∈ pending, ∀ d ∈ deps node, d ∈ retained ∨ d ∈ vertices)
    (equations : ∀ node ∈ pending, rank node = levelRule deps retained rank node)
    (waiting : ∀ node ∈ pending, bound < rank node) :
    pending.filter (ready deps (knownThrough retained vertices rank bound)) =
      pending.filter (fun node => decide (rank node = bound + 1)) := by
  apply List.filter_congr
  intro node hn
  apply Bool.eq_iff_iff.mpr
  rw [ready_iff_level deps retained vertices rank node bound (closed node hn)]
  simp only [decide_eq_true_eq, ← equations node hn]
  have hw := waiting node hn
  omega

/-- The accumulator used when released dependencies raise a parent's level. -/
def accumulate (rank : Nat → Nat) (released : List Nat) (initial : Nat) : Nat :=
  released.foldl (fun level dependency => max level (rank dependency + 1)) initial

theorem accumulate_le (rank : Nat → Nat) (released : List Nat) (initial bound : Nat) :
    accumulate rank released initial ≤ bound ↔
      initial ≤ bound ∧ ∀ d ∈ released, rank d + 1 ≤ bound := by
  induction released generalizing initial with
  | nil => simp [accumulate]
  | cons dependency rest ih =>
    simp only [accumulate, List.foldl_cons] at *
    rw [ih]
    simp only [max_le_iff, List.mem_cons, forall_eq_or_imp]
    tauto

theorem accumulate_membership_congr (rank : Nat → Nat) (left right : List Nat)
    (initial : Nat) (same : ∀ d, d ∈ left ↔ d ∈ right) :
    accumulate rank left initial = accumulate rank right initial := by
  apply Nat.le_antisymm
  · apply (accumulate_le rank left initial _).mpr
    have h := (accumulate_le rank right initial _).mp (Nat.le_refl _)
    exact ⟨h.1, fun d hd => h.2 d ((same d).mp hd)⟩
  · apply (accumulate_le rank right initial _).mpr
    have h := (accumulate_le rank left initial _).mp (Nat.le_refl _)
    exact ⟨h.1, fun d hd => h.2 d ((same d).mpr hd)⟩

theorem accumulate_height (rank : Nat → Nat) (released : List Nat) (initial : Nat) :
    accumulate rank released initial = max initial (height (released.map fun d => rank d + 1)) := by
  apply Nat.le_antisymm
  · apply (accumulate_le rank released initial _).mpr
    constructor
    · exact le_max_left _ _
    · intro d hd
      exact le_trans ((height_le _ _).mp (Nat.le_refl _) _ (List.mem_map.mpr ⟨d, hd, rfl⟩))
        (le_max_right _ _)
  · rw [max_le_iff]
    have h := (accumulate_le rank released initial _).mp (Nat.le_refl _)
    exact ⟨h.1, (height_le _ _).mpr (by simpa using h.2)⟩

theorem accumulate_eq_rule (deps : Dependencies) (retained : Finset Nat)
    (rank : Nat → Nat) (node : Nat) (released : List Nat)
    (complete : ∀ d, d ∈ released ↔ d ∈ deps node ∧ d ∉ retained) :
    accumulate rank released (if (deps node).isEmpty then 0 else 1) =
      levelRule deps retained rank node := by
  have same : ∀ d, d ∈ released ↔
      d ∈ (deps node).filter (fun d => decide (d ∉ retained)) := by
    intro d
    simpa using complete d
  rw [accumulate_membership_congr rank released _ _ same, accumulate_height]
  by_cases empty : deps node = []
  · simp [levelRule, empty, height]
  · simp [levelRule, empty]

theorem accumulate_rank_congr (left right : Nat → Nat) (released : List Nat)
    (initial : Nat) (stable : ∀ d ∈ released, left d = right d) :
    accumulate left released initial = accumulate right released initial := by
  induction released generalizing initial with
  | nil => rfl
  | cons d rest ih =>
    simp only [accumulate, List.foldl_cons]
    rw [stable d (by simp)]
    exact ih _ (fun child hc => stable child (by simp [hc]))

theorem knownThrough_successor (retained vertices : Finset Nat) (rank : Nat → Nat)
    (bound : Nat) :
    knownThrough retained vertices rank bound ∪
      (vertices.filter fun node => rank node = bound + 1) =
      knownThrough retained vertices rank (bound + 1) := by
  ext node
  simp only [knownThrough, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro ((hr | ⟨hv, hl⟩) | ⟨hv, hl⟩)
    · exact Or.inl hr
    · exact Or.inr ⟨hv, by omega⟩
    · exact Or.inr ⟨hv, by omega⟩
  · rintro (hr | ⟨hv, hl⟩)
    · exact Or.inl (Or.inl hr)
    · by_cases h : rank node ≤ bound
      · exact Or.inl (Or.inr ⟨hv, h⟩)
      · exact Or.inr ⟨hv, by omega⟩

theorem stable_waiting_eq (deps : Dependencies) (retained vertices : Finset Nat)
    (rank : Nat → Nat) (pending : List Nat) (bound : Nat)
    (closed : ∀ node ∈ pending, ∀ d ∈ deps node, d ∈ retained ∨ d ∈ vertices)
    (equations : ∀ node ∈ pending, rank node = levelRule deps retained rank node) :
    pending.filter (fun node => !ready deps (knownThrough retained vertices rank bound) node) =
      pending.filter (fun node => decide (bound + 1 < rank node)) := by
  apply List.filter_congr
  intro node hn
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  have h := ready_iff_level deps retained vertices rank node bound (closed node hn)
  rw [← equations node hn] at h
  cases hr : ready deps (knownThrough retained vertices rank bound) node <;> simp_all

theorem stable_wave_advances_known (deps : Dependencies) (retained vertices : Finset Nat)
    (rank : Nat → Nat) (pending : List Nat) (bound : Nat)
    (closed : ∀ node ∈ pending, ∀ d ∈ deps node, d ∈ retained ∨ d ∈ vertices)
    (equations : ∀ node ∈ pending, rank node = levelRule deps retained rank node)
    (pendingExact : ∀ node, node ∈ pending ↔ node ∈ vertices ∧ bound < rank node) :
    knownThrough retained vertices rank bound ∪
      (pending.filter (ready deps (knownThrough retained vertices rank bound))).toFinset =
      knownThrough retained vertices rank (bound + 1) := by
  rw [stable_wave_eq_bucket deps retained vertices rank pending bound closed equations
    (fun node hn => ((pendingExact node).mp hn).2)]
  have bucket : (pending.filter (fun node => decide (rank node = bound + 1))).toFinset =
      vertices.filter (fun node => rank node = bound + 1) := by
    ext node
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq,
      Finset.mem_filter, pendingExact]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, by omega⟩, h.2⟩
  rw [bucket, knownThrough_successor]

theorem stable_waiting_membership (deps : Dependencies) (retained vertices : Finset Nat)
    (rank : Nat → Nat) (pending : List Nat) (bound : Nat)
    (closed : ∀ node ∈ pending, ∀ d ∈ deps node, d ∈ retained ∨ d ∈ vertices)
    (equations : ∀ node ∈ pending, rank node = levelRule deps retained rank node)
    (pendingExact : ∀ node, node ∈ pending ↔ node ∈ vertices ∧ bound < rank node)
    (node : Nat) :
    node ∈ pending.filter (fun n => !ready deps (knownThrough retained vertices rank bound) n) ↔
      node ∈ vertices ∧ bound + 1 < rank node := by
  rw [stable_waiting_eq deps retained vertices rank pending bound closed equations]
  simp only [List.mem_filter, decide_eq_true_eq, pendingExact]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · exact fun h => ⟨⟨h.1, by omega⟩, h.2⟩

theorem initial_shells_eq_bucket (deps : Dependencies) (retained : Finset Nat)
    (rank : Nat → Nat) (fresh : List Nat)
    (equations : ∀ node ∈ fresh, rank node = levelRule deps retained rank node) :
    fresh.filter (fun node => (deps node).isEmpty) =
      fresh.filter (fun node => decide (rank node = 0)) := by
  apply List.filter_congr
  intro node hn
  apply Bool.eq_iff_iff.mpr
  simp only [List.isEmpty_iff, decide_eq_true_eq, equations node hn,
    level_zero_iff]

theorem initial_known_eq (deps : Dependencies) (retained : Finset Nat)
    (rank : Nat → Nat) (fresh : List Nat)
    (equations : ∀ node ∈ fresh, rank node = levelRule deps retained rank node) :
    retained ∪ (fresh.filter (fun node => (deps node).isEmpty)).toFinset =
      knownThrough retained fresh.toFinset rank 0 := by
  rw [initial_shells_eq_bucket deps retained rank fresh equations]
  ext node
  simp [knownThrough]

theorem initial_pending_membership (deps : Dependencies) (retained : Finset Nat)
    (rank : Nat → Nat) (fresh : List Nat)
    (equations : ∀ node ∈ fresh, rank node = levelRule deps retained rank node)
    (node : Nat) :
    node ∈ fresh.filter (fun n => !(deps n).isEmpty) ↔
      node ∈ fresh.toFinset ∧ 0 < rank node := by
  simp only [List.mem_filter, List.mem_toFinset]
  constructor
  · rintro ⟨hn, he⟩
    refine ⟨hn, ?_⟩
    have hz := level_zero_iff deps retained rank node
    rw [← equations node hn] at hz
    simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff] at he
    exact Nat.pos_of_ne_zero (fun h => he (hz.mp h))
  · rintro ⟨hn, hr⟩
    refine ⟨hn, ?_⟩
    have hz := level_zero_iff deps retained rank node
    rw [← equations node hn] at hz
    simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff]
    exact fun h => (Nat.ne_of_gt hr) (hz.mpr h)

/-- Specification bridge, not the linear-time counting-bucket implementation. -/
def bucketWaves (rank : Nat → Nat) : Nat → Nat → List Nat → Option (List Nat)
  | 0, _, pending => if pending.isEmpty then some [] else none
  | fuel + 1, bound, pending =>
    if pending.isEmpty then some [] else
      let bucket := pending.filter fun node => decide (rank node = bound + 1)
      if bucket.isEmpty then none else
        (bucketWaves rank fuel (bound + 1)
          (pending.filter fun node => decide (bound + 1 < rank node))).map (bucket ++ ·)

theorem waves_eq_bucketWaves (deps : Dependencies) (retained vertices : Finset Nat)
    (rank : Nat → Nat) (fuel bound : Nat) (pending : List Nat)
    (closed : ∀ node ∈ pending, ∀ d ∈ deps node, d ∈ retained ∨ d ∈ vertices)
    (equations : ∀ node ∈ pending, rank node = levelRule deps retained rank node)
    (pendingExact : ∀ node, node ∈ pending ↔ node ∈ vertices ∧ bound < rank node) :
    waves deps fuel (knownThrough retained vertices rank bound) pending =
      bucketWaves rank fuel bound pending := by
  induction fuel generalizing bound pending with
  | zero => rfl
  | succ fuel ih =>
    have hw := stable_wave_eq_bucket deps retained vertices rank pending bound closed
      equations (fun node hn => ((pendingExact node).mp hn).2)
    have hk := stable_wave_advances_known deps retained vertices rank pending bound
      closed equations pendingExact
    have ht := stable_waiting_eq deps retained vertices rank pending bound closed equations
    have hp := stable_waiting_membership deps retained vertices rank pending bound
      closed equations pendingExact
    simp only [waves, bucketWaves]
    rw [hw] at hk ⊢
    rw [hk, ht]
    split
    · rfl
    · split
      · rfl
      · congr 1
        apply ih
        · intro node hn
          exact closed node (List.mem_filter.mp hn).1
        · intro node hn
          exact equations node (List.mem_filter.mp hn).1
        · intro node
          rw [ht] at hp
          exact hp node

theorem schedule_eq_level_buckets (deps : Dependencies) (retained : Finset Nat)
    (rank : Nat → Nat) (nodes : List Nat)
    (closed : ∀ node ∈ Reconcile.ConstructionSetup.freshNodes retained nodes,
      ∀ d ∈ deps node, d ∈ retained ∨
        d ∈ (Reconcile.ConstructionSetup.freshNodes retained nodes).toFinset)
    (equations : ∀ node ∈ Reconcile.ConstructionSetup.freshNodes retained nodes,
      rank node = levelRule deps retained rank node) :
    schedule deps retained nodes =
      (bucketWaves rank nodes.length 0
        ((Reconcile.ConstructionSetup.freshNodes retained nodes).filter
          fun node => !(deps node).isEmpty)).map
        (((Reconcile.ConstructionSetup.freshNodes retained nodes).filter
          fun node => decide (rank node = 0)) ++ ·) := by
  let fresh := Reconcile.ConstructionSetup.freshNodes retained nodes
  change (waves deps nodes.length
    (retained ∪ (fresh.filter fun node => (deps node).isEmpty).toFinset)
    (fresh.filter fun node => !(deps node).isEmpty)).map _ = _
  rw [initial_known_eq deps retained rank fresh equations]
  rw [waves_eq_bucketWaves deps retained fresh.toFinset rank nodes.length 0
    (fresh.filter fun node => !(deps node).isEmpty)
    (fun node hn => closed node (List.mem_filter.mp hn).1)
    (fun node hn => equations node (List.mem_filter.mp hn).1)
    (initial_pending_membership deps retained rank fresh equations)]
  have shells := initial_shells_eq_bucket deps retained rank fresh equations
  simpa only [fresh, Reconcile.ConstructionSetup.freshNodes] using
    congrArg (fun shells => (bucketWaves rank nodes.length 0
      (fresh.filter fun node => !(deps node).isEmpty)).map (shells ++ ·)) shells

end Reconcile.ConstructionLevels
