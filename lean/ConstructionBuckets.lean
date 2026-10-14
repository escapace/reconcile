import ConstructionLevels

/-! Stable bucket distribution. Lists specify bucket contents; runtime array push
and indexed storage require the ordinary representation correspondence. -/
namespace Reconcile.ConstructionBuckets

abbrev Buckets := Nat → List Nat

def place (rank : Nat → Nat) (buckets : Buckets) (node : Nat) : Buckets :=
  fun level => if rank node = level then buckets level ++ [node] else buckets level

def distribute (rank : Nat → Nat) (nodes : List Nat) (initial : Buckets) : Buckets :=
  nodes.foldl (place rank) initial

theorem distribute_contents (rank : Nat → Nat) (nodes : List Nat)
    (initial : Buckets) (level : Nat) :
    distribute rank nodes initial level =
      initial level ++ nodes.filter (fun node => decide (rank node = level)) := by
  induction nodes generalizing initial with
  | nil => simp [distribute]
  | cons node rest ih =>
    change distribute rank rest (place rank initial node) level = _
    rw [ih]
    by_cases h : rank node = level <;> simp [place, h, List.append_assoc]

theorem empty_distribution (rank : Nat → Nat) (nodes : List Nat) (level : Nat) :
    distribute rank nodes (fun _ => []) level =
      nodes.filter (fun node => decide (rank node = level)) := by
  simp [distribute_contents]

def emit (buckets : Buckets) (levels : List Nat) : List Nat :=
  levels.flatMap buckets

theorem emit_distribution (rank : Nat → Nat) (nodes levels : List Nat) :
    emit (distribute rank nodes (fun _ => [])) levels =
      levels.flatMap (fun level => nodes.filter (fun node => decide (rank node = level))) := by
  unfold emit
  congr 1
  funext level
  exact empty_distribution rank nodes level

theorem distributed_membership (rank : Nat → Nat) (nodes : List Nat) (level node : Nat) :
    node ∈ distribute rank nodes (fun _ => []) level ↔
      node ∈ nodes ∧ rank node = level := by
  simp [empty_distribution]

theorem distributed_unique (rank : Nat → Nat) (nodes : List Nat) (level : Nat)
    (unique : nodes.Nodup) : (distribute rank nodes (fun _ => []) level).Nodup := by
  rw [empty_distribution]
  exact unique.filter _

theorem buckets_disjoint (rank : Nat → Nat) (nodes : List Nat) (left right : Nat)
    (different : left ≠ right) :
    List.Disjoint (distribute rank nodes (fun _ => []) left)
      (distribute rank nodes (fun _ => []) right) := by
  apply List.disjoint_left.mpr
  intro node hl hr
  have a := (distributed_membership rank nodes left node).mp hl
  have b := (distributed_membership rank nodes right node).mp hr
  exact different (a.2.symm.trans b.2)

theorem emitted_membership (rank : Nat → Nat) (nodes levels : List Nat) (node : Nat) :
    node ∈ emit (distribute rank nodes (fun _ => [])) levels ↔
      node ∈ nodes ∧ rank node ∈ levels := by
  rw [emit_distribution]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨level, hl, hn, he⟩
    exact ⟨hn, he.symm ▸ hl⟩
  · rintro ⟨hn, hl⟩
    exact ⟨rank node, hl, hn, rfl⟩

theorem bounded_emission_complete (rank : Nat → Nat) (nodes : List Nat) (bound node : Nat)
    (bounded : ∀ n ∈ nodes, rank n < bound) :
    node ∈ emit (distribute rank nodes (fun _ => [])) (List.range bound) ↔ node ∈ nodes := by
  rw [emitted_membership]
  simp only [List.mem_range]
  exact ⟨And.left, fun hn => ⟨hn, bounded node hn⟩⟩

def scan (buckets : Buckets) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, level => buckets level ++ scan buckets fuel (level + 1)

theorem scan_empty (fuel level : Nat) : scan (fun _ => []) fuel level = [] := by
  induction fuel generalizing level with
  | zero => rfl
  | succ fuel ih => simp [scan, ih]

theorem scan_congr_above (left right : Buckets) (fuel level : Nat)
    (agree : ∀ k, level ≤ k → left k = right k) :
    scan left fuel level = scan right fuel level := by
  induction fuel generalizing level with
  | zero => rfl
  | succ fuel ih =>
    simp only [scan, agree level (Nat.le_refl _)]
    rw [ih (level + 1) (fun k hk => agree k (by omega))]

theorem scan_filter_above (rank : Nat → Nat) (nodes : List Nat) (fuel level cutoff : Nat)
    (higher : cutoff < level) :
    scan (distribute rank (nodes.filter fun n => decide (cutoff < rank n)) (fun _ => [])) fuel level =
      scan (distribute rank nodes (fun _ => [])) fuel level := by
  apply scan_congr_above
  intro k hk
  simp only [empty_distribution, List.filter_filter]
  apply List.filter_congr
  intro node _
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem successful_buckets_eq_scan (rank : Nat → Nat) (fuel bound : Nat)
    (pending order : List Nat)
    (success : Reconcile.ConstructionLevels.bucketWaves rank fuel bound pending = some order) :
    order = scan (distribute rank pending (fun _ => [])) fuel (bound + 1) := by
  induction fuel generalizing bound pending order with
  | zero =>
    simp only [Reconcile.ConstructionLevels.bucketWaves] at success
    split at success <;> simp_all [scan]
  | succ fuel ih =>
    by_cases empty : pending = []
    · subst pending
      simp only [Reconcile.ConstructionLevels.bucketWaves, List.isEmpty_nil,
        ↓reduceIte, Option.some.injEq] at success
      subst order
      have he : distribute rank [] (fun _ => []) = (fun _ => []) := rfl
      rw [he, scan_empty]
    · simp only [Reconcile.ConstructionLevels.bucketWaves, List.isEmpty_iff,
        empty, ↓reduceIte] at success
      split at success
      · simp at success
      · obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some_iff.mp success
        rw [ih _ _ _ hr, scan_filter_above rank pending fuel (bound + 1 + 1) (bound + 1) (by omega)]
        simp only [scan, empty_distribution]

theorem scan_eq_emit (buckets : Buckets) (fuel level : Nat) :
    scan buckets fuel level = emit buckets (List.range' level fuel) := by
  induction fuel generalizing level with
  | zero => simp [scan, emit]
  | succ fuel ih => simp [scan, emit, List.range'_succ, ih]

theorem successful_schedule_eq_scan (deps : Reconcile.Construction.Dependencies)
    (retained : Finset Nat) (rank : Nat → Nat) (nodes order : List Nat)
    (closed : ∀ node ∈ Reconcile.ConstructionSetup.freshNodes retained nodes,
      ∀ d ∈ deps node, d ∈ retained ∨
        d ∈ (Reconcile.ConstructionSetup.freshNodes retained nodes).toFinset)
    (equations : ∀ node ∈ Reconcile.ConstructionSetup.freshNodes retained nodes,
      rank node = Reconcile.ConstructionLevels.levelRule deps retained rank node)
    (success : Reconcile.Construction.schedule deps retained nodes = some order) :
    order = scan (distribute rank (Reconcile.ConstructionSetup.freshNodes retained nodes)
      (fun _ => [])) (nodes.length + 1) 0 := by
  rw [Reconcile.ConstructionLevels.schedule_eq_level_buckets deps retained rank nodes
    closed equations] at success
  obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some_iff.mp success
  rw [successful_buckets_eq_scan rank nodes.length 0 _ _ hr]
  have pending :
      (Reconcile.ConstructionSetup.freshNodes retained nodes).filter
        (fun node => !(deps node).isEmpty) =
      (Reconcile.ConstructionSetup.freshNodes retained nodes).filter
        (fun node => decide (0 < rank node)) := by
    apply List.filter_congr
    intro node hn
    apply Bool.eq_iff_iff.mpr
    have hz := Reconcile.ConstructionLevels.level_zero_iff deps retained rank node
    rw [← equations node hn] at hz
    simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff, decide_eq_true_eq]
    exact ⟨fun h => Nat.pos_of_ne_zero (fun he => h (hz.mp he)),
      fun h he => (Nat.ne_of_gt h) (hz.mpr he)⟩
  rw [pending, scan_filter_above rank _ nodes.length 1 0 (by omega)]
  simp only [scan, empty_distribution]

end Reconcile.ConstructionBuckets
