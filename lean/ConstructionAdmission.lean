import ConstructionIncidence

/-! A ready notification is emitted on the positive-to-zero transition only.
These lemmas isolate the no-duplicate-admission obligation from queue ordering. -/
namespace Reconcile.ConstructionAdmission

open Reconcile.ConstructionIncidence

def admissions : Nat → Nat → Nat
  | 0, _ => 0
  | steps + 1, count => (if count = 1 then 1 else 0) + admissions steps (count - 1)

theorem admissions_exact (steps count : Nat) :
    admissions steps count = if 0 < count ∧ count ≤ steps then 1 else 0 := by
  induction steps generalizing count with
  | zero =>
    simp only [admissions]
    split_ifs <;> omega
  | succ steps ih =>
    cases count with
    | zero => simp [admissions, ih]
    | succ count =>
      cases count with
      | zero => simp [admissions, ih]
      | succ count =>
        simp only [admissions, ih]
        split_ifs <;> omega

theorem admissions_at_most_one (steps count : Nat) : admissions steps count ≤ 1 := by
  rw [admissions_exact]
  split_ifs <;> omega

theorem exhausted_admitted (count : Nat) (positive : 0 < count) :
    admissions count count = 1 := by
  simp [admissions_exact, positive]

theorem not_exhausted_not_admitted (steps count : Nat) (remaining : steps < count) :
    admissions steps count = 0 := by
  simp [admissions_exact, Nat.not_le.mpr remaining]

theorem initially_ready_not_readmitted (steps : Nat) : admissions steps 0 = 0 := by
  simp [admissions_exact]

-- Under the proved discharge bound, each actual decrement has a positive input.
theorem decrement_positive (count processed total : Nat)
    (within : total ≤ count) (pending : processed < total) : 0 < count - processed := by
  omega

theorem last_occurrence (count processed : Nat) (positive : processed < count) :
    count - processed = 1 ↔ count - (processed + 1) = 0 := by
  omega

def notifications : List Nat → Counters → List Nat
  | [], _ => []
  | parent :: rest, counters =>
    let later := notifications rest (tick counters parent)
    if counters parent = 1 then parent :: later else later

theorem notification_count (parents : List Nat) (counters : Counters) (node : Nat) :
    (notifications parents counters).count node = admissions (parents.count node) (counters node) := by
  induction parents generalizing counters with
  | nil => simp [notifications, admissions]
  | cons parent rest ih =>
    by_cases hp : parent = node
    · subst parent
      by_cases hc : counters node = 1
      · simp [notifications, hc, ih, tick, admissions, Nat.add_comm]
      · simp [notifications, hc, ih, tick, admissions]
    · by_cases hc : counters parent = 1 <;>
        simp [notifications, hc, ih, tick, hp, Ne.symm hp]

theorem notification_at_most_one (parents : List Nat) (counters : Counters) (node : Nat) :
    (notifications parents counters).count node ≤ 1 := by
  rw [notification_count]
  exact admissions_at_most_one _ _

theorem notifications_nodup (parents : List Nat) (counters : Counters) :
    (notifications parents counters).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  exact notification_at_most_one parents counters

theorem notified_iff (parents : List Nat) (counters : Counters) (node : Nat) :
    node ∈ notifications parents counters ↔
      0 < counters node ∧ counters node ≤ parents.count node := by
  rw [← List.count_pos_iff, notification_count, admissions_exact]
  split_ifs <;> simp_all

theorem initially_ready_disjoint (parents : List Nat) (counters : Counters)
    (node : Nat) (ready : counters node = 0) : node ∉ notifications parents counters := by
  simp [notified_iff, ready]

theorem seeded_frontier_nodup (seeds parents : List Nat) (counters : Counters)
    (unique : seeds.Nodup) (ready : ∀ node ∈ seeds, counters node = 0) :
    (seeds ++ notifications parents counters).Nodup := by
  apply List.nodup_append'.mpr
  refine ⟨unique, notifications_nodup parents counters, ?_⟩
  exact List.disjoint_left.mpr fun node hn hm =>
    initially_ready_disjoint parents counters node (ready node hn) hm

theorem notifications_subset (parents : List Nat) (counters : Counters) :
    notifications parents counters ⊆ parents := by
  intro node hn
  have h := (notified_iff parents counters node).mp hn
  exact List.count_pos_iff.mp (by omega)

theorem frontier_length_bound (seeds parents : List Nat) (counters : Counters)
    (vertices : Finset Nat) (unique : seeds.Nodup)
    (ready : ∀ node ∈ seeds, counters node = 0)
    (seedBound : ∀ node ∈ seeds, node ∈ vertices)
    (parentBound : ∀ node ∈ parents, node ∈ vertices) :
    (seeds ++ notifications parents counters).length ≤ vertices.card := by
  rw [← List.toFinset_card_of_nodup (seeded_frontier_nodup seeds parents counters unique ready)]
  apply Finset.card_le_card
  intro node hn
  rcases List.mem_append.mp (List.mem_toFinset.mp hn) with hs | hp
  · exact seedBound node hs
  · exact parentBound node (notifications_subset parents counters hp)

theorem notifications_append (first second : List Nat) (counters : Counters) :
    notifications (first ++ second) counters =
      notifications first counters ++ notifications second (first.foldl tick counters) := by
  induction first generalizing counters with
  | nil => simp [notifications]
  | cons parent rest ih =>
    simp only [List.cons_append, notifications, List.foldl_cons, ih]
    split_ifs <;> rfl

example : admissions 4 3 = 1 := by decide
example : admissions 8 0 = 0 := by decide

end Reconcile.ConstructionAdmission
