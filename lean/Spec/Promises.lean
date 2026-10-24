import Spec.Reconcile
import Spec.Produce

/-!
# The promises: theorems about the reference models

Each theorem states a promise the documentation makes, about the executable reference the random
differential bridge compares with the runtime. The bridge carries the promise to the runtime; the
theorem shows the reference keeps it on every input, not only the generated ones.

- `retainPrefix`: the retained prefix is a prefix of `next`'s order, a subsequence of `cur`'s, and
  the longest such prefix. The keys or entries outside it are the moves (`moves_minimal`,
  `collection_moves_minimal`).
- `reconcile`: a getter of `current` runs at most twice, and at most once when nothing is written
  (`get_bound`, `read_once_before_write`); the number of decision passes is bounded by the number
  of node pairs (`passes_le`): no plan search.
- `produce`: a current object is kept exactly when its subtree is unchanged, and the kept set is
  the greatest such set (`reuse_iff`, `changed_new`).
-/

namespace Reconcile.Spec.Reconcile

open Reconcile.Spec

/-! ## Retention -/

section Retention

variable {K : Type} [DecidableEq K]

theorem isSubseq_iff (l m : List K) : isSubseq l m = true ↔ l.Sublist m := by
  induction m generalizing l with
  | nil =>
    cases l with
    | nil => simp [isSubseq]
    | cons a as => simp [isSubseq]
  | cons b bs ih =>
    cases l with
    | nil => simp [isSubseq]
    | cons a as =>
      by_cases h : a = b
      · subst h
        simp [isSubseq, ih]
      · simp only [isSubseq, h, if_false, ih]
        constructor
        · intro hs
          exact hs.cons b
        · intro hs
          rcases List.sublist_cons_iff.mp hs with hs | ⟨r, hr, _⟩
          · exact hs
          · cases hr
            exact absurd rfl h

theorem retainLength_le (cur next : List K) (k : Nat) : retainLength cur next k ≤ k := by
  induction k with
  | zero => simp [retainLength]
  | succ k ih =>
    simp only [retainLength]
    split
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le ih

theorem retainLength_subseq (cur next : List K) (k : Nat) :
    isSubseq (next.take (retainLength cur next k)) cur = true := by
  induction k with
  | zero => simp [retainLength, isSubseq]
  | succ k ih =>
    simp only [retainLength]
    split
    · assumption
    · exact ih

theorem retainLength_maximal (cur next : List K) (k j : Nat) (hj : j ≤ k)
    (h : isSubseq (next.take j) cur = true) : j ≤ retainLength cur next k := by
  induction k with
  | zero => exact hj
  | succ k ih =>
    simp only [retainLength]
    split
    · exact hj
    · rename_i hk
      apply ih
      rcases Nat.lt_or_eq_of_le hj with hlt | heq
      · exact Nat.le_of_lt_succ hlt
      · subst heq
        exact absurd h hk

/-- The retained prefix is a prefix of `next`'s order. -/
theorem retainPrefix_prefix (cur next : List K) : (retainPrefix cur next).IsPrefix next :=
  List.take_prefix _ _

/-- The retained prefix is a subsequence of `cur`'s order: nothing in it moves. -/
theorem retainPrefix_sublist (cur next : List K) : (retainPrefix cur next).Sublist cur :=
  (isSubseq_iff _ _).mp (retainLength_subseq cur next next.length)

/-- No longer prefix of `next` is a subsequence of `cur`: every key or entry outside the retained
prefix must move, so the retained prefix rule makes the fewest moves among prefix rules. -/
theorem retainPrefix_longest (cur next : List K) (p : List K) (hp : p.IsPrefix next)
    (hs : p.Sublist cur) : p.length ≤ (retainPrefix cur next).length := by
  have hp' : p = next.take p.length := by
    rw [List.prefix_iff_eq_take.mp hp]
    simp
  have hk : p.length ≤ next.length := hp.length_le
  have := retainLength_maximal cur next next.length p.length hk (by
    rw [← hp']
    exact (isSubseq_iff _ _).mpr hs)
  simp only [retainPrefix, List.length_take]
  exact Nat.le_min.mpr ⟨this, hk⟩

end Retention

/-! ## Trace -/

theorem getCounts_le_two (captured readback : List (Nat × String)) :
    ∀ e ∈ getCounts captured readback, e.2.2 ≤ 2 := by
  intro e he
  simp only [getCounts, List.mem_map] at he
  obtain ⟨⟨i, k⟩, _, rfl⟩ := he
  simp only
  split <;> split <;> omega

theorem getCounts_le_one (captured : List (Nat × String)) :
    ∀ e ∈ getCounts captured [], e.2.2 ≤ 1 := by
  intro e he
  simp only [getCounts, List.mem_map] at he
  obtain ⟨⟨i, k⟩, _, rfl⟩ := he
  simp only [List.contains_nil, Bool.false_eq_true, if_false, Nat.add_zero]
  split <;> omega

theorem eraseDups_nil_of {α : Type} [BEq α] (l : List α) (h : l = []) : l.eraseDups = [] := by
  subst h
  rfl

theorem readbackKeys_nil (input : Input) (kept : Array (Option Nat)) :
    readbackKeys input kept [] = [] := by
  simp only [readbackKeys]
  apply eraseDups_nil_of
  rw [List.flatMap_eq_nil_iff]
  intro j _
  split <;> simp

/-- The getter counts of a run: none when the call is rejected or has nothing to do, else the
capture reads and the readback reads of the written objects. -/
theorem run_gets (input : Input) : (run input).gets = [] ∨
    ∃ al kept, (run input).gets =
      getCounts (capturedKeys (normalized input) al)
        (readbackKeys (normalized input) kept (run input).writes) := by
  simp only [run]
  split
  · split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · simp only [publish]
        exact Or.inr ⟨_, _, rfl⟩
  · exact Or.inl rfl

/-- A getter of `current` runs at most twice: once when its object is read, once in readback. -/
theorem get_bound (input : Input) : ∀ e ∈ (run input).gets, e.2.2 ≤ 2 := by
  rcases run_gets input with h | ⟨al, kept, h⟩ <;> rw [h]
  · simp
  · exact getCounts_le_two _ _

/-- When nothing is written, a getter of `current` runs at most once. -/
theorem read_once_before_write (input : Input) (hw : (run input).writes = []) :
    ∀ e ∈ (run input).gets, e.2.2 ≤ 1 := by
  rcases run_gets input with h | ⟨al, kept, h⟩ <;> rw [h]
  · simp
  · rw [hw, readbackKeys_nil]
    exact getCounts_le_one _

/-! ## Passes -/

theorem demote_rounds_le (input : Input) (al : Discovery) (pin : Array Bool) :
    ∀ fuel forbidden, (demote input al pin fuel forbidden).2 ≤ fuel := by
  intro fuel
  induction fuel with
  | zero => intro forbidden; simp [demote]
  | succ fuel ih =>
    intro forbidden
    simp only [demote]
    split
    · exact Nat.zero_le _
    · exact Nat.succ_le_succ (ih _)

/-- The number of decision passes is at most one per pair of a next node and a current object,
plus two: a decision is final after as many demotions as there are pairs to forbid, and no plan is
searched. -/
theorem fuelOf_normalized (input : Input) :
    fuelOf (normalized input) = input.next.nodes.size * (input.cur.nodes.size + 1) + 1 := by
  simp [fuelOf, normalized, Graph.normalize]

/-- The passes of a run: none when the call is rejected statically or has nothing to do, else one
decision plus the demotion rounds of the budget. -/
theorem run_passes (input : Input) : (run input).passes = 0 ∨
    (run input).passes = 1 + (demote (normalized input) (discover (normalized input))
      (pinned (normalized input) (discover (normalized input))) (fuelOf (normalized input)) []).2 := by
  simp only [run]
  split
  · split
    · exact Or.inl rfl
    · split
      · exact Or.inr rfl
      · exact Or.inr rfl
  · exact Or.inl rfl

theorem passes_le (input : Input) :
    (run input).passes ≤ input.next.nodes.size * (input.cur.nodes.size + 1) + 2 := by
  rcases run_passes input with h | h <;> rw [h]
  · exact Nat.zero_le _
  · have := demote_rounds_le (normalized input) (discover (normalized input))
      (pinned (normalized input) (discover (normalized input))) (fuelOf (normalized input)) []
    have hf := fuelOf_normalized input
    omega

end Reconcile.Spec.Reconcile

namespace Reconcile.Spec.Produce

open Reconcile.Spec

/-- The keep conditions on node `i` with respect to a set `set`: a current node equals its draft
and refers only to nodes of the set; a created object refers only to kept created objects and
changed `Date` copies. -/
def Keeps (cur : Graph) (heap : Array Obj) (set : List Nat) (i : Nat) : Prop :=
  i < heap.size ∧ (i < cur.nodes.size → heap[i]? = some (cur.node i)) ∧
    ((heap[i]?.getD default).refs.all fun r =>
      if i < cur.nodes.size then set.contains r else createdKeeps cur heap set r) = true

theorem createdKeeps_mono (cur : Graph) (heap : Array Obj) {s t : List Nat}
    (h : ∀ x ∈ s, x ∈ t) (r : Nat) (hr : createdKeeps cur heap s r = true) :
    createdKeeps cur heap t r = true := by
  simp only [createdKeeps, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.contains_iff_mem] at hr ⊢
  rcases hr with ⟨hn, hs⟩ | hd
  · exact Or.inl ⟨hn, h _ hs⟩
  · exact Or.inr hd

theorem keeps_mono (cur : Graph) (heap : Array Obj) {s t : List Nat} (h : ∀ x ∈ s, x ∈ t)
    (i : Nat) (hi : Keeps cur heap s i) : Keeps cur heap t i := by
  obtain ⟨h1, h2, h3⟩ := hi
  refine ⟨h1, h2, ?_⟩
  simp only [List.all_eq_true] at h3 ⊢
  intro r hr
  have := h3 r hr
  split at this <;> split
  · simp only [List.contains_iff_mem] at this ⊢
    exact h _ this
  · contradiction
  · contradiction
  · exact createdKeeps_mono cur heap h r this

/-- The pruning step of `kept.go` keeps every node of a set closed under `Keeps`. -/
theorem kept_go_superset (cur : Graph) (heap : Array Obj) (S : List Nat)
    (hS : ∀ i ∈ S, Keeps cur heap S i) :
    ∀ fuel set, (∀ i ∈ S, i ∈ set) → ∀ i ∈ S, i ∈ kept.go cur heap fuel set := by
  intro fuel
  induction fuel with
  | zero => intro set h i hi; simpa [kept.go] using h i hi
  | succ fuel ih =>
    intro set h i hi
    simp only [kept.go]
    split
    · exact h i hi
    · refine ih _ ?_ i hi
      intro x hx
      simp only [List.mem_filter]
      exact ⟨h x hx, (keeps_mono cur heap h x (hS x hx)).2.2⟩

/-- Every node whose subtree the recipe left unchanged is kept: `kept` contains every set closed
under the keep conditions, so the result reuses the parts of `current` the recipe did not change
wherever it can. -/
theorem kept_greatest (cur : Graph) (heap : Array Obj) (S : List Nat)
    (hS : ∀ i ∈ S, Keeps cur heap S i) : ∀ i ∈ S, i ∈ kept cur heap := by
  intro i hi
  simp only [kept]
  refine kept_go_superset cur heap S hS _ _ ?_ i hi
  intro x hx
  obtain ⟨h1, h2, _⟩ := hS x hx
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨h1, h2⟩

theorem kept_go_closed (cur : Graph) (heap : Array Obj) :
    ∀ fuel set, set.length ≤ fuel →
      (∀ i ∈ set, i < heap.size ∧ (i < cur.nodes.size → heap[i]? = some (cur.node i))) →
      ∀ i ∈ kept.go cur heap fuel set, Keeps cur heap (kept.go cur heap fuel set) i := by
  intro fuel
  induction fuel with
  | zero =>
    intro set hlen _ i hi
    have : set = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst this
    simp [kept.go] at hi
  | succ fuel ih =>
    intro set hlen hloc i hi
    simp only [kept.go] at hi ⊢
    split at hi <;> split
    · rename_i heq _
      have hall := List.length_filter_eq_length_iff.mp heq
      have := hall i hi
      exact ⟨(hloc i hi).1, (hloc i hi).2, by simpa using this⟩
    · contradiction
    · contradiction
    · rename_i hne _
      apply ih
      · have hle := List.length_filter_le (fun i =>
          (heap[i]?.getD default).refs.all fun r =>
            if i < cur.nodes.size then set.contains r else createdKeeps cur heap set r) set
        omega
      · intro x hx
        exact hloc x (List.mem_filter.mp hx).1
      · exact hi

/-- Every kept node satisfies the keep conditions with respect to the kept set: a kept current
object is unchanged and refers only to kept objects, so the result keeps nothing the recipe
changed. -/
theorem kept_closed (cur : Graph) (heap : Array Obj) :
    ∀ i ∈ kept cur heap, Keeps cur heap (kept cur heap) i := by
  intro i hi
  simp only [kept] at hi ⊢
  refine kept_go_closed cur heap heap.size _ ?_ ?_ i hi
  · exact Nat.le_trans (List.length_filter_le _ _) (by simp [List.length_range])
  · intro x hx
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
    exact hx

end Reconcile.Spec.Produce
