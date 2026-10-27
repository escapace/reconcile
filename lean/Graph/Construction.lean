import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Perm.Basic

/-! Reference model of the construction schedule (`src/graph/construction.ts`): `schedule` orders
the nodes that are not retained so that every dependency is known before its dependent, and a
schedule exists exactly when such a safe order does (`schedule_exists_iff`). The runtime computes
`flatSchedule`, which is the schedule when no prerequisite has prerequisites of its own
(`schedule_flat`). -/

namespace Reconcile.Construction

abbrev Dependencies := Nat → List Nat

def ready (deps : Dependencies) (known : Finset Nat) (node : Nat) : Bool :=
  (deps node).all fun dependency => decide (dependency ∈ known)

def Safe (deps : Dependencies) (known : Finset Nat) : List Nat → Prop
  | [] => True
  | node :: rest => (∀ dependency ∈ deps node, dependency ∈ known) ∧
      Safe deps (insert node known) rest

theorem safe_mono {deps : Dependencies} {known more : Finset Nat} {order : List Nat}
    (h : Safe deps known order) (hm : known ⊆ more) : Safe deps more order := by
  induction order generalizing known more with
  | nil => trivial
  | cons node rest ih =>
    exact ⟨fun d hd => hm (h.1 d hd), ih h.2 (Finset.insert_subset_insert node hm)⟩

theorem safe_append {deps : Dependencies} {known : Finset Nat} {left right : List Nat}
    (hl : Safe deps known left) (hr : Safe deps (known ∪ left.toFinset) right) :
    Safe deps known (left ++ right) := by
  induction left generalizing known with
  | nil => simpa using hr
  | cons node rest ih =>
    refine ⟨hl.1, ih hl.2 ?_⟩
    simpa [Finset.union_insert, Finset.insert_union] using hr

theorem ready_safe {deps : Dependencies} {known : Finset Nat} {wave : List Nat}
    (h : ∀ node ∈ wave, ready deps known node = true) : Safe deps known wave := by
  induction wave with
  | nil => trivial
  | cons node rest ih =>
    constructor
    · simpa [ready] using h node (by simp)
    · apply safe_mono (ih (fun n hn => h n (by simp [hn])))
      exact Finset.subset_insert _ _

-- Stable waves use only the previous wave's known identities. Fuel is a finite
-- implementation bound; each successful nonempty wave removes at least one node.
def waves (deps : Dependencies) : Nat → Finset Nat → List Nat → Option (List Nat)
  | 0, _, pending => if pending.isEmpty then some [] else none
  | fuel + 1, known, pending =>
    if pending.isEmpty then some [] else
      let wave := pending.filter (ready deps known)
      if wave.isEmpty then none else
        let waiting := pending.filter fun node => !ready deps known node
        (waves deps fuel (known ∪ wave.toFinset) waiting).map (wave ++ ·)

theorem waves_safe {deps : Dependencies} {fuel : Nat} {known : Finset Nat}
    {pending order : List Nat} (h : waves deps fuel known pending = some order) :
    Safe deps known order := by
  induction fuel generalizing known pending order with
  | zero =>
    simp only [waves] at h
    split at h <;> simp_all [Safe]
  | succ fuel ih =>
    simp only [waves] at h
    split at h
    · simp_all [Safe]
    · split at h
      · simp at h
      · obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some_iff.mp h
        apply safe_append ?_ (ih hr)
        apply ready_safe
        intro node hn
        exact (List.mem_filter.mp hn).2

theorem waves_perm {deps : Dependencies} {fuel : Nat} {known : Finset Nat}
    {pending order : List Nat} (h : waves deps fuel known pending = some order) :
    order.Perm pending := by
  induction fuel generalizing known pending order with
  | zero =>
    simp only [waves] at h
    split at h <;> simp_all
  | succ fuel ih =>
    simp only [waves] at h
    split at h
    · simp_all
    · split at h
      · simp at h
      · obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some_iff.mp h
        exact (List.Perm.append_left _ (ih hr)).trans (List.filter_append_perm _ _)

theorem safe_filter {deps : Dependencies} {known more : Finset Nat} {order : List Nat}
    {keep : Nat → Bool} (hs : Safe deps known order) (hm : known ⊆ more)
    (skip : ∀ node ∈ order, keep node = false → node ∈ more) :
    Safe deps more (order.filter keep) := by
  induction order generalizing known more with
  | nil => trivial
  | cons node rest ih =>
    by_cases hk : keep node = true
    · simp only [List.filter_cons, hk, ↓reduceIte, Safe]
      refine ⟨fun d hd => hm (hs.1 d hd), ih hs.2 (Finset.insert_subset_insert node hm) ?_⟩
      intro n hn hnkeep
      exact Finset.mem_insert_of_mem (skip n (by simp [hn]) hnkeep)
    · have hf : keep node = false := Bool.eq_false_iff.mpr hk
      simp only [List.filter_cons, hf, Bool.false_eq_true, ↓reduceIte]
      apply ih hs.2 (Finset.insert_subset_iff.mpr ⟨skip node (by simp) hf, hm⟩)
      intro n hn hnkeep
      exact skip n (by simp [hn]) hnkeep

theorem waves_complete {deps : Dependencies} {fuel : Nat} {known : Finset Nat}
    {pending : List Nat} (bound : pending.length ≤ fuel)
    (witness : ∃ order, Safe deps known order ∧ order.Perm pending) :
    ∃ order, waves deps fuel known pending = some order := by
  induction fuel generalizing known pending with
  | zero =>
    have : pending = [] := List.length_eq_zero_iff.mp (by omega)
    subst pending
    exact ⟨[], rfl⟩
  | succ fuel ih =>
    by_cases hp : pending = []
    · subst pending
      exact ⟨[], rfl⟩
    obtain ⟨order, hs, ho⟩ := witness
    have first : ∃ node ∈ pending, ready deps known node = true := by
      cases order with
      | nil => exact False.elim (hp (List.perm_nil.mp ho.symm))
      | cons node rest =>
        exact ⟨node, ho.mem_iff.mp (by simp), by simpa [ready] using hs.1⟩
    let wave := pending.filter (ready deps known)
    let waiting := pending.filter fun node => !ready deps known node
    have hw : wave ≠ [] := by
      obtain ⟨node, hn, hr⟩ := first
      intro he
      have : node ∈ wave := List.mem_filter.mpr ⟨hn, hr⟩
      simp [he] at this
    have partition := (List.filter_append_perm (ready deps known) pending).length_eq
    have positive : 0 < wave.length := List.length_pos_iff.mpr hw
    have smaller : waiting.length ≤ fuel := by
      simp only [List.length_append] at partition
      change wave.length + waiting.length = pending.length at partition
      omega
    have hs' : Safe deps (known ∪ wave.toFinset)
        (order.filter fun node => !ready deps known node) := by
      apply safe_filter hs Finset.subset_union_left
      intro node hn hk
      apply Finset.mem_union_right
      apply List.mem_toFinset.mpr
      exact List.mem_filter.mpr ⟨ho.mem_iff.mp hn, by simpa using hk⟩
    obtain ⟨rest, hr⟩ := ih smaller ⟨_, hs', ho.filter (fun node => !ready deps known node)⟩
    refine ⟨wave ++ rest, ?_⟩
    simpa [waves, hp, wave, waiting, hw] using congrArg (Option.map (wave ++ ·)) hr

def schedule (deps : Dependencies) (retained : Finset Nat) (nodes : List Nat) : Option (List Nat) :=
  let fresh := nodes.filter fun node => decide (node ∉ retained)
  let shells := fresh.filter fun node => (deps node).isEmpty
  let pending := fresh.filter fun node => !(deps node).isEmpty
  (waves deps nodes.length (retained ∪ shells.toFinset) pending).map (shells ++ ·)

theorem waves_nil {deps : Dependencies} {fuel : Nat} {known : Finset Nat} :
    waves deps fuel known [] = some [] := by
  cases fuel <;> rfl

/-- A wave that finds every pending node ready is the last one. -/
theorem waves_all_ready {deps : Dependencies} {fuel : Nat} {known : Finset Nat}
    {pending : List Nat} (bound : pending.length ≤ fuel)
    (allReady : ∀ node ∈ pending, ready deps known node = true) :
    waves deps fuel known pending = some pending := by
  cases pending with
  | nil => exact waves_nil
  | cons node rest =>
    obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 :=
      ⟨fuel - 1, by simp only [List.length_cons] at bound; omega⟩
    have wave : (node :: rest).filter (ready deps known) = node :: rest :=
      List.filter_eq_self.mpr allReady
    have waiting : (node :: rest).filter (fun node => !ready deps known node) = [] :=
      List.filter_eq_nil_iff.mpr fun other member => by simp [allReady other member]
    simp only [waves, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, wave, waiting, waves_nil,
      Option.map_some, List.append_nil]

/-- The construction order when every prerequisite has none of its own: the fresh nodes without
prerequisites, then the fresh nodes with some, each in the given order. -/
def flatSchedule (deps : Dependencies) (retained : Finset Nat) (nodes : List Nat) : List Nat :=
  let fresh := nodes.filter fun node => decide (node ∉ retained)
  fresh.filter (fun node => (deps node).isEmpty) ++ fresh.filter fun node => !(deps node).isEmpty

/-- When each prerequisite of a fresh node is retained or a node without prerequisites, the
fresh nodes with prerequisites all form the wave after the shells, so the schedule exists and is
`flatSchedule`, which `schedule_safe` and `schedule_perm` therefore cover. -/
theorem schedule_flat {deps : Dependencies} {retained : Finset Nat} {nodes : List Nat}
    (flat : ∀ node ∈ nodes, node ∉ retained → ∀ dependency ∈ deps node,
      dependency ∈ retained ∨ (dependency ∈ nodes ∧ deps dependency = [])) :
    schedule deps retained nodes = some (flatSchedule deps retained nodes) := by
  let fresh := nodes.filter fun node => decide (node ∉ retained)
  let shells := fresh.filter fun node => (deps node).isEmpty
  let pending := fresh.filter fun node => !(deps node).isEmpty
  have bound : pending.length ≤ nodes.length :=
    (List.length_filter_le _ _).trans (List.length_filter_le _ _)
  have allReady : ∀ node ∈ pending, ready deps (retained ∪ shells.toFinset) node = true := by
    intro node member
    obtain ⟨inNodes, isFresh⟩ := List.mem_filter.mp (List.mem_filter.mp member).1
    simp only [ready, List.all_eq_true, decide_eq_true_eq]
    intro dependency hd
    by_cases kept : dependency ∈ retained
    · exact Finset.mem_union_left _ kept
    · obtain ⟨dependencyInNodes, none⟩ :=
        (flat node inNodes (by simpa using isFresh) dependency hd).resolve_left kept
      apply Finset.mem_union_right
      apply List.mem_toFinset.mpr
      exact List.mem_filter.mpr
        ⟨List.mem_filter.mpr ⟨dependencyInNodes, by simpa using kept⟩, by simp [none]⟩
  have last := waves_all_ready bound allReady
  simp only [schedule, flatSchedule]
  exact congrArg (Option.map (shells ++ ·)) last

/-- When no fresh node has construction inputs, every fresh node is a shell and the order is
the fresh nodes in their given order. -/
theorem schedule_shells_only {deps : Dependencies} {retained : Finset Nat} {nodes : List Nat}
    (shells : ∀ node ∈ nodes, node ∉ retained → deps node = []) :
    schedule deps retained nodes = some (nodes.filter fun node => decide (node ∉ retained)) := by
  rw [schedule_flat fun node hn hr d hd => by simp [shells node hn hr] at hd, flatSchedule]
  set fresh := nodes.filter fun node => decide (node ∉ retained)
  have empty (node) (hn : node ∈ fresh) : (deps node).isEmpty = true := by
    obtain ⟨hm, hf⟩ := List.mem_filter.mp hn
    simp [shells node hm (by simpa using hf)]
  have all : fresh.filter (fun node => (deps node).isEmpty) = fresh := List.filter_eq_self.mpr empty
  have none : fresh.filter (fun node => !(deps node).isEmpty) = [] :=
    List.filter_eq_nil_iff.mpr fun n hn => by simp [empty n hn]
  simp only [all, none, List.append_nil]

/-- A plan retaining every node constructs nothing: its order is empty, so publication allocates
and writes nothing and each node keeps its own target. -/
theorem schedule_all_retained {deps : Dependencies} {retained : Finset Nat} {nodes : List Nat}
    (all : ∀ node ∈ nodes, node ∈ retained) : schedule deps retained nodes = some [] := by
  rw [schedule_shells_only fun node member fresh => absurd (all node member) fresh]
  simp only [Option.some.injEq, List.filter_eq_nil_iff, decide_eq_true_eq, not_not]
  exact all

theorem schedule_safe {deps : Dependencies} {retained : Finset Nat} {nodes order : List Nat}
    (h : schedule deps retained nodes = some order) : Safe deps retained order := by
  obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  apply safe_append ?_ (waves_safe hr)
  apply ready_safe
  intro node hn
  have he := (List.mem_filter.mp hn).2
  simp only [List.isEmpty_iff] at he
  simp [ready, he]

theorem schedule_perm {deps : Dependencies} {retained : Finset Nat} {nodes order : List Nat}
    (h : schedule deps retained nodes = some order) :
    order.Perm (nodes.filter fun node => decide (node ∉ retained)) := by
  obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  exact (List.Perm.append_left _ (waves_perm hr)).trans (List.filter_append_perm _ _)

theorem schedule_complete {deps : Dependencies} {retained : Finset Nat} {nodes : List Nat}
    (witness : ∃ order, Safe deps retained order ∧
      order.Perm (nodes.filter fun node => decide (node ∉ retained))) :
    ∃ order, schedule deps retained nodes = some order := by
  obtain ⟨order, hs, ho⟩ := witness
  let fresh := nodes.filter fun node => decide (node ∉ retained)
  let shells := fresh.filter fun node => (deps node).isEmpty
  let pending := fresh.filter fun node => !(deps node).isEmpty
  have bound : pending.length ≤ nodes.length :=
    (List.length_filter_le _ _).trans (List.length_filter_le _ _)
  have hs' : Safe deps (retained ∪ shells.toFinset)
      (order.filter fun node => !(deps node).isEmpty) := by
    apply safe_filter hs Finset.subset_union_left
    intro node hn hk
    apply Finset.mem_union_right
    apply List.mem_toFinset.mpr
    exact List.mem_filter.mpr ⟨ho.mem_iff.mp hn, by simpa using hk⟩
  obtain ⟨rest, hr⟩ := waves_complete bound
    ⟨_, hs', ho.filter (fun node => !(deps node).isEmpty)⟩
  refine ⟨shells ++ rest, ?_⟩
  simpa [schedule, fresh, shells, pending] using congrArg (Option.map (shells ++ ·)) hr

theorem schedule_exists_iff {deps : Dependencies} {retained : Finset Nat} {nodes : List Nat} :
    (∃ order, schedule deps retained nodes = some order) ↔
    (∃ order, Safe deps retained order ∧
      order.Perm (nodes.filter fun node => decide (node ∉ retained))) := by
  constructor
  · rintro ⟨order, h⟩
    exact ⟨order, schedule_safe h, schedule_perm h⟩
  · exact schedule_complete

end Reconcile.Construction
