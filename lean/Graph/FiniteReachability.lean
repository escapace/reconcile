import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Relation

/-! Finite reachability over an admitted graph by staged closure, and strongly connected
components with a canonical leader. A simple bounded reference for `src/graph/forced-groups.ts`;
no efficient strongly connected component algorithm is assumed. -/

namespace Reconcile.FiniteReachability

/-- Finite admitted graph; labels carry no JavaScript object semantics. -/
structure Graph where
  vertices : Finset Nat
  next : Nat → Finset Nat
  admitted : ∀ source, next source ⊆ vertices

def step (g : Graph) (seen : Finset Nat) : Finset Nat := seen ∪ seen.biUnion g.next

def stage (g : Graph) (seed : Finset Nat) : Nat → Finset Nat
  | 0 => seed
  | n + 1 => step g (stage g seed n)

def reaches (g : Graph) := Relation.ReflTransGen (fun a b => b ∈ g.next a)

/-- A simple bounded reference; no efficient SCC implementation is assumed. -/
def closure (g : Graph) (seed : Finset Nat) : Finset Nat :=
  stage g seed (g.vertices.card + 1)

theorem step_contains (g : Graph) (seen : Finset Nat) : seen ⊆ step g seen := by
  intro id hi
  exact Finset.mem_union_left _ hi

theorem step_admitted (g : Graph) (seen : Finset Nat) (h : seen ⊆ g.vertices) :
    step g seen ⊆ g.vertices := by
  intro id hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact h hi
  · obtain ⟨source, _, he⟩ := Finset.mem_biUnion.mp hi
    exact g.admitted source he

theorem stage_admitted (g : Graph) (seed : Finset Nat) (h : seed ⊆ g.vertices) (n : Nat) :
    stage g seed n ⊆ g.vertices := by
  induction n with
  | zero => exact h
  | succ n ih => exact step_admitted g _ ih

theorem stage_contains (g : Graph) (seed : Finset Nat) (n : Nat) : seed ⊆ stage g seed n := by
  induction n with
  | zero => exact Finset.Subset.refl _
  | succ n ih => exact Finset.Subset.trans ih (step_contains g _)

/-- Until saturation, every stage strictly increases the finite visited set. -/
theorem growth (g : Graph) (seed : Finset Nat) (n : Nat) :
    step g (stage g seed n) = stage g seed n ∨ n ≤ (stage g seed n).card := by
  induction n with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ n ih =>
    by_cases h : step g (stage g seed n) = stage g seed n
    · exact Or.inl (by simp only [stage, h])
    · have hg := ih.resolve_left h
      have hs : stage g seed n ⊂ step g (stage g seed n) :=
        lt_of_le_of_ne (step_contains g _) (Ne.symm h)
      have hc := Finset.card_lt_card hs
      right
      simp only [stage]
      omega

theorem closure_fixed (g : Graph) (seed : Finset Nat) (h : seed ⊆ g.vertices) :
    step g (closure g seed) = closure g seed := by
  rcases growth g seed (g.vertices.card + 1) with hf | hg
  · exact hf
  · have hb := Finset.card_le_card (stage_admitted g seed h (g.vertices.card + 1))
    omega

theorem stage_sound (g : Graph) (source : Nat) (n : Nat) :
    ∀ target ∈ stage g {source} n, reaches g source target := by
  induction n with
  | zero => intro target ht; have he := Finset.mem_singleton.mp ht; subst target; exact .refl
  | succ n ih =>
    intro target ht
    rcases Finset.mem_union.mp ht with ht | ht
    · exact ih target ht
    · obtain ⟨previous, hp, he⟩ := Finset.mem_biUnion.mp ht
      exact (ih previous hp).tail he

theorem closure_iff (g : Graph) {source target : Nat} (hs : source ∈ g.vertices) :
    target ∈ closure g {source} ↔ reaches g source target := by
  constructor
  · exact stage_sound g source _ target
  · intro hr
    have hf := closure_fixed g {source} (by simpa using hs)
    induction hr with
    | refl => exact stage_contains g {source} _ (by simp)
    | @tail previous target hr edge ih =>
      rw [← hf]
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨previous, ih, edge⟩)

def component (g : Graph) (source : Nat) : Finset Nat :=
  g.vertices.filter fun target => target ∈ closure g {source} ∧ source ∈ closure g {target}

theorem component_mem_iff (g : Graph) {source target : Nat} (hs : source ∈ g.vertices) :
    target ∈ component g source ↔
      target ∈ g.vertices ∧ reaches g source target ∧ reaches g target source := by
  by_cases ht : target ∈ g.vertices
  · simp only [component, Finset.mem_filter, ht, true_and, closure_iff g hs, closure_iff g ht]
  · simp [component, ht]

theorem component_self (g : Graph) {source : Nat} (hs : source ∈ g.vertices) :
    source ∈ component g source :=
  (component_mem_iff g hs).mpr ⟨hs, .refl, .refl⟩

/-- Canonical class label, with an irrelevant default for non-admitted IDs. -/
def leader (g : Graph) (source : Nat) : Nat :=
  if h : source ∈ g.vertices then (component g source).min' ⟨source, component_self g h⟩
  else source

theorem leader_mem (g : Graph) {source : Nat} (hs : source ∈ g.vertices) :
    leader g source ∈ component g source := by
  simp only [leader, dif_pos hs]
  exact Finset.min'_mem _ _

theorem component_eq (g : Graph) {a b : Nat} (ha : a ∈ g.vertices) (hb : b ∈ g.vertices)
    (hab : reaches g a b) (hba : reaches g b a) : component g a = component g b := by
  ext target
  rw [component_mem_iff g ha, component_mem_iff g hb]
  constructor
  · rintro ⟨ht, hat, hta⟩
    exact ⟨ht, hba.trans hat, hta.trans hab⟩
  · rintro ⟨ht, hbt, htb⟩
    exact ⟨ht, hab.trans hbt, htb.trans hba⟩

theorem leader_eq_iff (g : Graph) {a b : Nat} (ha : a ∈ g.vertices) (hb : b ∈ g.vertices) :
    leader g a = leader g b ↔ reaches g a b ∧ reaches g b a := by
  constructor
  · intro he
    obtain ⟨_, hal, hla⟩ := (component_mem_iff g ha).mp (leader_mem g ha)
    obtain ⟨_, hbl, hlb⟩ := (component_mem_iff g hb).mp (leader_mem g hb)
    rw [he] at hal hla
    exact ⟨hal.trans hlb, hbl.trans hla⟩
  · rintro ⟨hab, hba⟩
    have hc := component_eq g ha hb hab hba
    simp only [leader, dif_pos ha, dif_pos hb]
    congr 1

/-- A materialized finite table; lookup does not rebuild its entries under eta expansion. -/
structure Table (α : Type) where
  entries : Array α
  fallback : Nat → α

def table {α : Type} (limit : Nat) (f : Nat → α) : Table α :=
  { entries := Array.ofFn (fun i : Fin limit => f i.val), fallback := f }

def Table.get {α : Type} (values : Table α) (source : Nat) : α :=
  if h : source < values.entries.size then values.entries[source] else values.fallback source

theorem table_get {α : Type} (limit : Nat) (f : Nat → α) (source : Nat) :
    (table limit f).get source = f source := by
  simp only [Table.get, table, Array.size_ofFn]
  split <;> simp

/-- Pointwise table equivalence is independent of whether callers retain the table. -/
def memo {α : Type} (limit : Nat) (f : Nat → α) : Nat → α := (table limit f).get

theorem memo_eq {α : Type} (limit : Nat) (f : Nat → α) : memo limit f = f := by
  funext source
  exact table_get limit f source

/-- Materialize adjacency before repeated closure expansion. -/
def cachedGraph (g : Graph) (limit : Nat) : Graph :=
  let values := table limit g.next
  { vertices := g.vertices
    next := values.get
    admitted := by intro source; simp only [values, table_get]; exact g.admitted source }

theorem cachedGraph_eq (g : Graph) (limit : Nat) : cachedGraph g limit = g := by
  have he : (table limit g.next).get = g.next := funext (table_get limit g.next)
  cases g
  simp only [cachedGraph, he]

/-- Cache singleton closures once and materialize all canonical labels in one pass. -/
def cachedLabels (g : Graph) (limit : Nat) : Table Nat :=
  let graph := cachedGraph g limit
  let reachable := table limit (fun source => closure graph {source})
  table limit fun source =>
    if h : source ∈ g.vertices then
      let members := g.vertices.filter fun target =>
        target ∈ reachable.get source ∧ source ∈ reachable.get target
      members.min' ⟨source, by
        simp only [members, reachable, table_get, graph, cachedGraph_eq]
        exact component_self g h⟩
    else source

theorem cachedLabels_get (g : Graph) (limit source : Nat) :
    (cachedLabels g limit).get source = leader g source := by
  simp only [cachedLabels, table_get, cachedGraph_eq]
  rfl

/-- Pointwise projection; executable bridges retain the materialized label table itself. -/
def cachedLeader (g : Graph) (limit : Nat) : Nat → Nat := (cachedLabels g limit).get

theorem cachedLeader_eq (g : Graph) (limit : Nat) : cachedLeader g limit = leader g := by
  funext source
  exact cachedLabels_get g limit source

/-- A concrete nontrivial SCC and an outgoing singleton distinguish mutual from one-way reach. -/
def exampleGraph : Graph where
  vertices := {0, 1, 2}
  next := fun source => if source = 0 then {1} else if source = 1 then {0, 2} else ∅
  admitted := by intro source; split_ifs <;> simp

example : component exampleGraph 0 = {0, 1} := by decide
example : component exampleGraph 2 = {2} := by decide
example : leader exampleGraph 0 = leader exampleGraph 1 := by decide
example : leader exampleGraph 0 ≠ leader exampleGraph 2 := by decide

end Reconcile.FiniteReachability
