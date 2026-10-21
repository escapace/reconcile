import Graph.GraphPolicy
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation

/-! Forced choice groups (`src/graph/forced-groups.ts`): mandatory implications between choice
literals, components of mutually forcing literals that a feasible selection takes whole, and a
partition certificate that encodes selections as groups without changing retention or order. -/

namespace Reconcile.ForcedGroups

open Policy

/-- Literal IDs distinguish choice positions even when their payloads are equal. -/
structure Problem where
  nodes : Finset Nat
  literals : Finset Nat
  owner : Nat → Nat
  choice : Nat → Choice

def supports (p : Problem) (edge : Requirement) : Finset Nat :=
  p.literals.filter fun id => p.owner id = edge.node ∧ (p.choice id).identity = edge.identity

def feasible (p : Problem) (selected : Finset Nat) : Prop :=
  selected ⊆ p.literals ∧
  (∀ node ∈ p.nodes, ∃ id ∈ selected, p.owner id = node) ∧
  (∀ a ∈ selected, ∀ b ∈ selected, p.owner a = p.owner b → a = b) ∧
  (∀ a ∈ selected, ∀ b ∈ selected, (p.choice a).storage = (p.choice b).storage → a = b) ∧
  (∀ a ∈ selected, ∀ edge ∈ (p.choice a).required, ∃ b ∈ selected, b ∈ supports p edge)

instance (p : Problem) (selected : Finset Nat) : Decidable (feasible p selected) := by
  unfold feasible
  infer_instance

/-- An implication is mandatory only when the complete target domain has one support. -/
def mandatory (p : Problem) (source target : Nat) : Prop :=
  ∃ edge ∈ (p.choice source).required, supports p edge = {target}

instance (p : Problem) (source target : Nat) : Decidable (mandatory p source target) := by
  unfold mandatory
  infer_instance

def reaches (p : Problem) := Relation.ReflTransGen (mandatory p)

theorem selected_mandatory (p : Problem) (selected : Finset Nat)
    (hf : feasible p selected) {source target : Nat}
    (hs : source ∈ selected) (h : mandatory p source target) : target ∈ selected := by
  obtain ⟨edge, he, hu⟩ := h
  obtain ⟨id, hi, hm⟩ := hf.2.2.2.2 source hs edge he
  rw [hu] at hm
  have : id = target := Finset.mem_singleton.mp hm
  simpa [← this] using hi

theorem selected_reachable (p : Problem) (selected : Finset Nat)
    (hf : feasible p selected) {source target : Nat}
    (hs : source ∈ selected) (h : reaches p source target) : target ∈ selected := by
  induction h with
  | refl => exact hs
  | tail h edge ih => exact selected_mandatory p selected hf ih edge

/-- Exact SCC membership is a finite algorithm correspondence obligation. -/
def sameComponent (p : Problem) (a b : Nat) : Prop := reaches p a b ∧ reaches p b a

theorem component_forced (p : Problem) (selected : Finset Nat)
    (hf : feasible p selected) {source target : Nat}
    (hs : source ∈ selected) (h : sameComponent p source target) : target ∈ selected :=
  selected_reachable p selected hf hs h.1

/-- A group with two different choices for one variable cannot be partly selected. -/
theorem owner_conflict (p : Problem) (selected : Finset Nat)
    (hf : feasible p selected) {source target : Nat}
    (hgroup : sameComponent p source target) (howner : p.owner source = p.owner target)
    (hne : source ≠ target) : source ∉ selected := by
  intro hs
  exact hne (hf.2.2.1 source hs target (component_forced p selected hf hs hgroup) howner)

theorem storage_conflict (p : Problem) (selected : Finset Nat)
    (hf : feasible p selected) {source target : Nat}
    (hgroup : sameComponent p source target)
    (hstorage : (p.choice source).storage = (p.choice target).storage)
    (hne : source ≠ target) : source ∉ selected := by
  intro hs
  exact hne (hf.2.2.2.1 source hs target (component_forced p selected hf hs hgroup) hstorage)

/-- A partition certificate separates SCC computation from the quotient theorem. -/
structure Partition (p : Problem) where
  classOf : Nat → Nat
  exact : ∀ a ∈ p.literals, ∀ b ∈ p.literals,
    classOf a = classOf b ↔ sameComponent p a b

def encode (partition : Partition p) (selected : Finset Nat) : Finset Nat :=
  selected.image partition.classOf

def decode (partition : Partition p) (groups : Finset Nat) : Finset Nat :=
  p.literals.filter fun id => partition.classOf id ∈ groups

theorem decode_encode (p : Problem) (partition : Partition p) (selected : Finset Nat)
    (hf : feasible p selected) : decode partition (encode partition selected) = selected := by
  ext id
  constructor
  · intro h
    obtain ⟨hi, hg⟩ := Finset.mem_filter.mp h
    obtain ⟨source, hs, hc⟩ := Finset.mem_image.mp hg
    exact component_forced p selected hf hs ((partition.exact source (hf.1 hs) id hi).mp hc)
  · intro h
    exact Finset.mem_filter.mpr ⟨hf.1 h, Finset.mem_image.mpr ⟨id, h, rfl⟩⟩

theorem encode_decode (p : Problem) (partition : Partition p) (groups : Finset Nat)
    (hg : groups ⊆ p.literals.image partition.classOf) :
    encode partition (decode partition groups) = groups := by
  ext group
  simp only [encode, decode, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨id, ⟨_, hi⟩, he⟩
    simpa [he] using hi
  · intro h
    obtain ⟨id, hi, he⟩ := Finset.mem_image.mp (hg h)
    exact ⟨id, ⟨hi, by simpa [he] using h⟩, he⟩

/-- Expansion preserves the original literal set, hence every original retention weight. -/
theorem retained_projection (p : Problem) (partition : Partition p) (selected : Finset Nat)
    (hf : feasible p selected) :
    ((decode partition (encode partition selected)).filter fun id => (p.choice id).retained).card =
      (selected.filter fun id => (p.choice id).retained).card := by
  rw [decode_encode p partition selected hf]

/-- This projection preserves order and multiplicity; it does not authorize a new tie order. -/
theorem ordered_roundtrip (p : Problem) (partition : Partition p) (plans : List (Finset Nat))
    (hf : ∀ selected ∈ plans, feasible p selected) :
    plans.map (fun selected => decode partition (encode partition selected)) = plans := by
  induction plans with
  | nil => rfl
  | cons head rest ih =>
    simp only [List.map_cons]
    rw [decode_encode p partition head (hf head (by simp))]
    congr 1
    apply ih
    intro selected hs
    exact hf selected (by simp [hs])

/-- Forcing a partner of an already selected literal cannot remove a feasible completion. -/
theorem prefix_forcing (p : Problem) (selected chosen : Finset Nat)
    (hf : feasible p selected) (hp : chosen ⊆ selected) {source target : Nat}
    (hs : source ∈ chosen) (hc : sameComponent p source target) : target ∈ selected :=
  component_forced p selected hf (hp hs) hc

/-- A conflicting prefix choice excludes every member of the later candidate's component. -/
theorem prefix_conflict (p : Problem) (selected chosen : Finset Nat)
    (hf : feasible p selected) (hp : chosen ⊆ selected) {source target old : Nat}
    (hold : old ∈ chosen) (hc : sameComponent p source target)
    (ho : p.owner old = p.owner target) (hne : old ≠ target) : source ∉ selected := by
  intro hs
  exact hne (hf.2.2.1 old (hp hold) target (component_forced p selected hf hs hc) ho)

/-- Different partition classes cannot share a literal, even if some owners coincide. -/
theorem classes_disjoint (p : Problem) (partition : Partition p) {a b : Nat}
    (hne : a ≠ b) : Disjoint (decode partition {a}) (decode partition {b}) := by
  apply Finset.disjoint_left.mpr
  intro id ha hb
  have hia := (Finset.mem_filter.mp ha).2
  have hib := (Finset.mem_filter.mp hb).2
  simp only [Finset.mem_singleton] at hia hib
  exact hne (hia.symm.trans hib)

/-- An availability check supplies precisely the ownership premise needed by undo. -/
theorem available_owners (p : Problem) (previous group : Finset Nat)
    (available : ∀ member ∈ group, ∀ old ∈ previous, p.owner member ≠ p.owner old) :
    ∀ old ∈ previous, ∀ member ∈ group, p.owner old ≠ p.owner member := by
  intro old ho member hm he
  exact available member hm old ho he.symm

def clearOwners (p : Problem) (state group : Finset Nat) : Finset Nat :=
  state.filter fun id => ∀ member ∈ group, p.owner id ≠ p.owner member

/-- A group owns only previously unforced positions; clearing them exactly restores entry state. -/
theorem clear_after_assign (p : Problem) (previous group : Finset Nat)
    (hd : ∀ old ∈ previous, ∀ member ∈ group, p.owner old ≠ p.owner member) :
    clearOwners p (previous ∪ group) group = previous := by
  ext id
  simp only [clearOwners, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨h | h, hc⟩
    · exact h
    · exact False.elim (hc id h rfl)
  · intro h
    exact ⟨Or.inl h, hd id h⟩

theorem reaches_rank (p : Problem)
    (inc : ∀ a b, mandatory p a b → p.owner a < p.owner b)
    {source target : Nat} (h : reaches p source target) :
    source = target ∨ p.owner source < p.owner target := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail b c h edge ih =>
    rcases ih with he | hl
    · subst b
      exact Or.inr (inc _ _ edge)
    · exact Or.inr (Nat.lt_trans hl (inc _ _ edge))

/-- Strictly forward requirements certify singleton SCCs without computing supports or SCCs. -/
theorem forward_singletons (p : Problem)
    (forward : ∀ source edge, edge ∈ (p.choice source).required → p.owner source < edge.node)
    {a b : Nat} (h : sameComponent p a b) : a = b := by
  have inc : ∀ a b, mandatory p a b → p.owner a < p.owner b := by
    intro source target hm
    obtain ⟨edge, he, hu⟩ := hm
    have ht : target ∈ supports p edge := by rw [hu]; simp
    have hn := (Finset.mem_filter.mp ht).2.1
    simpa [hn] using forward source edge he
  rcases reaches_rank p inc h.1 with he | hl
  · exact he
  rcases reaches_rank p inc h.2 with he | hr
  · exact he.symm
  · exact False.elim (Nat.lt_asymm hl hr)

/-- An inhabited two-literal cycle witnesses an actual two-to-one quotient. -/
def twoCycle : Problem where
  nodes := {0, 1}
  literals := {0, 1}
  owner := id
  choice := fun id =>
    { identity := id, storage := id, retained := true,
      required := if id = 0 then [{ node := 1, identity := 1 }]
        else if id = 1 then [{ node := 0, identity := 0 }] else [] }

example : feasible twoCycle {0, 1} := by decide
example : ¬ feasible twoCycle {0} := by decide

def twoCyclePartition : Partition twoCycle where
  classOf := fun _ => 0
  exact := by
    intro a ha b hb
    have h01 : mandatory twoCycle 0 1 := by decide
    have h10 : mandatory twoCycle 1 0 := by decide
    simp only [twoCycle, Finset.mem_insert, Finset.mem_singleton] at ha hb
    constructor
    · intro _
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact ⟨.refl, .refl⟩
      · exact ⟨.single h01, .single h10⟩
      · exact ⟨.single h10, .single h01⟩
      · exact ⟨.refl, .refl⟩
    · intro _
      rfl

example : encode twoCyclePartition {0, 1} = {0} := by decide
example : decode twoCyclePartition {0} = {0, 1} := by decide

/-- Equal identities with distinct choice positions must not be guessed to be unique support. -/
def alternatives : Problem where
  nodes := {0, 1}
  literals := {0, 1, 2}
  owner := fun id => if id = 0 then 0 else 1
  choice := fun id =>
    { identity := if id = 0 then 0 else 1, storage := id, retained := true,
      required := if id = 0 then [{ node := 1, identity := 1 }] else [] }

example : feasible alternatives {0, 2} := by decide
example : ¬ mandatory alternatives 0 1 := by decide

-- Native/algorithm correspondence requires exact literal-position encoding,
-- complete target-domain supports, original ordered node projection and force/undo ownership.
-- ForcedGroupsReference supplies a proved executable partition. PolicyOracle and
-- complete-stream bridges check runtime correspondence on finite and native fixtures;
-- these lemmas do not mechanically verify the TypeScript SCC routine or enumerator.

end Reconcile.ForcedGroups
