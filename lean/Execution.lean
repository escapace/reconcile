import GraphPolicy
import Mathlib.Data.Finset.Card

namespace Reconcile.Execution

structure Binding where
  choice : Nat
  writer : Nat
  exposed : Nat
  storage : Nat
  mode : Nat
  palette : Finset Nat
  fixed : Bool
  construction : List Policy.Requirement

inductive Phase where
  | publishing | checking | done | rejected
  deriving DecidableEq, Repr

structure State where
  id : Nat
  revision : Nat
  phase : Phase
  domain : Finset Nat
  bindings : Nat → Binding
  checked : Finset Nat
  claims : Finset (Nat × Nat)

structure Receipt where
  id : Nat
  revision : Nat

def current (s : State) (r : Receipt) : Prop := r.id = s.id ∧ r.revision = s.revision
instance (s : State) (r : Receipt) : Decidable (current s r) := inferInstanceAs (Decidable (_ ∧ _))

def published (s : State) (r : Receipt) : State :=
  if current s r ∧ s.phase = .publishing then { s with phase := .checking, checked := ∅ } else s

def verify (s : State) (r : Receipt) (node : Nat) : State :=
  if current s r ∧ s.phase = .checking ∧ node ∈ s.domain then
    { s with checked := insert node s.checked }
  else s

def finish (s : State) (r : Receipt) : State :=
  if current s r ∧ s.phase = .checking ∧ s.domain ⊆ s.checked then
    { s with phase := .done }
  else s

-- A construction dependency cannot be rewritten during exposure-only rebinding.
def constructionStable (s : State) (node actual : Nat) : Prop :=
  ∀ owner ∈ s.domain, ∀ edge ∈ (s.bindings owner).construction,
    edge.node = node → edge.identity = actual

instance (s : State) (node actual : Nat) : Decidable (constructionStable s node actual) :=
  inferInstanceAs (Decidable (∀ owner ∈ s.domain, ∀ edge ∈ (s.bindings owner).construction,
    edge.node = node → edge.identity = actual))

def rebind (s : State) (r : Receipt) (node actual storage mode : Nat) : Option State :=
  if current s r ∧ s.phase = .checking ∧ node ∈ s.domain ∧
      (s.bindings node).fixed = false ∧ (s.bindings node).storage = storage ∧
      mode ∈ (s.bindings node).palette ∧ (node, mode) ∉ s.claims ∧
      constructionStable s node actual then
    some { s with
      bindings := fun n => if n = node then { s.bindings n with exposed := actual, mode } else s.bindings n
      revision := s.revision + 1
      phase := .publishing
      checked := ∅
      claims := insert (node, mode) s.claims }
  else none

theorem stale_plan_ignored (s : State) (r : Receipt) (node : Nat) (h : r.id ≠ s.id) :
    verify s r node = s ∧ published s r = s ∧ finish s r = s := by
  simp [verify, published, finish, current, h]

theorem stale_revision_ignored (s : State) (r : Receipt) (node : Nat) (h : r.revision ≠ s.revision) :
    verify s r node = s ∧ published s r = s ∧ finish s r = s := by
  simp [verify, published, finish, current, h]

theorem verify_within_domain (s : State) (r : Receipt) (node : Nat)
    (h : s.checked ⊆ s.domain) : (verify s r node).checked ⊆ s.domain := by
  unfold verify
  split
  · rename_i hg
    exact Finset.insert_subset hg.2.2 h
  · exact h

theorem finish_requires_complete_readback (s : State) (r : Receipt)
    (hbefore : s.phase ≠ .done) (h : (finish s r).phase = .done) :
    current s r ∧ s.phase = .checking ∧ s.domain ⊆ s.checked := by
  unfold finish at h
  split at h
  · assumption
  · exact False.elim (hbefore h)

theorem rebind_preserves_selection (s t : State) (r : Receipt) (node actual storage mode : Nat)
    (h : rebind s r node actual storage mode = some t) :
    t.id = s.id ∧ t.domain = s.domain ∧ ∀ n,
      (t.bindings n).writer = (s.bindings n).writer ∧
      (t.bindings n).choice = (s.bindings n).choice ∧
      (t.bindings n).storage = (s.bindings n).storage ∧
      (t.bindings n).construction = (s.bindings n).construction := by
  unfold rebind at h
  split at h
  · cases h
    refine ⟨rfl, rfl, ?_⟩
    intro n
    by_cases hn : n = node <;> simp [hn]
  · cases h

theorem rebind_invalidates (s t : State) (r : Receipt) (node actual storage mode : Nat)
    (h : rebind s r node actual storage mode = some t) :
    t.revision = s.revision + 1 ∧ t.phase = .publishing ∧ t.checked = ∅ := by
  unfold rebind at h
  split at h
  · cases h; simp
  · cases h

theorem cannot_finish_after_rebind (s t : State) (r receipt : Receipt) (node actual storage mode : Nat)
    (h : rebind s r node actual storage mode = some t) : finish t receipt = t := by
  have hp := (rebind_invalidates s t r node actual storage mode h).2.1
  simp [finish, hp]

theorem rebind_consumes_option (s t : State) (r : Receipt) (node actual storage mode : Nat)
    (h : rebind s r node actual storage mode = some t) :
    t.claims.card = s.claims.card + 1 := by
  unfold rebind at h
  split at h
  · rename_i hg
    have hn : (node, mode) ∉ s.claims := hg.2.2.2.2.2.2.1
    cases h
    simp [Finset.card_insert_of_notMem hn]
  · cases h

theorem rebind_construction_safe (s t : State) (r : Receipt) (node actual storage mode : Nat)
    (h : rebind s r node actual storage mode = some t) : constructionStable s node actual := by
  unfold rebind at h
  split at h
  · rename_i hg
    exact hg.2.2.2.2.2.2.2
  · cases h

-- Count only successful exposure revisions; publication/check events do not
-- create options. The supplied finite universe is the compiler's sealed palette.
inductive RebindPath : State → State → Nat → Prop where
  | nil (s : State) : RebindPath s s 0
  | publish {s t : State} {count : Nat} (r : Receipt)
      (rest : RebindPath (published s r) t count) : RebindPath s t count
  | check {s t : State} {count : Nat} (r : Receipt) (node : Nat)
      (rest : RebindPath (verify s r node) t count) : RebindPath s t count
  | cons {s t u : State} {count : Nat} (r : Receipt) (node actual storage mode : Nat)
      (step : rebind s r node actual storage mode = some t)
      (rest : RebindPath t u count) : RebindPath s u (count + 1)

theorem rebind_path_card {s t : State} {count : Nat} (h : RebindPath s t count) :
    t.claims.card = s.claims.card + count := by
  induction h with
  | nil => simp
  | publish r rest ih =>
    simpa [published, apply_ite (fun s : State => s.claims)] using ih
  | check r node rest ih =>
    simpa [verify, apply_ite (fun s : State => s.claims)] using ih
  | cons r node actual storage mode step rest ih =>
    have hc := rebind_consumes_option _ _ r node actual storage mode step
    omega

theorem rebind_path_bound {s t : State} {count : Nat} (h : RebindPath s t count)
    (options : Finset (Nat × Nat)) (hfinal : t.claims ⊆ options) :
    s.claims.card + count ≤ options.card := by
  rw [← rebind_path_card h]
  exact Finset.card_le_card hfinal

def PalettesWithin (s : State) (options : Finset (Nat × Nat)) : Prop :=
  ∀ node ∈ s.domain, ∀ mode ∈ (s.bindings node).palette, (node, mode) ∈ options

theorem rebind_palettes (s t : State) (r : Receipt) (node actual storage mode : Nat)
    (h : rebind s r node actual storage mode = some t) (options : Finset (Nat × Nat))
    (hp : PalettesWithin s options) : PalettesWithin t options := by
  unfold rebind at h
  split at h
  · cases h
    intro n hn m hm
    by_cases he : n = node <;> simp only [he, ↓reduceIte] at hm
    · subst n; exact hp node hn m hm
    · exact hp n hn m hm
  · cases h

theorem rebind_claims_within (s t : State) (r : Receipt) (node actual storage mode : Nat)
    (h : rebind s r node actual storage mode = some t) (options : Finset (Nat × Nat))
    (hc : s.claims ⊆ options) (hp : PalettesWithin s options) : t.claims ⊆ options := by
  unfold rebind at h
  split at h
  · rename_i hg
    have hd : node ∈ s.domain := hg.2.2.1
    have hm : mode ∈ (s.bindings node).palette := hg.2.2.2.2.2.1
    cases h
    exact Finset.insert_subset (hp node hd mode hm) hc
  · cases h

theorem rebind_path_within {s t : State} {count : Nat} (h : RebindPath s t count) :
    ∀ options : Finset (Nat × Nat), s.claims ⊆ options → PalettesWithin s options →
      t.claims ⊆ options := by
  induction h with
  | nil => intro options hc _; exact hc
  | publish r rest ih =>
    intro options hc hp
    apply ih options
    · simpa [published, apply_ite (fun s : State => s.claims)] using hc
    · unfold published; split <;> exact hp
  | check r node rest ih =>
    intro options hc hp
    apply ih options
    · simpa [verify, apply_ite (fun s : State => s.claims)] using hc
    · unfold verify; split <;> exact hp
  | cons r node actual storage mode step rest ih =>
    intro options hc hp
    exact ih options (rebind_claims_within _ _ r node actual storage mode step options hc hp)
      (rebind_palettes _ _ r node actual storage mode step options hp)

theorem publication_round_bound {s t : State} {count : Nat} (h : RebindPath s t count)
    (options : Finset (Nat × Nat)) (hc : s.claims ⊆ options) (hp : PalettesWithin s options) :
    1 + count ≤ 1 + options.card := by
  have hb := rebind_path_bound h options (rebind_path_within h options hc hp)
  omega

end Reconcile.Execution
