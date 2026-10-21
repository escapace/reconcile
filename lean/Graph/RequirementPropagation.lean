import Graph.RequirementAdmission

/-! Ordered propagation traces. Fuel counts fresh expansions, not skipped entries;
finite completion and ordered insertion are proved below. Native Set and array
representation correspondence remains a runtime obligation. -/
namespace Reconcile.RequirementPropagation

open Reconcile.RequirementAdmission

def lazyTrace (successors : Nat → List Nat) (fuel : Nat) (known : Finset Nat)
    (pending : List Nat) : List Nat :=
  match fuel, pending with
  | 0, _ => []
  | _, [] => []
  | fuel + 1, head :: rest =>
    if head ∈ known then lazyTrace successors (fuel + 1) known rest
    else head :: lazyTrace successors fuel (insert head known) (rest ++ successors head)
termination_by (fuel, pending.length)

def eagerTrace (successors : Nat → List Nat) : Nat → Finset Nat → List Nat → List Nat
  | 0, _, _ => []
  | _, _, [] => []
  | fuel + 1, admitted, head :: rest =>
    head :: eagerTrace successors fuel (admitted ∪ (successors head).toFinset)
      (rest ++ admit admitted (successors head))

theorem trace_eq (successors : Nat → List Nat) (fuel : Nat) (known : Finset Nat)
    (pending : List Nat) :
    lazyTrace successors fuel known pending =
      eagerTrace successors fuel (known ∪ pending.toFinset) (admit known pending) := by
  induction fuel generalizing known pending with
  | zero => simp [lazyTrace, eagerTrace]
  | succ fuel ih =>
    induction pending generalizing known with
    | nil => simp [lazyTrace, eagerTrace, admit]
    | cons head rest tailIH =>
      by_cases hh : head ∈ known
      · have hs : known ∪ (head :: rest).toFinset = known ∪ rest.toFinset := by
          ext fact
          simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons]
          aesop
        simp only [lazyTrace, hh, ↓reduceIte, admit]
        rw [hs]
        exact tailIH known
      · rw [lazyTrace, if_neg hh]
        rw [ih]
        have hs : insert head known ∪ (rest ++ successors head).toFinset =
            (known ∪ (head :: rest).toFinset) ∪ (successors head).toFinset := by
          ext fact
          simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset,
            List.mem_append, List.mem_cons]
          tauto
        rw [hs, queue_step known head rest (successors head) hh]
        rw [admit_set]
        simp only [admit, hh, ↓reduceIte, eagerTrace]

structure State where
  processed : List Nat
  pending : List Nat
  admitted : Finset Nat

def Invariant (initial : Finset Nat) (state : State) : Prop :=
  (state.processed ++ state.pending).Nodup ∧
    state.admitted = initial ∪ (state.processed ++ state.pending).toFinset

def start (initial : Finset Nat) (seeds : List Nat) : State :=
  ⟨[], admit initial seeds, initial ∪ seeds.toFinset⟩

theorem start_invariant (initial : Finset Nat) (seeds : List Nat) :
    Invariant initial (start initial seeds) := by
  simp only [Invariant, start, List.nil_append]
  exact ⟨admit_nodup _ _, (admit_set _ _).symm⟩

def step (successors : Nat → List Nat) (processed : List Nat) (head : Nat)
    (rest : List Nat) (admitted : Finset Nat) : State :=
  ⟨processed ++ [head], rest ++ admit admitted (successors head),
    admitted ∪ (successors head).toFinset⟩

theorem step_invariant (successors : Nat → List Nat) (initial : Finset Nat)
    (processed : List Nat) (head : Nat) (rest : List Nat) (admitted : Finset Nat)
    (h : Invariant initial ⟨processed, head :: rest, admitted⟩) :
    Invariant initial (step successors processed head rest admitted) := by
  rcases h with ⟨unique, sets⟩
  dsimp at unique sets
  have distinct : List.Disjoint (processed ++ head :: rest) (admit admitted (successors head)) := by
    apply List.disjoint_left.mpr
    intro fact hf ha
    have absent := ((admit_mem admitted (successors head) fact).mp ha).2
    apply absent
    rw [sets]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr hf)
  constructor
  · have hn := List.nodup_append'.mpr ⟨unique, admit_nodup _ _, distinct⟩
    simpa [step, List.append_assoc] using hn
  · change admitted ∪ (successors head).toFinset =
      initial ∪ ((processed ++ [head]) ++ (rest ++ admit admitted (successors head))).toFinset
    rw [← admit_set admitted (successors head), sets]
    ext fact
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_append, List.mem_cons]
    tauto

theorem frontier_bound (initial vertices : Finset Nat) (state : State)
    (h : Invariant initial state) (bounded : state.admitted ⊆ vertices) :
    (state.processed ++ state.pending).length ≤ vertices.card := by
  rw [← List.toFinset_card_of_nodup h.1]
  apply Finset.card_le_card
  intro fact hf
  apply bounded
  rw [h.2]
  exact Finset.mem_union_right _ hf

def run (successors : Nat → List Nat) : Nat → State → State
  | 0, state => state
  | fuel + 1, state => match state.pending with
    | [] => state
    | head :: rest => run successors fuel (step successors state.processed head rest state.admitted)

theorem run_invariant (successors : Nat → List Nat) (initial : Finset Nat)
    (fuel : Nat) (state : State) (h : Invariant initial state) :
    Invariant initial (run successors fuel state) := by
  induction fuel generalizing state with
  | zero => exact h
  | succ fuel ih =>
    rcases state with ⟨processed, pending, admitted⟩
    cases pending with
    | nil => exact h
    | cons head rest => exact ih _ (step_invariant successors initial processed head rest admitted h)

theorem run_trace (successors : Nat → List Nat) (fuel : Nat) (state : State) :
    (run successors fuel state).processed =
      state.processed ++ eagerTrace successors fuel state.admitted state.pending := by
  induction fuel generalizing state with
  | zero => simp [run, eagerTrace]
  | succ fuel ih =>
    rcases state with ⟨processed, pending, admitted⟩
    cases pending with
    | nil => simp [run, eagerTrace]
    | cons head rest =>
      simpa [run, eagerTrace, step, List.append_assoc] using
        (ih (step successors processed head rest admitted))

theorem run_drains (successors : Nat → List Nat) (initial vertices : Finset Nat)
    (closed : ∀ fact ∈ vertices, ∀ next ∈ successors fact, next ∈ vertices)
    (fuel : Nat) (state : State) (h : Invariant initial state)
    (bounded : state.admitted ⊆ vertices)
    (enough : vertices.card ≤ state.processed.length + fuel) :
    (run successors fuel state).pending = [] := by
  induction fuel generalizing state with
  | zero =>
    have bound := frontier_bound initial vertices state h bounded
    simp only [List.length_append] at bound
    have empty : state.pending.length = 0 := by omega
    exact List.length_eq_zero_iff.mp empty
  | succ fuel ih =>
    rcases state with ⟨processed, pending, admitted⟩
    cases pending with
    | nil => rfl
    | cons head rest =>
      apply ih _ (step_invariant successors initial processed head rest admitted h)
      · intro fact hf
        rcases Finset.mem_union.mp hf with old | added
        · exact bounded old
        · have hh : head ∈ admitted := by
            have sets := h.2
            dsimp at sets
            rw [sets]
            apply Finset.mem_union_right
            simp
          exact closed head (bounded hh) fact (List.mem_toFinset.mp added)
      · simp only [step, List.length_append, List.length_singleton]
        dsimp at enough
        omega

theorem completed_facts (successors : Nat → List Nat) (initial vertices : Finset Nat)
    (seeds : List Nat) (initialBound : initial ⊆ vertices)
    (seedBound : ∀ fact ∈ seeds, fact ∈ vertices)
    (closed : ∀ fact ∈ vertices, ∀ next ∈ successors fact, next ∈ vertices) :
    (run successors vertices.card (start initial seeds)).admitted =
      initial ∪ (lazyTrace successors vertices.card initial seeds).toFinset := by
  have inv := run_invariant successors initial vertices.card (start initial seeds)
    (start_invariant initial seeds)
  have drained := run_drains successors initial vertices closed vertices.card (start initial seeds)
    (start_invariant initial seeds) (by
      intro fact hf
      rcases Finset.mem_union.mp hf with hi | hs
      · exact initialBound hi
      · exact seedBound fact (List.mem_toFinset.mp hs)) (by simp [start])
  rw [inv.2, drained, List.append_nil, run_trace]
  simp only [start, List.nil_append, trace_eq]

/-- New Set insertions during expansion; seed insertions happen before this log. -/
def insertionTrace (successors : Nat → List Nat) : Nat → Finset Nat → List Nat → List Nat
  | 0, _, _ => []
  | _, _, [] => []
  | fuel + 1, admitted, head :: rest =>
    let added := admit admitted (successors head)
    added ++ insertionTrace successors fuel (admitted ∪ (successors head).toFinset) (rest ++ added)

theorem run_insertions (successors : Nat → List Nat) (fuel : Nat) (state : State) :
    (run successors fuel state).processed ++ (run successors fuel state).pending =
      (state.processed ++ state.pending) ++
        insertionTrace successors fuel state.admitted state.pending := by
  induction fuel generalizing state with
  | zero => simp [run, insertionTrace]
  | succ fuel ih =>
    rcases state with ⟨processed, pending, admitted⟩
    cases pending with
    | nil => simp [run, insertionTrace]
    | cons head rest =>
      simpa [run, insertionTrace, step, List.append_assoc] using
        (ih (step successors processed head rest admitted))

theorem completed_insertion_order (successors : Nat → List Nat) (initial vertices : Finset Nat)
    (seeds : List Nat) (initialBound : initial ⊆ vertices)
    (seedBound : ∀ fact ∈ seeds, fact ∈ vertices)
    (closed : ∀ fact ∈ vertices, ∀ next ∈ successors fact, next ∈ vertices) :
    admit initial seeds ++ insertionTrace successors vertices.card
      (initial ∪ seeds.toFinset) (admit initial seeds) =
      lazyTrace successors vertices.card initial seeds := by
  have drained := run_drains successors initial vertices closed vertices.card (start initial seeds)
    (start_invariant initial seeds) (by
      intro fact hf
      rcases Finset.mem_union.mp hf with hi | hs
      · exact initialBound hi
      · exact seedBound fact (List.mem_toFinset.mp hs)) (by simp [start])
  have log := run_insertions successors vertices.card (start initial seeds)
  rw [drained, List.append_nil, run_trace] at log
  simpa only [start, List.nil_append, trace_eq] using log.symm

end Reconcile.RequirementPropagation
