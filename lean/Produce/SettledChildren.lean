import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Relation

/-!
# Settled children

`produce`'s finalization asks whether an object needs a new copy (`needsMaterialization` in
`src/finalization.ts`): it walks the object's children, stops at the first one that changed, and
remembers each object it settles as unchanged. Two repeated walks are avoided here.

- **Kept lists.** A walk keeps the child list of each object it walked to the end, so identity
  restoration, which registers every object of an unchanged subtree the result keeps, reads no
  list again. A walk that stopped at a changed child keeps nothing, so every kept list is
  complete (`recorded_getD`).
- **Early settling.** A negative answer settles its object at once, unless it leaned on a visited
  object not yet settled, which only a cycle back into the current walk produces. Such a
  *pending* answer stays unsettled until the question's answer is known; settling the others at
  once spares a later question from walking them again when the question itself turns out
  positive.

Every check keeps the invariant that each settled object has its list kept and settled children
(`check_step`, `needs_settled`), so a walk from an unchanged object meets only kept lists
(`settled_reach_recorded`). With the changed objects fixed, a settled object reaches none of them
(`needs_unchanged`): settling early never answers wrongly.

The runtime's other answers, a closure fact, a changed object and a change found after the walk,
are questions to `Oracle`, which may depend on the state. That repeated reads of an object list
the same children is the runtime's stability obligation.
-/

namespace Reconcile.SettledChildren

/-- The object children of each object, in slot order, as one complete read lists them. -/
abbrev Graph := Nat → List Nat

/-- One finalization phase's walk state: the current question's visited objects, the settled
answers and the kept child lists. -/
structure State where
  visited : List Nat
  memo : Nat → Option Bool
  recorded : Nat → Option (List Nat)

/-- The runtime's answers besides the walk. -/
structure Oracle where
  /-- A closure fact: the object needs a copy, asked before the memo. -/
  fact : State → Nat → Bool
  /-- A changed object, a special value with a copy, and the like. -/
  changed : State → Nat → Bool
  /-- A change the walk itself caused, such as a getter's write or an observed accessor. -/
  after : State → Nat → Bool

namespace State

def visit (s : State) (n : Nat) : State := { s with visited := n :: s.visited }

def settle (s : State) (n : Nat) (b : Bool) : State :=
  { s with memo := Function.update s.memo n (some b) }

def record (s : State) (n : Nat) (l : List Nat) : State :=
  { s with recorded := Function.update s.recorded n (some l) }

end State

/-- A check's answer, whether a negative answer leaned on a visited object not yet settled, and
the state after it. -/
structure Result where
  needs : Bool
  pending : Bool
  state : State

/-- `someChild`: checks the children in order and stops at the first that needs a copy. -/
def walk (f : State → Nat → Result) : State → List Nat → Result
  | s, [] => ⟨false, false, s⟩
  | s, c :: cs =>
    let r := f s c
    if r.needs then r
    else
      let r' := walk f r.state cs
      ⟨r'.needs, r.pending || r'.pending, r'.state⟩

/-- `checkState` with `fuel` nested walks; out of fuel it answers that a copy is
needed and keeps nothing. A walk that found no changed child keeps the child list, and settles
the object unless it is pending. -/
def check (g : Graph) (o : Oracle) : Nat → State → Nat → Result
  | 0, s, _ => ⟨true, false, s⟩
  | fuel + 1, s, n =>
    if o.fact s n then ⟨true, false, s⟩ else
    match s.memo n with
    | some b => ⟨b, false, s⟩
    | none =>
      if o.changed s n then ⟨true, false, s.settle n true⟩
      else if n ∈ s.visited then ⟨false, true, s⟩
      else
        let r := walk (check g o fuel) (s.visit n) (g n)
        if r.needs then ⟨true, false, r.state.settle n true⟩
        else if o.after (r.state.record n (g n)) n then
          ⟨true, false, (r.state.record n (g n)).settle n true⟩
        else if r.pending then ⟨false, true, r.state.record n (g n)⟩
        else ⟨false, false, (r.state.record n (g n)).settle n false⟩

/-- Settles each listed object as unchanged. -/
def settleAll (s : State) : List Nat → State
  | [] => s
  | v :: vs => settleAll (s.settle v false) vs

/-- `needsMaterialization` at the top: a fresh visited set; a negative answer settles every
object the walk visited. -/
def needs (g : Graph) (o : Oracle) (fuel : Nat) (s : State) (n : Nat) : Bool × State :=
  let r := check g o fuel { s with visited := [] } n
  if r.needs then (true, { r.state with visited := [] })
  else (false, { settleAll r.state r.state.visited with visited := [] })

/-- Every kept list is the object's complete child list. -/
def RecOK (g : Graph) (s : State) : Prop := ∀ v l, s.recorded v = some l → l = g v

/-- Every settled object has its list kept, and its children are settled. -/
def Inv (g : Graph) (s : State) : Prop :=
  RecOK g s ∧
    ∀ v, s.memo v = some false → s.recorded v = some (g v) ∧ ∀ c ∈ g v, s.memo c = some false

/-- What every check keeps: complete lists, the invariant, settled objects, which are new only
among the objects it visited, their kept lists and the visited objects. -/
def Step (g : Graph) (s s' : State) : Prop :=
  (RecOK g s → RecOK g s') ∧ (Inv g s → Inv g s') ∧
    (∀ v, s.memo v = some false → s'.memo v = some false) ∧
    (∀ v, s'.memo v = some false → s.memo v = some false ∨ v ∉ s.visited) ∧
    (∀ v, s.recorded v = some (g v) → s'.recorded v = some (g v)) ∧
    (∀ v ∈ s.visited, v ∈ s'.visited)

theorem Step.refl (g : Graph) (s : State) : Step g s s :=
  ⟨id, id, fun _ h => h, fun _ h => Or.inl h, fun _ h => h, fun _ h => h⟩

theorem Step.trans {g : Graph} {s₁ s₂ s₃ : State} (h₁ : Step g s₁ s₂) (h₂ : Step g s₂ s₃) :
    Step g s₁ s₃ := by
  obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂, f₂⟩ := h₂
  refine ⟨a₂ ∘ a₁, b₂ ∘ b₁, fun v h => c₂ v (c₁ v h), fun v h => ?_, fun v h => e₂ v (e₁ v h),
    fun v h => f₂ v (f₁ v h)⟩
  rcases d₂ v h with h' | h'
  · exact d₁ v h'
  · exact Or.inr fun hv => h' (f₁ v hv)

theorem step_visit (g : Graph) (s : State) (n : Nat) : Step g s (s.visit n) :=
  ⟨id, fun h => h, fun _ h => h, fun _ h => Or.inl h, fun _ h => h,
    fun _ h => List.mem_cons_of_mem _ h⟩

theorem recOK_record (g : Graph) (s : State) (n : Nat) (h : RecOK g s) :
    RecOK g (s.record n (g n)) := by
  intro v l hv
  by_cases hn : v = n
  · subst hn; simp [State.record] at hv; exact hv.symm
  · exact h v l (by simpa [State.record, Function.update_of_ne hn] using hv)

theorem record_kept (g : Graph) (s : State) (n v : Nat) (h : s.recorded v = some (g v)) :
    (s.record n (g n)).recorded v = some (g v) := by
  by_cases hn : v = n
  · subst hn; simp [State.record]
  · simpa [State.record, Function.update_of_ne hn] using h

theorem step_record (g : Graph) (s : State) (n : Nat) : Step g s (s.record n (g n)) :=
  ⟨recOK_record g s n, fun h => ⟨recOK_record g s n h.1, fun v hv =>
    ⟨record_kept g s n v (h.2 v hv).1, (h.2 v hv).2⟩⟩, fun _ h => h, fun _ h => Or.inl h,
    fun v h => record_kept g s n v h, fun _ h => h⟩

/-- Settling an object that is not settled unchanged as needing a copy. -/
theorem step_settle (g : Graph) (s : State) (n : Nat) (h : s.memo n ≠ some false) :
    Step g s (s.settle n true) := by
  have hfalse : ∀ v, (s.settle n true).memo v = some false ↔ s.memo v = some false := by
    intro v
    by_cases hn : v = n
    · subst hn; simp [State.settle, h]
    · simp [State.settle, Function.update_of_ne hn]
  refine ⟨id, fun hi => ⟨hi.1, fun v hv => ?_⟩, fun v hv => (hfalse v).2 hv,
    fun v hv => Or.inl ((hfalse v).1 hv), fun _ h => h, fun _ h => h⟩
  obtain ⟨hr, hc⟩ := hi.2 v ((hfalse v).1 hv)
  exact ⟨hr, fun c hc' => (hfalse c).2 (hc c hc')⟩

/-- Settling unchanged an object the check did not visit before, whose list is kept and whose
children are settled. -/
theorem Step.settle_false {g : Graph} {s₀ s : State} {n : Nat} (h : Step g s₀ s)
    (hv : n ∉ s₀.visited) (hr : s.recorded n = some (g n)) (hc : ∀ c ∈ g n, s.memo c = some false) :
    Step g s₀ (s.settle n false) := by
  have hmemo : ∀ v, (s.settle n false).memo v = some false ↔ v = n ∨ s.memo v = some false := by
    intro v
    by_cases hn : v = n
    · subst hn; simp [State.settle]
    · simp [State.settle, hn]
  obtain ⟨ha, hi, hk, hnew, hrec, hvis⟩ := h
  refine ⟨ha, fun h₀ => ⟨(hi h₀).1, fun v hv' => ?_⟩, fun v h' => (hmemo v).2 (Or.inr (hk v h')),
    fun v h' => ?_, hrec, hvis⟩
  · rcases (hmemo v).1 hv' with rfl | h'
    · exact ⟨hr, fun c hc' => (hmemo c).2 (Or.inr (hc c hc'))⟩
    · exact ⟨((hi h₀).2 v h').1, fun c hc' => (hmemo c).2 (Or.inr (((hi h₀).2 v h').2 c hc'))⟩
  · rcases (hmemo v).1 h' with rfl | h'
    · exact Or.inr hv
    · exact hnew v h'

/-- A walk keeps what each check keeps, and a negative answer that is not pending settles every
child. -/
theorem walk_step (g : Graph) (f : State → Nat → Result)
    (hf : ∀ s n, Step g s (f s n).state ∧
      ((f s n).needs = false → (f s n).pending = false → (f s n).state.memo n = some false)) :
    ∀ s l, Step g s (walk f s l).state ∧
      ((walk f s l).needs = false → (walk f s l).pending = false →
        ∀ c ∈ l, (walk f s l).state.memo c = some false)
  | s, [] => ⟨Step.refl g s, fun _ _ c hc => by simp at hc⟩
  | s, c :: cs => by
    obtain ⟨hs, hset⟩ := hf s c
    cases hn : (f s c).needs
    · simp only [walk, hn, Bool.false_eq_true, if_false]
      obtain ⟨hs', hset'⟩ := walk_step g f hf (f s c).state cs
      refine ⟨hs.trans hs', fun hneeds hpend c' hc' => ?_⟩
      have hpend' : (f s c).pending = false ∧ (walk f (f s c).state cs).pending = false := by
        simpa using hpend
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact hs'.2.2.1 _ (hset hn hpend'.1)
      · exact hset' hneeds hpend'.2 c' hc'
    · simp only [walk, hn, if_true]
      exact ⟨hs, fun h => by simp at h⟩

/-- A walk keeps what each check keeps. -/
theorem walk_step_state (g : Graph) (f : State → Nat → Result)
    (hf : ∀ s n, Step g s (f s n).state) :
    ∀ s l, Step g s (walk f s l).state
  | s, [] => Step.refl g s
  | s, c :: cs => by
    cases hn : (f s c).needs
    · simp only [walk, hn, Bool.false_eq_true, if_false]
      exact (hf s c).trans (walk_step_state g f hf _ cs)
    · simp only [walk, hn, if_true]
      exact hf s c

theorem check_step (g : Graph) (o : Oracle) : ∀ fuel s n,
    Step g s (check g o fuel s n).state ∧
      ((check g o fuel s n).needs = false → (check g o fuel s n).pending = false →
        (check g o fuel s n).state.memo n = some false)
  | 0, s, _ => ⟨Step.refl g s, fun h => by simp [check] at h⟩
  | fuel + 1, s, n => by
    by_cases hf : o.fact s n
    · simp only [check, hf, if_true]
      exact ⟨Step.refl g s, fun h => by simp at h⟩
    rcases hm : s.memo n with _ | b
    · by_cases hc : o.changed s n
      · simp only [check, Bool.false_eq_true, if_false, hf, hm, hc, if_true]
        exact ⟨step_settle g s n (by simp [hm]), fun h => by simp at h⟩
      by_cases hv : n ∈ s.visited
      · simp only [check, Bool.false_eq_true, if_false, hf, hm, hc, hv, if_true]
        exact ⟨Step.refl g s, fun _ h => by simp at h⟩
      obtain ⟨hw, hset⟩ := walk_step g _ (check_step g o fuel) (s.visit n) (g n)
      have hw' := (step_visit g s n).trans hw
      rcases hwalk : walk (check g o fuel) (s.visit n) (g n) with ⟨b, p, s'⟩
      rw [hwalk] at hw hw' hset
      have hn' : s'.memo n ≠ some false := by
        intro h
        rcases hw.2.2.2.1 n h with h' | h'
        · simp [State.visit, hm] at h'
        · exact h' (by simp [State.visit])
      have hrec := hw'.trans (step_record g s' n)
      cases b
      · by_cases ha : o.after (s'.record n (g n)) n
        · simp only [check, Bool.false_eq_true, if_false, hf, hm, hc, hv, hwalk, ha, if_true]
          exact ⟨hrec.trans (step_settle g _ n (by simpa [State.record] using hn')),
            fun h => by simp at h⟩
        cases p
        · simp only [check, Bool.false_eq_true, if_false, hf, hm, hc, hv, hwalk, ha]
          have hch : ∀ c ∈ g n, (s'.record n (g n)).memo c = some false := fun c hc' =>
            by simpa [State.record] using hset rfl rfl c hc'
          exact ⟨hrec.settle_false hv (by simp [State.record]) hch,
            fun _ _ => by simp [State.settle]⟩
        · simp only [check, Bool.false_eq_true, if_false, hf, hm, hc, hv, hwalk, ha, if_true]
          exact ⟨hrec, fun _ h => by simp at h⟩
      · simp only [check, Bool.false_eq_true, if_false, hf, hm, hc, hv, hwalk, if_true]
        exact ⟨hw'.trans (step_settle g s' n hn'), fun h => by simp at h⟩
    · simp only [check, Bool.false_eq_true, if_false, hf, hm]
      exact ⟨Step.refl g s, fun hb _ => by simp_all⟩

/-- A negative answer's newly visited objects have their lists kept and each child visited or
settled. -/
def Negative (g : Graph) (s s' : State) : Prop :=
  ∀ v ∈ s'.visited, v ∉ s.visited →
    s'.recorded v = some (g v) ∧ ∀ c ∈ g v, c ∈ s'.visited ∨ s'.memo c = some false

theorem Negative.refl (g : Graph) (s : State) : Negative g s s := fun _ h h' => absurd h h'

/-- A later step that visits nothing new, keeps settled objects and kept lists keeps a negative
answer's facts. -/
theorem Negative.keep {g : Graph} {s s₁ s₂ : State} (h : Negative g s s₁)
    (hm : ∀ c, s₁.memo c = some false → s₂.memo c = some false)
    (hr : ∀ v, s₁.recorded v = some (g v) → s₂.recorded v = some (g v))
    (hv : s₂.visited = s₁.visited) : Negative g s s₂ := by
  intro v hv₂ hvs
  rw [hv] at hv₂
  obtain ⟨hr', hc⟩ := h v hv₂ hvs
  refine ⟨hr v hr', fun c hc' => ?_⟩
  rcases hc c hc' with h' | h'
  · exact Or.inl (by rw [hv]; exact h')
  · exact Or.inr (hm c h')

theorem Negative.trans {g : Graph} {s₁ s₂ s₃ : State} (h₁ : Negative g s₁ s₂)
    (h₂ : Negative g s₂ s₃) (hs : Step g s₂ s₃) : Negative g s₁ s₃ := by
  intro v hv₃ hvs
  by_cases hv₂ : v ∈ s₂.visited
  · obtain ⟨hr, hc⟩ := h₁ v hv₂ hvs
    refine ⟨hs.2.2.2.2.1 v hr, fun c hc' => ?_⟩
    rcases hc c hc' with h' | h'
    · exact Or.inl (hs.2.2.2.2.2 c h')
    · exact Or.inr (hs.2.2.1 c h')
  · exact h₂ v hv₃ hv₂

theorem walk_negative (g : Graph) (f : State → Nat → Result)
    (hstep : ∀ s n, Step g s (f s n).state)
    (hf : ∀ s n, (f s n).needs = false →
      Negative g s (f s n).state ∧
        (n ∈ (f s n).state.visited ∨ (f s n).state.memo n = some false)) :
    ∀ s l, (walk f s l).needs = false →
      Negative g s (walk f s l).state ∧
        ∀ c ∈ l, c ∈ (walk f s l).state.visited ∨ (walk f s l).state.memo c = some false
  | s, [], _ => ⟨Negative.refl g s, fun _ h => by simp at h⟩
  | s, c :: cs, h => by
    cases hn : (f s c).needs
    · simp only [walk, hn, Bool.false_eq_true, if_false] at h ⊢
      obtain ⟨h₁, hc₁⟩ := hf s c hn
      obtain ⟨h₂, hcs⟩ := walk_negative g f hstep hf (f s c).state cs h
      have hs₂ := walk_step_state g f hstep (f s c).state cs
      refine ⟨h₁.trans h₂ hs₂, fun c' hc' => ?_⟩
      rcases List.mem_cons.mp hc' with rfl | hc'
      · rcases hc₁ with h' | h'
        · exact Or.inl (hs₂.2.2.2.2.2 _ h')
        · exact Or.inr (hs₂.2.2.1 _ h')
      · exact hcs c' hc'
    · simp [walk, hn] at h

theorem check_negative (g : Graph) (o : Oracle) : ∀ fuel s n,
    (check g o fuel s n).needs = false →
      Negative g s (check g o fuel s n).state ∧
        (n ∈ (check g o fuel s n).state.visited ∨ (check g o fuel s n).state.memo n = some false)
  | 0, s, n, h => by simp [check] at h
  | fuel + 1, s, n, h => by
    by_cases hf : o.fact s n
    · simp [check, hf] at h
    rcases hm : s.memo n with _ | b
    · by_cases hc : o.changed s n
      · simp [check, hf, hm, hc] at h
      by_cases hv : n ∈ s.visited
      · simp only [check, Bool.false_eq_true, if_false, hf, hm, hc, hv, if_true]
        exact ⟨Negative.refl g s, Or.inl trivial⟩
      have hstep : ∀ s' n', Step g s' (check g o fuel s' n').state := fun s' n' =>
        (check_step g o fuel s' n').1
      have hwn := walk_negative g _ hstep (check_negative g o fuel) (s.visit n) (g n)
      have hws := walk_step_state g _ hstep (s.visit n) (g n)
      rcases hwalk : walk (check g o fuel) (s.visit n) (g n) with ⟨b, p, s'⟩
      rw [hwalk] at hwn hws
      cases b
      · obtain ⟨hneg, hch⟩ := hwn rfl
        -- The object itself: its list kept, each child visited or settled.
        have hn : ∀ s'', s''.visited = s'.visited →
            (∀ c, s'.memo c = some false → s''.memo c = some false) →
            (∀ v, s'.recorded v = some (g v) → s''.recorded v = some (g v)) →
            s''.recorded n = some (g n) → Negative g s s'' ∧ n ∈ s''.visited := by
          intro s'' hvis hmemo hrecs hrec
          refine ⟨fun v hv'' hvs => ?_, by rw [hvis]; exact hws.2.2.2.2.2 n (by simp [State.visit])⟩
          by_cases hvn : v = n
          · subst hvn
            refine ⟨hrec, fun c hc' => ?_⟩
            rcases hch c hc' with h' | h'
            · exact Or.inl (by rw [hvis]; exact h')
            · exact Or.inr (hmemo c h')
          · have hv' : v ∉ (s.visit n).visited := by simp [State.visit, hvn, hvs]
            exact (hneg.keep hmemo hrecs hvis) v hv'' hv'
        by_cases ha : o.after (s'.record n (g n)) n
        · simp [check, hf, hm, hc, hv, hwalk, ha] at h
        cases p
        · simp only [check, Bool.false_eq_true, if_false, hf, hm, hc, hv, hwalk, ha]
          refine (hn ((s'.record n (g n)).settle n false) (by simp [State.settle, State.record])
            (fun c h' => ?_) (fun v h' => ?_)
            (by simp [State.record, State.settle])).imp_right Or.inl
          · by_cases hcn : c = n
            · subst hcn; simp [State.settle]
            · simpa [State.settle, State.record, Function.update_of_ne hcn] using h'
          · simpa [State.settle] using record_kept g s' n v h'
        · simp only [check, Bool.false_eq_true, if_false, hf, hm, hc, hv, hwalk, ha, if_true]
          exact (hn (s'.record n (g n)) (by simp [State.record])
            (fun c h' => by simpa [State.record] using h')
            (fun v h' => record_kept g s' n v h') (by simp [State.record])).imp_right Or.inl
      · simp [check, hf, hm, hc, hv, hwalk] at h
    · simp only [check, Bool.false_eq_true, if_false, hf, hm] at h ⊢
      subst h
      exact ⟨Negative.refl g s, Or.inr rfl⟩

theorem settleAll_memo (s : State) (l : List Nat) (v : Nat) :
    (settleAll s l).memo v = if v ∈ l then some false else s.memo v := by
  induction l generalizing s with
  | nil => simp [settleAll]
  | cons w ws ih =>
    simp only [settleAll, ih, State.settle, List.mem_cons]
    by_cases hv : v ∈ ws
    · simp [hv]
    · by_cases hw : v = w
      · subst hw; simp [hv]
      · simp [hv, hw]

theorem settleAll_recorded (s : State) (l : List Nat) : (settleAll s l).recorded = s.recorded := by
  induction l generalizing s with
  | nil => rfl
  | cons w ws ih => simp [settleAll, ih, State.settle]

/-- Each top-level question keeps the invariant: kept lists are complete, and every settled
object has its list kept and settled children. -/
theorem needs_settled (g : Graph) (o : Oracle) (fuel : Nat) (s : State) (n : Nat)
    (h : Inv g s) : Inv g (needs g o fuel s n).2 := by
  have hi : Inv g (check g o fuel { s with visited := [] } n).state :=
    (check_step g o fuel { s with visited := [] } n).1.2.1 h
  cases hn : (check g o fuel { s with visited := [] } n).needs
  · obtain ⟨hneg, -⟩ := check_negative g o fuel _ n hn
    have hgoal : (needs g o fuel s n).2 =
        { settleAll (check g o fuel { s with visited := [] } n).state
          (check g o fuel { s with visited := [] } n).state.visited with visited := [] } := by
      simp [needs, hn]
    rw [hgoal]
    generalize (check g o fuel { s with visited := [] } n).state = s' at hneg hi ⊢
    refine ⟨fun v l hv => hi.1 v l (by simpa [settleAll_recorded] using hv), fun v hv => ?_⟩
    simp only [settleAll_memo, settleAll_recorded] at hv ⊢
    have hsettled : ∀ c, s'.memo c = some false →
        (if c ∈ s'.visited then some false else s'.memo c) = some false := by
      intro c hc; split <;> simp [hc]
    by_cases hvis : v ∈ s'.visited
    · obtain ⟨hr, hch⟩ := hneg v hvis (by simp)
      refine ⟨hr, fun c hc' => ?_⟩
      rcases hch c hc' with h' | h'
      · simp [h']
      · exact hsettled c h'
    · simp only [hvis, if_false] at hv
      obtain ⟨hr, hch⟩ := hi.2 v hv
      exact ⟨hr, fun c hc' => hsettled c (hch c hc')⟩
  · have hgoal : (needs g o fuel s n).2 =
        { (check g o fuel { s with visited := [] } n).state with visited := [] } := by
      simp [needs, hn]
    rw [hgoal]
    exact hi

/-- The empty state, before any question. -/
def initial : State := { visited := [], memo := fun _ => none, recorded := fun _ => none }

theorem initial_inv (g : Graph) : Inv g initial := by
  constructor <;> intro v <;> simp [initial]

/-- The list a later walk uses: the kept one, or a fresh read. Kept lists are complete, so it is
always the object's child list. -/
theorem recorded_getD (g : Graph) (s : State) (h : RecOK g s) (v : Nat) :
    (s.recorded v).getD (g v) = g v := by
  rcases hv : s.recorded v with _ | l
  · rfl
  · simp [h v l hv]

/-- From a settled object, every object a walk reaches is settled and has its list kept, so a
walk of an unchanged subtree the result keeps reads no child list again. -/
theorem settled_reach_recorded (g : Graph) (s : State) (h : Inv g s) {v u : Nat}
    (hv : s.memo v = some false) (hu : Relation.ReflTransGen (fun a b => b ∈ g a) v u) :
    s.memo u = some false ∧ s.recorded u = some (g u) := by
  induction hu with
  | refl => exact ⟨hv, (h.2 v hv).1⟩
  | tail _ hb ih =>
    have hc := (h.2 _ ih.1).2 _ hb
    exact ⟨hc, (h.2 _ hc).1⟩

/-- No settled object is one of the changed objects `c`. -/
def Sound (c : Nat → Bool) (s : State) : Prop := ∀ v, s.memo v = some false → c v = false

/-- With the changed objects fixed, a check settles only unchanged objects, and visits only
objects that are not changed. -/
def StepSound (c : Nat → Bool) (s s' : State) : Prop :=
  (Sound c s → Sound c s') ∧ (∀ v ∈ s'.visited, v ∉ s.visited → c v = false) ∧
    (∀ v ∈ s.visited, v ∈ s'.visited)

theorem StepSound.refl (c : Nat → Bool) (s : State) : StepSound c s s :=
  ⟨id, fun _ h h' => absurd h h', fun _ h => h⟩

theorem StepSound.trans {c : Nat → Bool} {s₁ s₂ s₃ : State} (h₁ : StepSound c s₁ s₂)
    (h₂ : StepSound c s₂ s₃) : StepSound c s₁ s₃ :=
  ⟨h₂.1 ∘ h₁.1, fun v hv hv₁ => if h : v ∈ s₂.visited then h₁.2.1 v h hv₁ else h₂.2.1 v hv h,
    fun v h => h₂.2.2 v (h₁.2.2 v h)⟩

theorem stepSound_record (c : Nat → Bool) (s : State) (n : Nat) (l : List Nat) :
    StepSound c s (s.record n l) :=
  ⟨fun h v hv => h v (by simpa [State.record] using hv), fun _ h h' => absurd h h', fun _ h => h⟩

theorem stepSound_settle (c : Nat → Bool) (s : State) (n : Nat) (b : Bool)
    (hb : b = false → c n = false) : StepSound c s (s.settle n b) := by
  refine ⟨fun h v hv => ?_, fun _ h h' => absurd h h', fun _ h => h⟩
  by_cases hvn : v = n
  · subst hvn
    exact hb (by simpa [State.settle] using hv)
  · exact h v (by simpa [State.settle, Function.update_of_ne hvn] using hv)

theorem walk_sound (c : Nat → Bool) (f : State → Nat → Result)
    (hf : ∀ s n, StepSound c s (f s n).state) : ∀ s l, StepSound c s (walk f s l).state
  | s, [] => StepSound.refl c s
  | s, d :: ds => by
    cases hn : (f s d).needs
    · simp only [walk, hn, Bool.false_eq_true, if_false]
      exact (hf s d).trans (walk_sound c f hf _ ds)
    · simp only [walk, hn, if_true]
      exact hf s d

theorem check_sound (g : Graph) (o : Oracle) (c : Nat → Bool) (hc : ∀ s n, o.changed s n = c n) :
    ∀ fuel s n, StepSound c s (check g o fuel s n).state
  | 0, s, _ => StepSound.refl c s
  | fuel + 1, s, n => by
    by_cases hf : o.fact s n
    · simp only [check, hf, if_true]; exact StepSound.refl c s
    rcases hm : s.memo n with _ | b
    · by_cases hch : o.changed s n
      · simp only [check, Bool.false_eq_true, if_false, hf, hm, hch, if_true]
        exact stepSound_settle c s n true (by simp)
      have hcn : c n = false := by simpa [hc] using hch
      by_cases hv : n ∈ s.visited
      · simp only [check, Bool.false_eq_true, if_false, hf, hm, hch, hv, if_true]
        exact StepSound.refl c s
      have hvisit : StepSound c s (s.visit n) := ⟨fun h => h, fun v hv' hvs => by
          rcases (by simpa [State.visit] using hv' : v = n ∨ v ∈ s.visited) with rfl | hv'
          · exact hcn
          · exact absurd hv' hvs,
        fun _ h => List.mem_cons_of_mem _ h⟩
      have hw := hvisit.trans (walk_sound c _ (check_sound g o c hc fuel) (s.visit n) (g n))
      rcases hwalk : walk (check g o fuel) (s.visit n) (g n) with ⟨b, p, s'⟩
      rw [hwalk] at hw
      have hr := hw.trans (stepSound_record c s' n (g n))
      cases b
      · by_cases ha : o.after (s'.record n (g n)) n
        · simp only [check, Bool.false_eq_true, if_false, hf, hm, hch, hv, hwalk, ha, if_true]
          exact hr.trans (stepSound_settle c _ n true (by simp))
        cases p
        · simp only [check, Bool.false_eq_true, if_false, hf, hm, hch, hv, hwalk, ha]
          exact hr.trans (stepSound_settle c _ n false fun _ => hcn)
        · simp only [check, Bool.false_eq_true, if_false, hf, hm, hch, hv, hwalk, ha, if_true]
          exact hr
      · simp only [check, Bool.false_eq_true, if_false, hf, hm, hch, hv, hwalk, if_true]
        exact hw.trans (stepSound_settle c s' n true (by simp))
    · simp only [check, Bool.false_eq_true, if_false, hf, hm]; exact StepSound.refl c s

/-- With the changed objects fixed, every question settles only unchanged objects. -/
theorem needs_sound (g : Graph) (o : Oracle) (c : Nat → Bool) (hc : ∀ s n, o.changed s n = c n)
    (fuel : Nat) (s : State) (n : Nat) (h : Sound c s) : Sound c (needs g o fuel s n).2 := by
  have hs := check_sound g o c hc fuel { s with visited := [] } n
  cases hn : (check g o fuel { s with visited := [] } n).needs
  · have hgoal : (needs g o fuel s n).2 =
        { settleAll (check g o fuel { s with visited := [] } n).state
          (check g o fuel { s with visited := [] } n).state.visited with visited := [] } := by
      simp [needs, hn]
    rw [hgoal]
    intro v hv
    simp only [settleAll_memo] at hv
    split at hv
    · next hvis => exact hs.2.1 v hvis (by simp)
    · exact hs.1 h v hv
  · have hgoal : (needs g o fuel s n).2 =
        { (check g o fuel { s with visited := [] } n).state with visited := [] } := by
      simp [needs, hn]
    rw [hgoal]
    exact hs.1 h

/-- A negative answer reaches no changed object: settling early never answers wrongly. -/
theorem needs_unchanged (g : Graph) (o : Oracle) (c : Nat → Bool) (hc : ∀ s n, o.changed s n = c n)
    (fuel : Nat) (s : State) (n : Nat) (hi : Inv g s) (hs : Sound c s)
    (h : (needs g o fuel s n).1 = false) {u : Nat}
    (hu : Relation.ReflTransGen (fun a b => b ∈ g a) n u) :
    c u = false := by
  have hinv := needs_settled g o fuel s n hi
  have hsound := needs_sound g o c hc fuel s n hs
  have hn : (needs g o fuel s n).2.memo n = some false := by
    cases hr : (check g o fuel { s with visited := [] } n).needs
    · have hgoal : (needs g o fuel s n).2.memo n =
          (settleAll (check g o fuel { s with visited := [] } n).state
            (check g o fuel { s with visited := [] } n).state.visited).memo n := by
        simp [needs, hr]
      rw [hgoal, settleAll_memo]
      rcases (check_negative g o fuel _ n hr).2 with h' | h'
      · simp [h']
      · split <;> simp [h']
    · simp [needs, hr] at h
  exact hsound u (settled_reach_recorded g _ hinv hn hu).1

/-- The oracle the examples use: object 2 changed, nothing else. -/
def changedTwo : Oracle :=
  { fact := fun _ _ => false, changed := fun _ n => n == 2, after := fun _ _ => false }

/-- An unchanged sibling before a changed one: the question is positive, and object 1 is settled
at once, so a later question does not walk it again. -/
example :
    let g : Graph := fun n => if n = 0 then [1, 2] else []
    (needs g changedTwo 4 initial 0).1 = true ∧
      (needs g changedTwo 4 initial 0).2.memo 1 = some false := by
  decide

/-- A cycle back into the walk: object 1 leans on object 0, still being walked, and object 0 then
finds the changed object 2. Object 1 is pending, so it stays unsettled; settling it would be
wrong, since it reaches object 2 through object 0. -/
example :
    let g : Graph := fun n => if n = 0 then [1, 2] else if n = 1 then [0] else []
    (needs g changedTwo 4 initial 0).1 = true ∧
      (needs g changedTwo 4 initial 0).2.memo 1 = none := by
  decide

/-- A cycle without a change: one question settles both objects and keeps both lists. -/
example :
    let g : Graph := fun n => if n = 0 then [1] else if n = 1 then [0] else []
    let s := (needs g changedTwo 4 initial 0).2
    (needs g changedTwo 4 initial 0).1 = false ∧ s.memo 1 = some false ∧
      s.recorded 1 = some [0] := by
  decide

/-- Keeping the children a walk saw before it stopped would keep a prefix: here object 0's walk
stops at the changed object 1 before reading object 2. -/
def stoppedPrefix (changed : Nat → Bool) : List Nat → List Nat
  | [] => []
  | c :: cs => if changed c then [c] else c :: stoppedPrefix changed cs

example : stoppedPrefix (· == 1) [1, 2] ≠ [1, 2] := by decide

end Reconcile.SettledChildren
