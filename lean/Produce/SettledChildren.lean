import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Relation

/-!
# Settled children

`produce`'s finalization asks whether an object needs a new copy (`needsMaterialization` in
`src/finalization.ts`): it walks the object's children, stops at the first one that changed, and
remembers each object it settles as unchanged. `compileImmutable` then walks every unchanged
subtree the result keeps a second time, to register each object in it. The walk here keeps the
child list of each object it walked to the end, so that second walk reads nothing.

A list is kept only when the walk visited every child; a walk that stopped at a changed child
keeps nothing (`check_recorded`). After each top-level question, every object settled as unchanged
has its child list kept, and so do its children, which are settled too (`needs_settled`): a walk
from an unchanged object the result keeps meets only kept lists (`settled_reach_recorded`).

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

/-- `someChild`: checks the children in order and stops at the first that needs a copy. -/
def walk (f : State → Nat → Bool × State) : State → List Nat → Bool × State
  | s, [] => (false, s)
  | s, c :: cs =>
    match f s c with
    | (true, s') => (true, s')
    | (false, s') => walk f s' cs

/-- `checkMaterialization` with `fuel` nested walks; out of fuel it answers that a copy is
needed and keeps nothing. A walk that found no changed child keeps the child list. -/
def check (g : Graph) (o : Oracle) : Nat → State → Nat → Bool × State
  | 0, s, _ => (true, s)
  | fuel + 1, s, n =>
    if o.fact s n then (true, s) else
    match s.memo n with
    | some b => (b, s)
    | none =>
      if o.changed s n then (true, s.settle n true)
      else if n ∈ s.visited then (false, s)
      else
        match walk (check g o fuel) (s.visit n) (g n) with
        | (true, s') => (true, s'.settle n true)
        | (false, s') =>
          if o.after (s'.record n (g n)) n then (true, (s'.record n (g n)).settle n true)
          else (false, s'.record n (g n))

/-- Settles each listed object as unchanged. -/
def settleAll (s : State) : List Nat → State
  | [] => s
  | v :: vs => settleAll (s.settle v false) vs

/-- `needsMaterialization` at the top: a fresh visited set; a negative answer settles every
object the walk visited. -/
def needs (g : Graph) (o : Oracle) (fuel : Nat) (s : State) (n : Nat) : Bool × State :=
  match check g o fuel { s with visited := [] } n with
  | (true, s') => (true, { s' with visited := [] })
  | (false, s') => (false, { settleAll s' s'.visited with visited := [] })

/-- Every kept list is the object's complete child list. -/
def RecOK (g : Graph) (s : State) : Prop := ∀ v l, s.recorded v = some l → l = g v

/-- Every settled object has its list kept, and its children are settled. -/
def Inv (g : Graph) (s : State) : Prop :=
  RecOK g s ∧
    ∀ v, s.memo v = some false → s.recorded v = some (g v) ∧ ∀ c ∈ g v, s.memo c = some false

/-- What every check keeps: complete lists, the settled objects, their kept lists and the
visited objects. -/
def Step (g : Graph) (s s' : State) : Prop :=
  (RecOK g s → RecOK g s') ∧ (∀ v, s'.memo v = some false ↔ s.memo v = some false) ∧
    (∀ v, s.recorded v = some (g v) → s'.recorded v = some (g v)) ∧
    (∀ v ∈ s.visited, v ∈ s'.visited)

theorem Step.refl (g : Graph) (s : State) : Step g s s :=
  ⟨id, fun _ => Iff.rfl, fun _ h => h, fun _ h => h⟩

theorem Step.trans {g : Graph} {s₁ s₂ s₃ : State} (h₁ : Step g s₁ s₂) (h₂ : Step g s₂ s₃) :
    Step g s₁ s₃ :=
  ⟨fun h => h₂.1 (h₁.1 h), fun v => (h₂.2.1 v).trans (h₁.2.1 v),
    fun v h => h₂.2.2.1 v (h₁.2.2.1 v h),
    fun v h => h₂.2.2.2 v (h₁.2.2.2 v h)⟩

theorem step_visit (g : Graph) (s : State) (n : Nat) : Step g s (s.visit n) :=
  ⟨id, fun _ => Iff.rfl, fun _ h => h, fun _ h => List.mem_cons_of_mem _ h⟩

theorem step_record (g : Graph) (s : State) (n : Nat) : Step g s (s.record n (g n)) := by
  refine ⟨fun h v l hv => ?_, fun _ => Iff.rfl, fun v hv => ?_, fun _ h => h⟩
  · by_cases hn : v = n
    · subst hn; simp [State.record] at hv; exact hv.symm
    · exact h v l (by simpa [State.record, Function.update_of_ne hn] using hv)
  · by_cases hn : v = n
    · subst hn; simp [State.record]
    · simpa [State.record, Function.update_of_ne hn] using hv

/-- Settling an object that is not settled unchanged as needing a copy. -/
theorem step_settle (g : Graph) (s : State) (n : Nat) (h : s.memo n ≠ some false) :
    Step g s (s.settle n true) := by
  refine ⟨id, fun v => ?_, fun _ h => h, fun _ h => h⟩
  by_cases hn : v = n
  · subst hn; simp [State.settle, h]
  · simp [State.settle, Function.update_of_ne hn]

/-- A walk keeps what each check keeps. -/
theorem walk_step (g : Graph) (f : State → Nat → Bool × State)
    (hf : ∀ s n, Step g s (f s n).2) : ∀ s l, Step g s (walk f s l).2
  | s, [] => Step.refl g s
  | s, c :: cs => by
    unfold walk
    rcases h : f s c with ⟨b, s'⟩
    cases b
    · exact (by simpa [h] using hf s c : Step g s s').trans (walk_step g f hf s' cs)
    · simpa [h] using hf s c

theorem check_step (g : Graph) (o : Oracle) : ∀ fuel s n, Step g s (check g o fuel s n).2
  | 0, s, _ => Step.refl g s
  | fuel + 1, s, n => by
    unfold check
    by_cases hf : o.fact s n
    · simp [hf, Step.refl]
    simp only [hf]
    rcases hm : s.memo n with _ | b
    · simp only
      by_cases hc : o.changed s n
      · simp [hc, step_settle g s n (by simp [hm])]
      simp only [hc]
      by_cases hv : n ∈ s.visited
      · simp [hv, Step.refl]
      simp only [hv]
      have hw := (step_visit g s n).trans (walk_step g _ (check_step g o fuel) (s.visit n) (g n))
      rcases hwalk : walk (check g o fuel) (s.visit n) (g n) with ⟨b, s'⟩
      rw [hwalk] at hw
      have hn' : s'.memo n ≠ some false := by
        intro h; have := (hw.2.1 n).1 h; simp [hm] at this
      cases b
      · simp only
        have hr := hw.trans (step_record g s' n)
        by_cases ha : o.after (s'.record n (g n)) n
        · simp only [ha, if_true]
          exact hr.trans (step_settle g _ n (by simpa [State.record] using hn'))
        · simp [ha, hr]
      · simpa using hw.trans (step_settle g s' n hn')
    · simp [Step.refl]

/-- A negative answer settles nothing, and each object it newly visited was unsettled, has its
complete list kept, and has each child visited or already settled. -/
def Negative (g : Graph) (s s' : State) : Prop :=
  s'.memo = s.memo ∧ (∀ v ∈ s.visited, v ∈ s'.visited) ∧
    ∀ v ∈ s'.visited, v ∉ s.visited →
      s.memo v = none ∧ s'.recorded v = some (g v) ∧
        ∀ c ∈ g v, c ∈ s'.visited ∨ s.memo c = some false

theorem Negative.refl (g : Graph) (s : State) : Negative g s s :=
  ⟨rfl, fun _ h => h, fun _ h h' => absurd h h'⟩

/-- A walk that found no changed child: each child visited or settled. -/
theorem walk_negative (g : Graph) (f : State → Nat → Bool × State)
    (hstep : ∀ s n, Step g s (f s n).2)
    (hf : ∀ s n s', f s n = (false, s') →
      Negative g s s' ∧ (n ∈ s'.visited ∨ s.memo n = some false)) :
    ∀ s l s', walk f s l = (false, s') →
      Negative g s s' ∧ ∀ c ∈ l, c ∈ s'.visited ∨ s.memo c = some false
  | s, [], s', h => by
    have h' : s = s' := by simpa [walk] using h
    subst h'; exact ⟨Negative.refl g s, by simp⟩
  | s, c :: cs, s', h => by
    unfold walk at h
    rcases hc : f s c with ⟨b, s₁⟩
    rw [hc] at h
    cases b
    · simp only at h
      obtain ⟨⟨hm₁, hv₁, hn₁⟩, hc₁⟩ := hf s c s₁ hc
      obtain ⟨⟨hm₂, hv₂, hn₂⟩, hcs⟩ := walk_negative g f hstep hf s₁ cs s' h
      have hrec := (walk_step g f hstep s₁ cs).2.2.1
      rw [h] at hrec
      refine ⟨⟨hm₂.trans hm₁, fun v hv => hv₂ v (hv₁ v hv), fun v hv hvs => ?_⟩, ?_⟩
      · by_cases hv1 : v ∈ s₁.visited
        · obtain ⟨hnone, hr, hch⟩ := hn₁ v hv1 hvs
          refine ⟨hnone, hrec v hr, fun c' hc' => ?_⟩
          rcases hch c' hc' with h' | h'
          · exact Or.inl (hv₂ c' h')
          · exact Or.inr h'
        · obtain ⟨hnone, hr, hch⟩ := hn₂ v hv hv1
          refine ⟨by rw [← hm₁]; exact hnone, hr, fun c' hc' => ?_⟩
          rcases hch c' hc' with h' | h'
          · exact Or.inl h'
          · exact Or.inr (by rw [← hm₁]; exact h')
      · intro c' hc'
        rcases List.mem_cons.mp hc' with rfl | hc'
        · rcases hc₁ with h' | h'
          · exact Or.inl (hv₂ _ h')
          · exact Or.inr h'
        · rcases hcs c' hc' with h' | h'
          · exact Or.inl h'
          · exact Or.inr (by rw [← hm₁]; exact h')
    · simp at h

theorem check_negative (g : Graph) (o : Oracle) :
    ∀ fuel s n s', check g o fuel s n = (false, s') →
      Negative g s s' ∧ (n ∈ s'.visited ∨ s.memo n = some false)
  | 0, s, n, s', h => by simp [check] at h
  | fuel + 1, s, n, s', h => by
    unfold check at h
    by_cases hf : o.fact s n
    · simp [hf] at h
    simp only [hf] at h
    rcases hm : s.memo n with _ | b
    · rw [hm] at h
      simp only at h
      by_cases hc : o.changed s n
      · simp [hc] at h
      simp only [hc] at h
      by_cases hv : n ∈ s.visited
      · have h' : s = s' := by simpa [hv] using h
        subst h'; exact ⟨Negative.refl g s, Or.inl hv⟩
      simp only [hv] at h
      rcases hwalk : walk (check g o fuel) (s.visit n) (g n) with ⟨b, s₁⟩
      rw [hwalk] at h
      cases b
      · simp only at h
        by_cases ha : o.after (s₁.record n (g n)) n
        · simp [ha] at h
        simp only [ha] at h
        have h' : s₁.record n (g n) = s' := by simpa using h
        subst h'
        obtain ⟨⟨hm₁, hv₁, hn₁⟩, hch⟩ :=
          walk_negative g _ (check_step g o fuel) (check_negative g o fuel) _ _ _ hwalk
        have hnv : n ∈ s₁.visited := hv₁ n (by simp [State.visit])
        refine ⟨⟨by simpa [State.record, State.visit] using hm₁, fun v h' => ?_,
          fun v h' hvs => ?_⟩,
          Or.inl (by simpa [State.record] using hnv)⟩
        · exact by simpa [State.record] using hv₁ v (List.mem_cons_of_mem _ h')
        · simp only [State.record] at h' ⊢
          by_cases hvn : v = n
          · subst hvn
            refine ⟨hm, by simp, fun c hc' => ?_⟩
            rcases hch c hc' with h'' | h''
            · exact Or.inl h''
            · exact Or.inr (by simpa [State.visit] using h'')
          · have hvs' : v ∉ (s.visit n).visited := by simp [State.visit, hvn, hvs]
            obtain ⟨hnone, hr, hch'⟩ := hn₁ v h' hvs'
            refine ⟨by simpa [State.visit] using hnone, by simp [Function.update_of_ne hvn, hr],
              fun c hc' => ?_⟩
            rcases hch' c hc' with h'' | h''
            · exact Or.inl h''
            · exact Or.inr (by simpa [State.visit] using h'')
      · simp at h
    · rw [hm] at h
      have h' : b = false ∧ s = s' := by simpa using h
      obtain ⟨rfl, rfl⟩ := h'
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
  unfold needs
  have hstep := check_step g o fuel { s with visited := [] } n
  rcases hc : check g o fuel { s with visited := [] } n with ⟨b, s'⟩
  rw [hc] at hstep
  obtain ⟨hrec, hmemo, hkept, -⟩ := hstep
  cases b
  · obtain ⟨⟨hm, -, hnew⟩, -⟩ := check_negative g o fuel _ n s' hc
    simp only at hm hnew
    refine ⟨fun v l hv => hrec h.1 v l (by simpa [settleAll_recorded] using hv), fun v hv => ?_⟩
    simp only [settleAll_memo, settleAll_recorded] at hv ⊢
    by_cases hvis : v ∈ s'.visited
    · obtain ⟨-, hr, hch⟩ := hnew v hvis (by simp)
      refine ⟨hr, fun c hc' => ?_⟩
      rcases hch c hc' with h' | h'
      · simp [h']
      · by_cases hcv : c ∈ s'.visited
        · simp [hcv]
        · simp [hcv, hm, h']
    · simp only [hvis, if_false, hm] at hv
      obtain ⟨hr, hch⟩ := h.2 v hv
      refine ⟨hkept v hr, fun c hc' => ?_⟩
      by_cases hcv : c ∈ s'.visited
      · simp [hcv]
      · simp [hcv, hm, hch c hc']
  · refine ⟨hrec h.1, fun v hv => ?_⟩
    simp only at hv ⊢
    have hv' := (hmemo v).1 hv
    obtain ⟨hr, hch⟩ := h.2 v hv'
    exact ⟨hkept v hr, fun c hc' => (hmemo c).2 (hch c hc')⟩

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

/-- Keeping the children a walk saw before it stopped would keep a prefix: here object 0's walk
stops at the changed object 1 before reading object 2. -/
def stoppedPrefix (g : Graph) (changed : Nat → Bool) : List Nat → List Nat
  | [] => []
  | c :: cs => if changed c then [c] else c :: stoppedPrefix g changed cs

example : stoppedPrefix (fun _ => []) (· == 1) [1, 2] ≠ [1, 2] := by decide

/-- A cycle: object 0 reaches itself through 1; one question settles both and keeps both lists. -/
example :
    let g : Graph := fun n => if n = 0 then [1] else if n = 1 then [0] else []
    let o : Oracle :=
      { fact := fun _ _ => false, changed := fun _ _ => false, after := fun _ _ => false }
    let s := (needs g o 4 initial 0).2
    (needs g o 4 initial 0).1 = false ∧ s.memo 1 = some false ∧ s.recorded 1 = some [0] := by
  decide

end Reconcile.SettledChildren
