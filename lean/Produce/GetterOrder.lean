import Batteries.Data.List.Perm
import Serialization.DFS

/-!
# Getter order

After the recipe returns, `produce` calls each own getter of the result once, in depth-first order
(README, `produce`). Getters run where finalization (`src/finalization.ts`) reads a slot: in the
probe walk of `needsMaterialization`, which `run` asks first about the result and discovery asks
again about each object it reaches, and in discovery itself (`materializeContainerSlot`). Both read
an object's slots in order and resolve a slot's child before the next slot (`someChild`,
`observeDraft`), and an accessor runs once per object and key (`observeAccessor`): a later read
takes the value it returned. The probe stops at the first child that needs a copy, so discovery
reads that object's later slots afterwards, and the probe discovery asks about an object reads
ahead of discovery.

This module models both walks over a graph of slots (`Graph`): `check` and `walk` are
`checkState` with `someChild`, `question` is `needsMaterialization` at the top, `disc` and `slots`
are `materializeContainerSlot` with `observeDraft`, and `run` is the question about the result
followed by discovery. `State.reads` lists the slots in the order of their first read, which is
when a getter runs. The runtime's other answers (closure facts, written drafts, changes found after
a walk, draft handles in slots) are an arbitrary `Oracle`. `Dfs` is the depth-first walk: an object
is entered at the first slot that holds it, and its slots are read in order, each child walked
before the next slot.

- Together the walks read each slot for the first time in depth-first order: the first reads are
  exactly the depth-first walk's slots (`run_reads`), whatever the oracle answers. So each getter
  of a reachable object runs once, in depth-first order, and every one runs (`getters_once`,
  `Dfs.slots_iff`). On a finite graph the walk exists (`run_dfs`).
- The depth-first walk is the one `Serialization.DFS.Recursive` models for `serialize`: its edge
  events are these slots (`dfs_eq_serialization`).
- The proof: the probe walks in step with the depth-first walk and, when it stops, leaves the part
  read in a shape discovery resumes (`probe`, `Part`); discovery resumes it, reading nothing again
  behind the walk's frontier (`check_behind`, `disc_behind`) and the rest in step (`resume`).
- The model bounds discovery's nesting with fuel, and with too little it stops early (`Example`);
  the runtime's recursion has no such bound. The probe's fuel can be any: out of fuel, it answers
  that a copy is needed, and discovery reads the rest.

The runtime obligation (_Finalization reads_ in the Lean guide): a later read of a slot answers
the child the first read did, as `SettledChildren` assumes, so one graph describes every walk; an
accessor's result is cached by object and key; the sealed pass runs no getter, and throws
`FinalizationAccessorUnstable` at one not run before; identity restoration takes an object's
children from a walk that visited all of them, and so calls no getter. A special value, a value
kept by reference and a primitive are objects without slots: no own getter of theirs runs.
-/

namespace Reconcile.GetterOrder

/-- The object children of each object, one per slot in order: own properties in key order,
array elements, `Map` keys and values, `Set` members. A primitive, a function, a value kept by
reference and a special value is a node without slots. -/
abbrev Graph := Nat → List Nat

/-- A slot: an object and the index of the slot. -/
abbrev Slot := Nat × Nat

/-- One finalization phase's state: the current question's visited objects, the settled answers
(`phase.required`), the objects discovery resolved (`phase.values`) and those it began as records,
which the closure requires, and the slots read so far, in order of their first read, which is when
an accessor's getter runs. -/
structure State where
  visited : List Nat
  memo : Nat → Option Bool
  done : List Nat
  records : List Nat
  reads : List Slot

/-- The runtime's answers besides the walks; they may depend on the state. -/
structure Oracle where
  /-- A closure fact: the object needs a copy, asked before the settled answer. -/
  fact : State → Nat → Bool
  /-- A written draft, asked before the walk (`changedBefore`). -/
  changed : State → Nat → Bool
  /-- A change found after the walk: a draft written meanwhile, or an observed accessor. -/
  after : State → Nat → Bool
  /-- The slot holds a draft handle, which needs unwrapping: the probe answers without walking it,
  and discovery resolves the handle's object. -/
  handle : Nat → Nat → Bool

namespace State

/-- Reads a slot; the first read of a slot is recorded, as an accessor's result is cached. -/
def read (s : State) (x : Slot) : State :=
  if x ∈ s.reads then s else { s with reads := s.reads ++ [x] }

def settle (s : State) (n : Nat) (b : Bool) : State :=
  { s with memo := fun m => if m = n then some b else s.memo m }

end State

/-- A check's answer, whether a negative answer leaned on a visited object not yet settled, and
the state after it. -/
structure Result where
  needs : Bool
  pending : Bool
  state : State

/-- Reads slot `i` of `n`, then checks its child `c` with `f`; a slot holding a draft handle
needs a copy without a check. -/
def step (o : Oracle) (f : State → Nat → Result) (n i : Nat) (s : State) (c : Nat) : Result :=
  if o.handle n i then ⟨true, false, s.read (n, i)⟩ else f (s.read (n, i)) c

/-- `someChild` with `readTraversalProperty`: reads each slot, then checks its child, and stops at
the first child that needs a copy. -/
def walk (o : Oracle) (f : State → Nat → Result) (n : Nat) : Nat → State → List Nat → Result
  | _, s, [] => ⟨false, false, s⟩
  | i, s, c :: cs =>
    let r := step o f n i s c
    if r.needs then r
    else
      let r' := walk o f n (i + 1) r.state cs
      ⟨r'.needs, r.pending || r'.pending, r'.state⟩

/-- `checkState` with `fuel` nested walks; out of fuel it answers that a copy is needed. -/
def check (g : Graph) (o : Oracle) : Nat → State → Nat → Result
  | 0, s, _ => ⟨true, false, s⟩
  | fuel + 1, s, n =>
    if o.fact s n || decide (n ∈ s.records) then ⟨true, false, s⟩
    else match s.memo n with
    | some b => ⟨b, false, s⟩
    | none =>
      if o.changed s n then ⟨true, false, s.settle n true⟩
      else if n ∈ s.visited then ⟨false, true, s⟩
      else
        let r := walk o (check g o fuel) n 0 { s with visited := n :: s.visited } (g n)
        if r.needs then ⟨true, false, r.state.settle n true⟩
        else if o.after r.state n then ⟨true, false, r.state.settle n true⟩
        else if r.pending then ⟨false, true, r.state⟩
        else ⟨false, false, r.state.settle n false⟩

/-- Settles each listed object that has no answer as not needing a copy: the pending answers of a
question that answers no. -/
def settlePending (s : State) : List Nat → State
  | [] => s
  | v :: vs => settlePending (if s.memo v = none then s.settle v false else s) vs

/-- `needsMaterialization` at the top: a fresh visited set, and a negative answer settles the
pending objects. -/
def question (g : Graph) (o : Oracle) (fuel : Nat) (s : State) (n : Nat) : Bool × State :=
  let r := check g o fuel { s with visited := [] } n
  if r.needs then (true, { r.state with visited := [] })
  else (false, { settlePending r.state r.state.visited with visited := [] })

/-- `observeDraft`: reads each slot, then resolves its child, in order. -/
def slots (f : State → Nat → State) (n : Nat) : Nat → State → List Nat → State
  | _, s, [] => s
  | i, s, c :: cs => slots f n (i + 1) (f (s.read (n, i)) c) cs

/-- `materializeContainerSlot` on a structural object, with `fuel` nested objects and `qfuel` for
each question: a resolved object is not resolved again; a written draft, or one whose question
answers yes, becomes a record whose slots are read and resolved; any other is a leaf. -/
def disc (g : Graph) (o : Oracle) (qfuel : Nat) : Nat → State → Nat → State
  | 0, s, _ => s
  | fuel + 1, s, n =>
    if n ∈ s.done then s
    else
      let q := if o.changed s n then (true, s) else question g o qfuel s n
      if q.1 then
        slots (disc g o qfuel fuel) n 0
          { q.2 with done := n :: q.2.done, records := n :: q.2.records } (g n)
      else { q.2 with done := n :: q.2.done }

/-- The state before finalization. -/
def initial : State := ⟨[], fun _ => none, [], [], []⟩

/-- `Finalization.run` up to the sealed pass: the question about the result, then discovery. -/
def run (g : Graph) (o : Oracle) (qfuel fuel root : Nat) : State :=
  disc g o qfuel fuel (question g o qfuel initial root).2 root

/-! ## Depth-first order -/

/-- A step of the depth-first walk: enter an object, or continue its slots from an index. -/
inductive Frame where
  | visit (n : Nat)
  | resume (n i : Nat) (cs : List Nat)

/-- The depth-first walk from a frame, given the objects entered so far: the slots it reads, in
order, and the objects entered after it. An object is entered at its first slot in this order,
and its slots are read in order, each child walked before the next slot. An object without slots
is never entered. -/
inductive Dfs (g : Graph) : Frame → List Nat → List Slot → List Nat → Prop
  | seen {n S} : n ∈ S → Dfs g (.visit n) S [] S
  | leaf {n S} : g n = [] → Dfs g (.visit n) S [] S
  | fresh {n S T S'} : n ∉ S → g n ≠ [] → Dfs g (.resume n 0 (g n)) (n :: S) T S' →
      Dfs g (.visit n) S T S'
  | nil {n i S} : Dfs g (.resume n i []) S [] S
  | cons {n i c cs S S₁ S₂ T₁ T₂} : Dfs g (.visit c) S T₁ S₁ →
      Dfs g (.resume n (i + 1) cs) S₁ T₂ S₂ →
      Dfs g (.resume n i (c :: cs)) S ((n, i) :: (T₁ ++ T₂)) S₂

/-! ## Facts about the depth-first walk -/

section DfsFacts

variable {g : Graph}

/-- The walk only adds objects to the seen list, each once, none seen before. -/
theorem Dfs.extends {F : Frame} {S S' : List Nat} {T : List Slot} (D : Dfs g F S T S') :
    ∃ L, S' = L ++ S ∧ L.Nodup ∧ ∀ m ∈ L, m ∉ S := by
  induction D with
  | seen => exact ⟨[], by simp, by simp, by simp⟩
  | leaf => exact ⟨[], by simp, by simp, by simp⟩
  | nil => exact ⟨[], by simp, by simp, by simp⟩
  | @fresh n S T S' hn _ _ ih =>
    obtain ⟨L, hL, hnd, hnot⟩ := ih
    refine ⟨L ++ [n], by simp [hL], ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hnd, by simp, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      intro hab
      subst hab
      exact hnot a ha (by simp)
    · intro m hm
      rcases List.mem_append.mp hm with hm | hm
      · intro hS; exact hnot m hm (List.mem_cons_of_mem _ hS)
      · rw [List.mem_singleton] at hm; subst hm; exact hn
  | @cons n i c cs S S₁ S₂ T₁ T₂ _ _ ih₁ ih₂ =>
    obtain ⟨L₁, h₁, hnd₁, hnot₁⟩ := ih₁
    obtain ⟨L₂, h₂, hnd₂, hnot₂⟩ := ih₂
    refine ⟨L₂ ++ L₁, by simp [h₁, h₂], ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hnd₂, hnd₁, ?_⟩
      intro a ha b hb hab
      subst hab
      exact hnot₂ a ha (by rw [h₁]; exact List.mem_append_left _ hb)
    · intro m hm
      rcases List.mem_append.mp hm with hm | hm
      · intro hS; exact hnot₂ m hm (by rw [h₁]; exact List.mem_append_right _ hS)
      · exact hnot₁ m hm

theorem Dfs.sub {F : Frame} {S S' : List Nat} {T : List Slot} (D : Dfs g F S T S') {m : Nat} (h : m ∈ S) :
    m ∈ S' := by
  obtain ⟨L, hL, _, _⟩ := D.extends
  rw [hL]; exact List.mem_append_right _ h

theorem Dfs.length {F : Frame} {S S' : List Nat} {T : List Slot} (D : Dfs g F S T S') :
    S.length ≤ S'.length := by
  obtain ⟨L, hL, _, _⟩ := D.extends
  rw [hL]; simp

/-- The walk is determined by its frame and the objects seen. -/
theorem Dfs.det {F : Frame} {S S₁ S₂ : List Nat} {T₁ T₂ : List Slot} (D₁ : Dfs g F S T₁ S₁)
    (D₂ : Dfs g F S T₂ S₂) : T₁ = T₂ ∧ S₁ = S₂ := by
  induction D₁ generalizing T₂ S₂ with
  | seen h =>
    cases D₂ with
    | seen => exact ⟨rfl, rfl⟩
    | leaf => exact ⟨rfl, rfl⟩
    | fresh h' => exact absurd h h'
  | leaf h =>
    cases D₂ with
    | seen => exact ⟨rfl, rfl⟩
    | leaf => exact ⟨rfl, rfl⟩
    | fresh _ h' => exact absurd h h'
  | fresh h hg _ ih =>
    cases D₂ with
    | seen h' => exact absurd h' h
    | leaf h' => exact absurd h' hg
    | fresh _ _ D' => exact ih D'
  | nil =>
    cases D₂ with
    | nil => exact ⟨rfl, rfl⟩
  | cons _ _ ih₁ ih₂ =>
    cases D₂ with
    | cons D₁' D₂' =>
      obtain ⟨rfl, rfl⟩ := ih₁ D₁'
      obtain ⟨rfl, rfl⟩ := ih₂ D₂'
      exact ⟨rfl, rfl⟩

/-- After a visit, the object is entered, unless it has no slots. -/
theorem Dfs.visit_mem {c : Nat} {S S' : List Nat} {T : List Slot} (D : Dfs g (.visit c) S T S') :
    c ∈ S' ∨ g c = [] := by
  cases D with
  | seen h => exact Or.inl h
  | leaf h => exact Or.inr h
  | fresh _ _ D' => exact Or.inl (D'.sub (List.mem_cons_self ..))

/-- Which slots a frame reads: those of objects it enters, and from a resumed object its slots from
the index on. -/
def Owns (S : List Nat) : Frame → Slot → Prop
  | .visit _, x => x.1 ∉ S
  | .resume n i _, x => (x.1 = n ∧ i ≤ x.2) ∨ x.1 ∉ S

/-- The slots a frame reads belong to objects entered by the end, or to the object it resumes. -/
def Ends (S' : List Nat) : Frame → Slot → Prop
  | .visit _, x => x.1 ∈ S'
  | .resume n _ _, x => x.1 ∈ S' ∨ x.1 = n

theorem Dfs.owns {F : Frame} {S S' : List Nat} {T : List Slot} (D : Dfs g F S T S') :
    ∀ x ∈ T, Owns S F x ∧ Ends S' F x := by
  induction D with
  | seen => simp
  | leaf => simp
  | nil => simp
  | @fresh n S T S' hn _ D ih =>
    intro x hx
    obtain ⟨ho, hm⟩ := ih x hx
    simp only [Owns, Ends] at ho hm ⊢
    refine ⟨?_, ?_⟩
    · rcases ho with ⟨h, _⟩ | h
      · rw [h]; exact hn
      · exact fun hS => h (List.mem_cons_of_mem _ hS)
    · rcases hm with hm | hm
      · exact hm
      · rw [hm]; exact D.sub (List.mem_cons_self ..)
  | @cons n i c cs S S₁ S₂ T₁ T₂ D₁ D₂ ih₁ ih₂ =>
    intro x hx
    simp only [List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · exact ⟨Or.inl ⟨rfl, Nat.le_refl _⟩, Or.inr rfl⟩
    · obtain ⟨ho, hm⟩ := ih₁ x hx
      simp only [Owns, Ends] at ho hm ⊢
      exact ⟨Or.inr ho, Or.inl (D₂.sub hm)⟩
    · obtain ⟨ho, hm⟩ := ih₂ x hx
      refine ⟨?_, hm⟩
      simp only [Owns] at ho ⊢
      rcases ho with ⟨h, hi⟩ | h
      · exact Or.inl ⟨h, by omega⟩
      · exact Or.inr fun hS => h (D₁.sub hS)

/-- The walk reads each slot once. -/
theorem Dfs.nodup {F : Frame} {S S' : List Nat} {T : List Slot} (D : Dfs g F S T S')
    (hF : ∀ n i cs, F = .resume n i cs → n ∈ S) : T.Nodup := by
  induction D with
  | seen => simp
  | leaf => simp
  | nil => simp
  | fresh _ _ _ ih => exact ih fun n i cs h => by cases h; exact List.mem_cons_self ..
  | @cons n i c cs S S₁ S₂ T₁ T₂ D₁ D₂ ih₁ ih₂ =>
    have hn : n ∈ S := hF n i (c :: cs) rfl
    have h₁ := ih₁ (by intro _ _ _ h; cases h)
    have h₂ := ih₂ (by intro _ _ _ h; cases h; exact D₁.sub hn)
    rw [List.nodup_cons, List.nodup_append]
    refine ⟨?_, h₁, h₂, ?_⟩
    · simp only [List.mem_append, not_or]
      constructor
      · intro hx
        have := (D₁.owns _ hx).1
        simp only [Owns] at this
        exact this hn
      · intro hx
        have := (D₂.owns _ hx).1
        simp only [Owns] at this
        rcases this with ⟨_, h⟩ | h
        · omega
        · exact h (D₁.sub hn)
    · intro a ha b hb hab
      subst hab
      have ho₁ := (D₁.owns _ ha)
      have ho₂ := (D₂.owns _ hb).1
      simp only [Owns, Ends] at ho₁ ho₂
      rcases ho₂ with ⟨h, _⟩ | h
      · exact ho₁.1 (h ▸ hn)
      · exact h ho₁.2

/-- Every object a frame enters is finished by its end: all its slots read and all its children
entered, unless they have no slots. A resumed object's remaining slots are read and their children
entered too. -/
theorem Dfs.finished {F : Frame} {S S' : List Nat} {T : List Slot} (D : Dfs g F S T S') :
    (∀ m ∈ S', m ∉ S → (∀ k < (g m).length, (m, k) ∈ T) ∧ ∀ c ∈ g m, c ∈ S' ∨ g c = []) ∧
      match F with
      | .resume n i cs => (∀ j < cs.length, (n, i + j) ∈ T) ∧ ∀ c ∈ cs, c ∈ S' ∨ g c = []
      | .visit _ => True := by
  induction D with
  | seen => exact ⟨fun _ h h' => absurd h h', trivial⟩
  | leaf => exact ⟨fun _ h h' => absurd h h', trivial⟩
  | nil => exact ⟨fun _ h h' => absurd h h', by simp⟩
  | @fresh n S T S' hn _ D ih =>
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    refine ⟨?_, trivial⟩
    intro m hm hmS
    by_cases hmn : m = n
    · subst hmn
      exact ⟨fun k hk => by simpa using ih₂ k hk, ih₃⟩
    · exact ih₁ m hm (by simp [hmn, hmS])
  | @cons n i c cs S S₁ S₂ T₁ T₂ D₁ D₂ ih₁ ih₂ =>
    obtain ⟨a₁, -⟩ := ih₁
    obtain ⟨a₂, b₂, c₂⟩ := ih₂
    refine ⟨?_, ?_, ?_⟩
    · intro m hm hmS
      by_cases h₁ : m ∈ S₁
      · obtain ⟨hk, hc⟩ := a₁ m h₁ hmS
        exact ⟨fun k hk' => by simp [hk k hk'],
          fun c' hc' => (hc c' hc').imp_left D₂.sub⟩
      · obtain ⟨hk, hc⟩ := a₂ m hm h₁
        exact ⟨fun k hk' => by simp [hk k hk'], hc⟩
    · intro j hj
      cases j with
      | zero => simp
      | succ j =>
        have := b₂ j (by simp at hj; omega)
        simp only [List.mem_cons, List.mem_append]
        right; right
        rw [show i + (j + 1) = i + 1 + j by omega]
        exact this
    · intro c' hc'
      simp only [List.mem_cons] at hc'
      rcases hc' with rfl | hc'
      · exact D₁.visit_mem.imp_left D₂.sub
      · exact c₂ c' hc'

end DfsFacts

/-! ## What the walks keep -/

section Mono

variable {g : Graph} {o : Oracle}

/-- What a probe walk keeps: reads only grow at the end, a settled answer stays, the visited
objects only grow, and the resolved objects and records do not change. -/
structure Mono (s s' : State) : Prop where
  reads : s.reads <+: s'.reads
  memo : ∀ n b, s.memo n = some b → s'.memo n = some b
  visited : ∀ n ∈ s.visited, n ∈ s'.visited
  done : s'.done = s.done
  records : s'.records = s.records

theorem Mono.refl (s : State) : Mono s s :=
  ⟨List.prefix_refl _, fun _ _ h => h, fun _ h => h, rfl, rfl⟩

theorem Mono.trans {s₁ s₂ s₃ : State} (h₁ : Mono s₁ s₂) (h₂ : Mono s₂ s₃) : Mono s₁ s₃ :=
  ⟨h₁.reads.trans h₂.reads, fun n b h => h₂.memo n b (h₁.memo n b h),
    fun n h => h₂.visited n (h₁.visited n h), h₂.done.trans h₁.done,
    h₂.records.trans h₁.records⟩

theorem read_mono (s : State) (x : Slot) : Mono s (s.read x) := by
  unfold State.read
  split
  · exact Mono.refl s
  · exact ⟨List.prefix_append _ _, fun _ _ h => h, fun _ h => h, rfl, rfl⟩

@[simp] theorem read_memo (s : State) (x : Slot) : (s.read x).memo = s.memo := by
  unfold State.read; split <;> rfl

@[simp] theorem read_visited (s : State) (x : Slot) : (s.read x).visited = s.visited := by
  unfold State.read; split <;> rfl

@[simp] theorem read_done (s : State) (x : Slot) : (s.read x).done = s.done := by
  unfold State.read; split <;> rfl

@[simp] theorem read_records (s : State) (x : Slot) : (s.read x).records = s.records := by
  unfold State.read; split <;> rfl

theorem read_reads (s : State) (x : Slot) :
    (s.read x).reads = if x ∈ s.reads then s.reads else s.reads ++ [x] := by
  unfold State.read; split <;> rfl

theorem read_of_mem {s : State} {x : Slot} (h : x ∈ s.reads) : s.read x = s := by
  simp [State.read, h]

theorem mem_read (s : State) (x : Slot) : x ∈ (s.read x).reads := by
  rw [read_reads]; split
  · assumption
  · simp

theorem settle_mono (s : State) (n : Nat) (b : Bool) (h : s.memo n = none) :
    Mono s (s.settle n b) := by
  refine ⟨List.prefix_refl _, fun m b' hm => ?_, fun _ h => h, rfl, rfl⟩
  simp only [State.settle]
  split
  · subst m; rw [h] at hm; cases hm
  · exact hm

theorem walk_mono {f : State → Nat → Result} (hf : ∀ s c, Mono s (f s c).state) (n : Nat) :
    ∀ (cs : List Nat) i s, Mono s (walk o f n i s cs).state := by
  intro cs
  induction cs with
  | nil => intro i s; exact Mono.refl s
  | cons c cs ih =>
    intro i s
    have h₁ : Mono s (step o f n i s c).state := by
      unfold step
      split
      · exact read_mono s (n, i)
      · exact (read_mono s (n, i)).trans (hf _ _)
    simp only [walk]
    split
    · exact h₁
    · exact h₁.trans (ih _ _)

theorem check_mono : ∀ fuel s n, Mono s (check g o fuel s n).state := by
  intro fuel
  induction fuel with
  | zero => intro s n; exact Mono.refl s
  | succ fuel ih =>
    intro s n
    simp only [check]
    split
    · exact Mono.refl s
    · split
      · exact Mono.refl s
      · rename_i hm
        split
        · exact settle_mono s n true hm
        · split
          · exact Mono.refl s
          · have hv : Mono s { s with visited := n :: s.visited } :=
              ⟨List.prefix_refl _, fun _ _ h => h, fun _ h => List.mem_cons_of_mem _ h, rfl, rfl⟩
            have hw := hv.trans (walk_mono (o := o) ih n (g n) 0 { s with visited := n :: s.visited })
            -- The walk may settle `n` only through a nested check that found it changed; the
            -- final settle keeps every answer settled before `n` was checked.
            have keep : ∀ (r : State) (b : Bool), Mono s r → Mono s (r.settle n b) := by
              intro r b hr
              refine ⟨hr.reads, fun m b' h => ?_, hr.visited, hr.done, hr.records⟩
              simp only [State.settle]
              split
              · subst m; rw [hm] at h; cases h
              · exact hr.memo m b' h
            split
            · exact keep _ _ hw
            · split
              · exact keep _ _ hw
              · split
                · exact hw
                · exact keep _ _ hw

end Mono

section Mono2

variable {g : Graph} {o : Oracle}

/-- `settlePending` changes only answers that were missing, and settles every listed object. -/
theorem settlePending_spec : ∀ (l : List Nat) (s : State),
    (settlePending s l).reads = s.reads ∧ (settlePending s l).done = s.done ∧
      (settlePending s l).records = s.records ∧ (settlePending s l).visited = s.visited ∧
      (∀ n b, s.memo n = some b → (settlePending s l).memo n = some b) ∧
      (∀ n, (settlePending s l).memo n = some false → s.memo n = some false ∨ n ∈ l) ∧
      ∀ v ∈ l, ((settlePending s l).memo v).isSome = true := by
  intro l
  induction l with
  | nil => intro s; simp [settlePending]
  | cons v vs ih =>
    intro s
    simp only [settlePending]
    generalize hs₁ : (if s.memo v = none then s.settle v false else s) = s₁
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := ih s₁
    have e₁ : s₁.reads = s.reads ∧ s₁.done = s.done ∧ s₁.records = s.records ∧
        s₁.visited = s.visited := by
      rw [← hs₁]; split <;> simp [State.settle]
    have m₁ : ∀ n b, s.memo n = some b → s₁.memo n = some b := by
      intro n b h
      rw [← hs₁]; split
      · rename_i hv
        simp only [State.settle]
        split
        · subst n; rw [hv] at h; cases h
        · exact h
      · exact h
    have v₁ : (s₁.memo v).isSome = true := by
      rw [← hs₁]; split
      · simp [State.settle]
      · rename_i hv; cases h : s.memo v
        · exact absurd h hv
        · simp
    refine ⟨h₁.trans e₁.1, h₂.trans e₁.2.1, h₃.trans e₁.2.2.1, h₄.trans e₁.2.2.2,
      fun n b h => h₅ n b (m₁ n b h), fun n h => ?_, fun w hw => ?_⟩
    · rcases h₆ n h with h | h
      · rw [← hs₁] at h
        split at h
        · simp only [State.settle] at h
          split at h
          · subst n; exact Or.inr (List.mem_cons_self ..)
          · exact Or.inl h
        · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · cases hm : s₁.memo w with
        | none => rw [hm] at v₁; cases v₁
        | some b => rw [h₅ w b hm]; rfl
      · exact h₇ w hw

/-- What a question keeps: reads only grow at the end, a settled answer stays, and the resolved
objects and records do not change. Its visited set is gone at the end. -/
structure QMono (s s' : State) : Prop where
  reads : s.reads <+: s'.reads
  memo : ∀ n b, s.memo n = some b → s'.memo n = some b
  done : s'.done = s.done
  records : s'.records = s.records

theorem question_mono (fuel : Nat) (s : State) (n : Nat) :
    QMono s (question g o fuel s n).2 ∧ (question g o fuel s n).2.visited = [] := by
  have hm := check_mono (g := g) (o := o) fuel { s with visited := [] } n
  unfold question
  generalize check g o fuel { s with visited := [] } n = r at hm ⊢
  simp only
  split
  · exact ⟨⟨hm.reads, hm.memo, hm.done, hm.records⟩, rfl⟩
  · obtain ⟨h₁, h₂, h₃, -, h₅, -⟩ := settlePending_spec r.state.visited r.state
    exact ⟨⟨by rw [h₁]; exact hm.reads, fun m b h => h₅ m b (hm.memo m b h), h₂.trans hm.done,
      h₃.trans hm.records⟩, rfl⟩

/-- A check that answers no leaves its object settled, or visited and pending. -/
theorem check_false : ∀ fuel s n, (check g o fuel s n).needs = false →
    ((check g o fuel s n).state.memo n).isSome = true ∨ n ∈ (check g o fuel s n).state.visited := by
  intro fuel s n h
  cases fuel with
  | zero => simp [check] at h
  | succ fuel =>
    revert h
    simp only [check]
    split
    · simp
    · split
      · rename_i b hb; intro _; left; simp [hb]
      · split
        · simp
        · split
          · rename_i hv; intro _; right; exact hv
          · have hw := walk_mono (o := o) (check_mono (g := g) (o := o) fuel) n (g n) 0
              { s with visited := n :: s.visited }
            split
            · simp
            · split
              · simp
              · split
                · intro _; right; exact hw.visited n (List.mem_cons_self ..)
                · intro _; left; simp [State.settle]

theorem question_eq (fuel : Nat) (s : State) (n : Nat) : question g o fuel s n =
    let r := check g o fuel { s with visited := [] } n
    if r.needs then (true, { r.state with visited := [] })
    else (false, { settlePending r.state r.state.visited with visited := [] }) := rfl

/-- A question that answers no leaves its object settled. -/
theorem question_false (fuel : Nat) (s : State) (n : Nat)
    (h : (question g o fuel s n).1 = false) : ((question g o fuel s n).2.memo n).isSome = true := by
  have hc := check_false (g := g) (o := o) fuel { s with visited := [] } n
  rw [question_eq] at h ⊢
  generalize check g o fuel { s with visited := [] } n = r at h hc ⊢
  simp only at h ⊢
  split at h
  · cases h
  · rename_i hneg
    rw [if_neg hneg]
    obtain ⟨-, -, -, -, h₅, -, h₇⟩ := settlePending_spec r.state.visited r.state
    rcases hc (by simpa using hneg) with hm | hv
    · cases hb : r.state.memo n with
      | none => rw [hb] at hm; cases hm
      | some b => simp [h₅ n b hb]
    · exact h₇ n hv

end Mono2

section Behind

variable {g : Graph} {o : Oracle} {qfuel : Nat}

/-- What discovery keeps: reads only grow at the end, a settled answer stays, the resolved objects
and records only grow, and no question is left open. -/
structure Grows (s s' : State) : Prop where
  reads : s.reads <+: s'.reads
  memo : ∀ n b, s.memo n = some b → s'.memo n = some b
  done : ∀ n ∈ s.done, n ∈ s'.done
  records : ∀ n ∈ s.records, n ∈ s'.records
  visited : s.visited = [] → s'.visited = []

theorem Grows.refl (s : State) : Grows s s :=
  ⟨List.prefix_refl _, fun _ _ h => h, fun _ h => h, fun _ h => h, id⟩

theorem Grows.trans {s₁ s₂ s₃ : State} (h₁ : Grows s₁ s₂) (h₂ : Grows s₂ s₃) : Grows s₁ s₃ :=
  ⟨h₁.reads.trans h₂.reads, fun n b h => h₂.memo n b (h₁.memo n b h),
    fun n h => h₂.done n (h₁.done n h), fun n h => h₂.records n (h₁.records n h),
    fun h => h₂.visited (h₁.visited h)⟩

theorem read_grows (s : State) (x : Slot) : Grows s (s.read x) := by
  have h := read_mono s x
  refine ⟨h.reads, h.memo, fun n hn => h.done ▸ hn, fun n hn => h.records ▸ hn, fun hv => ?_⟩
  unfold State.read; split <;> simp [hv]

theorem slots_grows {f : State → Nat → State} (hf : ∀ s c, Grows s (f s c)) (n : Nat) :
    ∀ (cs : List Nat) i s, Grows s (slots f n i s cs) := by
  intro cs
  induction cs with
  | nil => intro i s; exact Grows.refl s
  | cons c cs ih =>
    intro i s
    exact ((read_grows s (n, i)).trans (hf _ _)).trans (ih _ _)

/-- The discovery step before reading slots: a written draft is active without a question. -/
theorem ask_grows (s : State) (n : Nat) :
    Grows s (if o.changed s n then (true, s) else question g o qfuel s n).2 := by
  split
  · exact Grows.refl s
  · obtain ⟨h, hv⟩ := question_mono (g := g) (o := o) qfuel s n
    exact ⟨h.reads, h.memo, fun m hm => h.done ▸ hm, fun m hm => h.records ▸ hm,
      fun _ => hv⟩

theorem disc_grows : ∀ fuel s n, Grows s (disc g o qfuel fuel s n) := by
  intro fuel
  induction fuel with
  | zero => intro s n; exact Grows.refl s
  | succ fuel ih =>
    intro s n
    simp only [disc]
    split
    · exact Grows.refl s
    · have hq := ask_grows (g := g) (o := o) (qfuel := qfuel) s n
      generalize (if o.changed s n then (true, s) else question g o qfuel s n) = q at hq ⊢
      split
      · refine Grows.trans ?_ (slots_grows ih n (g n) 0 _)
        exact ⟨hq.reads, hq.memo, fun m hm => List.mem_cons_of_mem _ (hq.done m hm),
          fun m hm => List.mem_cons_of_mem _ (hq.records m hm), hq.visited⟩
      · exact ⟨hq.reads, hq.memo, fun m hm => List.mem_cons_of_mem _ (hq.done m hm),
          hq.records, hq.visited⟩

/-- Every resolved object is a record or settled: a leaf's question answered no. -/
def DoneOK (s : State) : Prop := ∀ d ∈ s.done, d ∈ s.records ∨ (s.memo d).isSome = true

theorem slots_doneOK {f : State → Nat → State} (hf : ∀ s c, DoneOK s → DoneOK (f s c)) (n : Nat) :
    ∀ (cs : List Nat) i s, DoneOK s → DoneOK (slots f n i s cs) := by
  intro cs
  induction cs with
  | nil => intro i s h; exact h
  | cons c cs ih =>
    intro i s h
    apply ih
    apply hf
    unfold State.read; split
    · exact h
    · exact h

/-- Asking keeps `DoneOK`: a question changes no resolved object or record and keeps answers. -/
theorem ask_doneOK (s : State) (n : Nat) (h : DoneOK s) :
    DoneOK (if o.changed s n then (true, s) else question g o qfuel s n).2 := by
  split
  · exact h
  · obtain ⟨hm, -⟩ := question_mono (g := g) (o := o) qfuel s n
    intro d hd
    rw [hm.done] at hd
    rcases h d hd with h' | h'
    · exact Or.inl (hm.records ▸ h')
    · right
      cases hb : s.memo d with
      | none => rw [hb] at h'; cases h'
      | some b => rw [hm.memo d b hb]; rfl

theorem disc_doneOK : ∀ fuel s n, DoneOK s → DoneOK (disc g o qfuel fuel s n) := by
  intro fuel
  induction fuel with
  | zero => intro s n h; exact h
  | succ fuel ih =>
    intro s n h
    simp only [disc]
    split
    · exact h
    · have hq' := ask_doneOK (g := g) (o := o) (qfuel := qfuel) s n h
      have hf : (if o.changed s n then (true, s) else question g o qfuel s n).1 = false →
          (((if o.changed s n then (true, s) else question g o qfuel s n).2).memo n).isSome
            = true := by
        split
        · intro h'; cases h'
        · exact question_false qfuel s n
      generalize (if o.changed s n then (true, s) else question g o qfuel s n) = q at hq' hf ⊢
      split
      next =>
        apply slots_doneOK ih
        intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact Or.inl (List.mem_cons_self ..)
        · exact (hq' d hd).imp_left (List.mem_cons_of_mem _)
      next hneg =>
        intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact Or.inr (hf (by simpa using hneg))
        · exact hq' d hd

end Behind

/-! ## Walks behind the frontier read nothing new

A finished object has all its slots read, and its children are finished, or block the walk. A walk
from a finished object therefore reads no slot for the first time. -/

section Behind2

variable {g : Graph} {o : Oracle} {qfuel : Nat}

/-- Every slot of the object was read. -/
def Full (g : Graph) (s : State) (n : Nat) : Prop := ∀ k < (g n).length, (n, k) ∈ s.reads

/-- A probe walk does not walk the object: it is a record, settled, or being walked. -/
def Blocks (s : State) (n : Nat) : Prop :=
  n ∈ s.records ∨ (s.memo n).isSome = true ∨ n ∈ s.visited

/-- Objects in `Z` are full, and each child is in `Z`, blocked by `B`, or has no slots. -/
def Closed (g : Graph) (s : State) (Z B : Nat → Prop) : Prop :=
  ∀ z, Z z → Full g s z ∧ ∀ c ∈ g z, Z c ∨ B c ∨ g c = []

theorem memo_isSome {s s' : State} (h : ∀ n b, s.memo n = some b → s'.memo n = some b) {n : Nat}
    (hn : (s.memo n).isSome = true) : (s'.memo n).isSome = true := by
  cases hb : s.memo n with
  | none => rw [hb] at hn; cases hn
  | some b => rw [h n b hb]; rfl

theorem Blocks.mono {s s' : State} (h : Mono s s') {n : Nat} (hb : Blocks s n) : Blocks s' n := by
  rcases hb with hb | hb | hb
  · exact Or.inl (h.records ▸ hb)
  · exact Or.inr (Or.inl (memo_isSome h.memo hb))
  · exact Or.inr (Or.inr (h.visited n hb))

theorem Closed.mono {Z : Nat → Prop} {s s' : State} (h : Mono s s') (hc : Closed g s Z (Blocks s)) :
    Closed g s' Z (Blocks s') := by
  intro z hz
  obtain ⟨hf, hch⟩ := hc z hz
  exact ⟨fun k hk => h.reads.subset (hf k hk),
    fun c hc' => (hch c hc').imp_right (Or.imp_left (Blocks.mono h))⟩

theorem walk_behind (Z : Nat → Prop) {f : State → Nat → Result}
    (hf : ∀ s c, Closed g s Z (Blocks s) → (Z c ∨ Blocks s c ∨ g c = []) →
      (f s c).state.reads = s.reads)
    (hfm : ∀ s c, Mono s (f s c).state) (n : Nat) :
    ∀ (cs : List Nat) i s, Closed g s Z (Blocks s) → (∀ j < cs.length, (n, i + j) ∈ s.reads) →
      (∀ c ∈ cs, Z c ∨ Blocks s c ∨ g c = []) → (walk o f n i s cs).state.reads = s.reads := by
  intro cs
  induction cs with
  | nil => intro i s _ _ _; rfl
  | cons c cs ih =>
    intro i s hc hr hch
    have hread : s.read (n, i) = s := read_of_mem (by simpa using hr 0 (by simp))
    have h₁ : (step o f n i s c).state.reads = s.reads := by
      unfold step; rw [hread]; split
      · rfl
      · exact hf s c hc (hch c (List.mem_cons_self ..))
    have m₁ : Mono s (step o f n i s c).state := by
      unfold step; rw [hread]; split
      · exact Mono.refl s
      · exact hfm s c
    simp only [walk]
    split
    · exact h₁
    · rw [ih (i + 1) _ (hc.mono m₁) (fun j hj => by
          rw [h₁, show i + 1 + j = i + (j + 1) by omega]; exact hr (j + 1) (by simp; omega))
        (fun c' hc' => (hch c' (List.mem_cons_of_mem _ hc')).imp_right
          (Or.imp_left (Blocks.mono m₁))), h₁]

theorem check_behind (Z : Nat → Prop) : ∀ fuel s n, Closed g s Z (Blocks s) →
    (Z n ∨ Blocks s n ∨ g n = []) → (check g o fuel s n).state.reads = s.reads := by
  intro fuel
  induction fuel with
  | zero => intro s n _ _; rfl
  | succ fuel ih =>
    intro s n hc hn
    simp only [check]
    split
    · rfl
    · rename_i hfact
      split
      · rfl
      · rename_i hm
        split
        · rfl
        · split
          · rfl
          · rename_i hv
            have hv' : Mono s { s with visited := n :: s.visited } :=
              ⟨List.prefix_refl _, fun _ _ h => h, fun _ h => List.mem_cons_of_mem _ h, rfl, rfl⟩
            have hw : (walk o (check g o fuel) n 0 { s with visited := n :: s.visited }
                (g n)).state.reads = s.reads := by
              have hn' : Z n ∨ g n = [] := by
                rcases hn with hn | hn | hn
                · exact Or.inl hn
                · exfalso
                  rcases hn with hn | hn | hn
                  · exact hfact (by simp [hn])
                  · rw [hm] at hn; cases hn
                  · exact hv hn
                · exact Or.inr hn
              rcases hn' with hz | hz
              · exact walk_behind Z (fun s c hs hc' => ih s c hs hc') (check_mono fuel) n (g n) 0 _
                  (hc.mono hv') (fun j hj => by simpa using (hc n hz).1 j hj)
                  (fun c' hc' => ((hc n hz).2 c' hc').imp_right (Or.imp_left (Blocks.mono hv')))
              · rw [hz]; rfl
            split
            · simp [State.settle, hw]
            · split
              · simp [State.settle, hw]
              · split
                · exact hw
                · simp [State.settle, hw]

theorem question_behind (Z : Nat → Prop) (fuel : Nat) (s : State) (n : Nat)
    (hc : Closed g s Z (fun c => c ∈ s.records ∨ (s.memo c).isSome = true))
    (hn : Z n ∨ n ∈ s.records ∨ (s.memo n).isSome = true ∨ g n = []) :
    (question g o fuel s n).2.reads = s.reads := by
  have hcheck := check_behind (g := g) (o := o) Z fuel { s with visited := [] } n
    (fun z hz => ⟨(hc z hz).1, fun c h => ((hc z hz).2 c h).imp_right
      (Or.imp_left fun h => h.elim Or.inl fun h => Or.inr (Or.inl h))⟩)
    (by rcases hn with hn | hn | hn | hn
        · exact Or.inl hn
        · exact Or.inr (Or.inl (Or.inl hn))
        · exact Or.inr (Or.inl (Or.inr (Or.inl hn)))
        · exact Or.inr (Or.inr hn))
  rw [question_eq]
  generalize check g o fuel { s with visited := [] } n = r at hcheck ⊢
  simp only
  split
  · exact hcheck
  · rw [← hcheck]; exact (settlePending_spec r.state.visited r.state).1

theorem slots_behind (Z : Nat → Prop) {f : State → Nat → State}
    (hf : ∀ s c, Closed g s Z (· ∈ s.done) → DoneOK s → (Z c ∨ c ∈ s.done ∨ g c = []) →
      (f s c).reads = s.reads ∧ ∀ d ∈ (f s c).done, d ∈ s.done ∨ Z d ∨ g d = [])
    (hfg : ∀ s c, Grows s (f s c)) (hfd : ∀ s c, DoneOK s → DoneOK (f s c)) (n : Nat) :
    ∀ (cs : List Nat) i s, Closed g s Z (· ∈ s.done) → DoneOK s →
      (∀ j < cs.length, (n, i + j) ∈ s.reads) → (∀ c ∈ cs, Z c ∨ c ∈ s.done ∨ g c = []) →
      (slots f n i s cs).reads = s.reads ∧
        ∀ d ∈ (slots f n i s cs).done, d ∈ s.done ∨ Z d ∨ g d = [] := by
  intro cs
  induction cs with
  | nil => intro i s _ _ _ _; exact ⟨rfl, fun d h => Or.inl h⟩
  | cons c cs ih =>
    intro i s hc hd hr hch
    have hread : s.read (n, i) = s := read_of_mem (by simpa using hr 0 (by simp))
    simp only [slots]
    rw [hread]
    have h₁ := hf s c hc hd (hch c (List.mem_cons_self ..))
    have g₁ := hfg s c
    have k₁ : Closed g (f s c) Z (· ∈ (f s c).done) := by
      intro z hz
      obtain ⟨hz₁, hz₂⟩ := hc z hz
      exact ⟨fun k hk => g₁.reads.subset (hz₁ k hk),
        fun c' h => (hz₂ c' h).imp_right (Or.imp_left (g₁.done _))⟩
    have k₂ : ∀ j < cs.length, (n, i + 1 + j) ∈ (f s c).reads := by
      intro j hj
      rw [h₁.1, show i + 1 + j = i + (j + 1) by omega]; exact hr (j + 1) (by simp; omega)
    have k₃ : ∀ c' ∈ cs, Z c' ∨ c' ∈ (f s c).done ∨ g c' = [] := by
      intro c' hc'
      exact (hch c' (List.mem_cons_of_mem _ hc')).imp_right (Or.imp_left (g₁.done _))
    obtain ⟨e₁, e₂⟩ := ih (i + 1) (f s c) k₁ (hfd s c hd) k₂ k₃
    refine ⟨e₁.trans h₁.1, fun d hd' => ?_⟩
    rcases e₂ d hd' with h | h
    · exact h₁.2 d h
    · exact Or.inr h

theorem disc_behind (Z : Nat → Prop) : ∀ fuel s n, Closed g s Z (· ∈ s.done) → DoneOK s →
    (Z n ∨ n ∈ s.done ∨ g n = []) → (disc g o qfuel fuel s n).reads = s.reads ∧
      ∀ d ∈ (disc g o qfuel fuel s n).done, d ∈ s.done ∨ Z d ∨ g d = [] := by
  intro fuel
  induction fuel with
  | zero => intro s n _ _ _; exact ⟨rfl, fun d h => Or.inl h⟩
  | succ fuel ih =>
    intro s n hc hd hn
    simp only [disc]
    split
    · exact ⟨rfl, fun d h => Or.inl h⟩
    · rename_i hnd
      have hn' : Z n ∨ g n = [] := by
        rcases hn with hn | hn | hn
        · exact Or.inl hn
        · exact absurd hn hnd
        · exact Or.inr hn
      have hask : (if o.changed s n then (true, s) else question g o qfuel s n).2.reads = s.reads ∧
          (if o.changed s n then (true, s) else question g o qfuel s n).2.done = s.done := by
        split
        · exact ⟨rfl, rfl⟩
        · refine ⟨question_behind Z qfuel s n ?_ ?_, (question_mono qfuel s n).1.done⟩
          · intro z hz
            exact ⟨(hc z hz).1, fun c h => ((hc z hz).2 c h).imp_right
              (Or.imp_left fun h => hd c h)⟩
          · rcases hn' with hz | hz
            · exact Or.inl hz
            · exact Or.inr (Or.inr (Or.inr hz))
      have hdq := ask_doneOK (g := g) (o := o) (qfuel := qfuel) s n hd
      generalize (if o.changed s n then (true, s) else question g o qfuel s n) = q at hask hdq ⊢
      have hnew : ∀ d ∈ n :: q.2.done, d ∈ s.done ∨ Z d ∨ g d = [] := by
        intro d hd'
        simp only [List.mem_cons] at hd'
        rcases hd' with rfl | hd'
        · exact Or.inr hn'
        · exact Or.inl (hask.2 ▸ hd')
      split
      next =>
        have k₁ : Closed g { q.2 with done := n :: q.2.done, records := n :: q.2.records } Z
            (· ∈ n :: q.2.done) := by
          intro z hz
          obtain ⟨hz₁, hz₂⟩ := hc z hz
          refine ⟨fun k hk => by simpa [hask.1] using hz₁ k hk, fun c h => ?_⟩
          rcases hz₂ c h with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl (List.mem_cons_of_mem _ (hask.2 ▸ h)))
          · exact Or.inr (Or.inr h)
        have k₂ : DoneOK { q.2 with done := n :: q.2.done, records := n :: q.2.records } := by
          intro d hd'
          simp only [List.mem_cons] at hd'
          rcases hd' with rfl | hd'
          · exact Or.inl (List.mem_cons_self ..)
          · exact (hdq d hd').imp_left (List.mem_cons_of_mem _)
        have k₃ : ∀ j < (g n).length, (n, 0 + j) ∈ q.2.reads := by
          intro j hj
          rcases hn' with hz | hz
          · simpa [hask.1] using (hc n hz).1 j hj
          · simp [hz] at hj
        have k₄ : ∀ c ∈ g n, Z c ∨ c ∈ n :: q.2.done ∨ g c = [] := by
          intro c h
          rcases hn' with hz | hz
          · rcases (hc n hz).2 c h with h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl (List.mem_cons_of_mem _ (hask.2 ▸ h)))
            · exact Or.inr (Or.inr h)
          · rw [hz] at h; cases h
        obtain ⟨e₁, e₂⟩ := slots_behind Z (fun s c hs hd' hc' => ih s c hs hd' hc')
          (disc_grows fuel) (disc_doneOK fuel) n (g n) 0
          { q.2 with done := n :: q.2.done, records := n :: q.2.records } k₁ k₂ k₃ k₄
        refine ⟨e₁.trans hask.1, fun d hd' => ?_⟩
        rcases e₂ d hd' with h | h
        · exact hnew d h
        · exact Or.inr h
      next => exact ⟨hask.1, hnew⟩

end Behind2

/-! ## Invariants of every state -/

section Invariants

variable {g : Graph} {o : Oracle} {qfuel : Nat}

/-- An object settled as needing no copy was entered, unless it has no slots. -/
def MemoOK (g : Graph) (s : State) : Prop := ∀ n, s.memo n = some false → g n = [] ∨ (n, 0) ∈ s.reads

/-- A visited object was entered, unless it has no slots; inside the walk of `n` from slot 0, `n`
may not be yet. -/
def VisitedOK (g : Graph) (s : State) (n : Option Nat) : Prop :=
  ∀ v ∈ s.visited, g v = [] ∨ (v, 0) ∈ s.reads ∨ n = some v

theorem walk_reads_head (f : State → Nat → Result) (n i : Nat) (s : State) (c : Nat)
    (cs : List Nat) (hf : ∀ s c, Mono s (f s c).state) :
    (n, i) ∈ (walk o f n i s (c :: cs)).state.reads := by
  have h₁ : (n, i) ∈ (step o f n i s c).state.reads := by
    unfold step; split
    · exact mem_read s (n, i)
    · exact (hf _ _).reads.subset (mem_read s (n, i))
  simp only [walk]
  split
  · exact h₁
  · exact (walk_mono hf n cs (i + 1) _).reads.subset h₁

theorem walk_ok {f : State → Nat → Result}
    (hf : ∀ s c, MemoOK g s → VisitedOK g s none →
      MemoOK g (f s c).state ∧ VisitedOK g (f s c).state none)
    (n : Nat) :
    ∀ (cs : List Nat) i s, MemoOK g s → VisitedOK g s (if i = 0 then some n else none) →
      MemoOK g (walk o f n i s cs).state ∧
        VisitedOK g (walk o f n i s cs).state (if i = 0 ∧ cs = [] then some n else none) := by
  intro cs
  induction cs with
  | nil =>
    intro i s hm hv
    refine ⟨hm, fun v hv' => ?_⟩
    rcases hv v hv' with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · right; right; split at h <;> simp_all
  | cons c cs ih =>
    intro i s hm hv
    have hr : MemoOK g (s.read (n, i)) ∧ VisitedOK g (s.read (n, i)) none := by
      have hmono := read_mono s (n, i)
      refine ⟨fun m hm' => ?_, fun v hv' => ?_⟩
      · rcases hm m (by simpa using hm') with h | h
        · exact Or.inl h
        · exact Or.inr (hmono.reads.subset h)
      · have hv'' : v ∈ s.visited := by simpa using hv'
        rcases hv v hv'' with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (hmono.reads.subset h))
        · split at h
          · cases h; subst ‹i = 0›; exact Or.inr (Or.inl (mem_read s (n, 0)))
          · cases h
    have h₁ : MemoOK g (step o f n i s c).state ∧ VisitedOK g (step o f n i s c).state none := by
      unfold step; split
      · exact hr
      · exact hf _ c hr.1 hr.2
    simp only [walk]
    split
    · exact ⟨h₁.1, fun v hv' => (h₁.2 v hv').imp_right (Or.imp_right (fun h => by cases h))⟩
    · obtain ⟨a, b⟩ := ih (i + 1) _ h₁.1 (by simpa using h₁.2)
      exact ⟨a, fun v hv' => (b v hv').imp_right (Or.imp_right (fun h => by simp at h))⟩

theorem check_ok : ∀ fuel s n, MemoOK g s → VisitedOK g s none →
    MemoOK g (check g o fuel s n).state ∧ VisitedOK g (check g o fuel s n).state none := by
  intro fuel
  induction fuel with
  | zero => intro s n hm hv; exact ⟨hm, hv⟩
  | succ fuel ih =>
    intro s n hm hv
    have settled : ∀ (r : State) (b : Bool), MemoOK g r → (b = false → g n = [] ∨ (n, 0) ∈ r.reads) →
        MemoOK g (r.settle n b) := by
      intro r b hr hb m hm'
      simp only [State.settle] at hm' ⊢
      split at hm'
      · subst m; cases hm'; exact hb rfl
      · exact hr m hm'
    simp only [check]
    split
    · exact ⟨hm, hv⟩
    · split
      · exact ⟨hm, hv⟩
      · split
        · exact ⟨settled s true hm (by simp), hv⟩
        · split
          · exact ⟨hm, hv⟩
          · have hw := walk_ok (o := o) (fun s c h₁ h₂ => ih s c h₁ h₂) n (g n) 0
              { s with visited := n :: s.visited } hm (fun v hv' => by
                simp only [List.mem_cons] at hv'
                rcases hv' with rfl | hv'
                · simp
                · exact (hv v hv').imp_right (Or.imp_right (fun h => by cases h)))
            have hread : g n = [] ∨ (n, 0) ∈
                (walk o (check g o fuel) n 0 { s with visited := n :: s.visited } (g n)).state.reads := by
              cases hg : g n with
              | nil => exact Or.inl rfl
              | cons c cs => exact Or.inr (walk_reads_head _ n 0 _ c cs (check_mono fuel))
            have hv₂ : VisitedOK g (walk o (check g o fuel) n 0 { s with visited := n :: s.visited }
                (g n)).state none := by
              intro v hv'
              rcases hw.2 v hv' with h | h | h
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · simp only [true_and] at h
                split at h
                · cases h; rename_i hg; exact Or.inl hg
                · cases h
            split
            · exact ⟨settled _ true hw.1 (by simp), fun v h => hv₂ v h⟩
            · split
              · exact ⟨settled _ true hw.1 (by simp), fun v h => hv₂ v h⟩
              · split
                · exact ⟨hw.1, hv₂⟩
                · exact ⟨settled _ false hw.1 (fun _ => hread), fun v h => hv₂ v h⟩

theorem question_ok (fuel : Nat) (s : State) (n : Nat) (hm : MemoOK g s) :
    MemoOK g (question g o fuel s n).2 := by
  have hc := check_ok (g := g) (o := o) fuel { s with visited := [] } n hm (by simp [VisitedOK])
  rw [question_eq]
  generalize check g o fuel { s with visited := [] } n = r at hc ⊢
  simp only
  split
  · exact hc.1
  · obtain ⟨h₁, -, -, -, -, h₆, -⟩ := settlePending_spec r.state.visited r.state
    intro m hm'
    simp only at hm'
    rcases h₆ m hm' with h | h
    · rcases hc.1 m h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by simp only; rw [h₁]; exact h')
    · rcases hc.2 m h with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (by simp only; rw [h₁]; exact h')
      · cases h'

theorem disc_ok : ∀ fuel s n, MemoOK g s → MemoOK g (disc g o qfuel fuel s n) := by
  intro fuel
  induction fuel with
  | zero => intro s n h; exact h
  | succ fuel ih =>
    intro s n h
    have hslots : ∀ (cs : List Nat) i s', MemoOK g s' →
        MemoOK g (slots (disc g o qfuel fuel) n i s' cs) := by
      intro cs
      induction cs with
      | nil => intro i s' h'; exact h'
      | cons c cs ihc =>
        intro i s' h'
        apply ihc
        apply ih
        intro m hm'
        have hmono := read_mono s' (n, i)
        rcases h' m (by simpa using hm') with h'' | h''
        · exact Or.inl h''
        · exact Or.inr (hmono.reads.subset h'')
    simp only [disc]
    split
    · exact h
    · have hq : MemoOK g (if o.changed s n then (true, s) else question g o qfuel s n).2 := by
        split
        · exact h
        · exact question_ok qfuel s n h
      generalize (if o.changed s n then (true, s) else question g o qfuel s n) = q at hq ⊢
      split
      · exact hslots _ _ _ hq
      · exact hq

end Invariants

/-! ## The probe walks in lockstep with the depth-first walk -/

section Probe

variable {g : Graph} {o : Oracle} {qfuel : Nat}

/-- The objects seen so far other than the frontier `A` are finished: all their slots read, and
their children seen, unless they have no slots. -/
def Good (g : Graph) (s : State) (A S : List Nat) : Prop :=
  ∀ n ∈ S, n ∉ A → Full g s n ∧ ∀ c ∈ g n, c ∈ S ∨ g c = []

theorem Good.mono {s s' : State} {A S : List Nat} (h : s.reads <+: s'.reads) (hg : Good g s A S) :
    Good g s' A S :=
  fun n hn hA => ⟨fun k hk => h.subset ((hg n hn hA).1 k hk), (hg n hn hA).2⟩

/-- A finished frame extends `Good` to the objects it entered. -/
theorem Good.extend {F : Frame} {S S' A : List Nat} {T : List Slot} {s : State}
    (D : Dfs g F S T S') (hg : Good g s A S) (hT : ∀ x ∈ T, x ∈ s.reads) : Good g s A S' := by
  intro n hn hA
  by_cases hS : n ∈ S
  · obtain ⟨h₁, h₂⟩ := hg n hS hA
    exact ⟨h₁, fun c hc => (h₂ c hc).imp_left D.sub⟩
  · obtain ⟨h₁, h₂⟩ := D.finished.1 n hn hS
    exact ⟨fun k hk => hT _ (h₁ k hk), h₂⟩

/-- How far a frame of the depth-first walk is read, in a way discovery can resume: nothing; all
of it; an entered object whose answer is settled as needing a copy, read partway; or a slot read
with its child read partway, or with its child finished and later slots read partway. -/
inductive Part (g : Graph) (memo : Nat → Option Bool) :
    Frame → List Nat → List Slot → List Nat → List Slot → Prop
  | none {F S T S'} : Dfs g F S T S' → Part g memo F S T S' []
  | all {F S T S'} : Dfs g F S T S' → Part g memo F S T S' T
  | visit {n S T S' t} : n ∉ S → g n ≠ [] → memo n = some true →
      Part g memo (.resume n 0 (g n)) (n :: S) T S' t → Part g memo (.visit n) S T S' t
  | here {n i c cs S S₁ S₂ T₁ T₂ t} : Dfs g (.visit c) S T₁ S₁ →
      Dfs g (.resume n (i + 1) cs) S₁ T₂ S₂ → Part g memo (.visit c) S T₁ S₁ t →
      Part g memo (.resume n i (c :: cs)) S ((n, i) :: (T₁ ++ T₂)) S₂ ((n, i) :: t)
  | later {n i c cs S S₁ S₂ T₁ T₂ t} : Dfs g (.visit c) S T₁ S₁ →
      Part g memo (.resume n (i + 1) cs) S₁ T₂ S₂ t →
      Part g memo (.resume n i (c :: cs)) S ((n, i) :: (T₁ ++ T₂)) S₂ ((n, i) :: (T₁ ++ t))

theorem Part.mono {memo memo' : Nat → Option Bool}
    (h : ∀ n, memo n = some true → memo' n = some true) {F : Frame} {S S' : List Nat}
    {T t : List Slot} (p : Part g memo F S T S' t) : Part g memo' F S T S' t := by
  induction p with
  | none D => exact .none D
  | all D => exact .all D
  | visit h₁ h₂ h₃ _ ih => exact .visit h₁ h₂ (h _ h₃) ih
  | here D₁ D₂ _ ih => exact .here D₁ D₂ ih
  | later D₁ _ ih => exact .later D₁ ih

theorem Part.dfs {memo : Nat → Option Bool} {F : Frame} {S S' : List Nat} {T t : List Slot}
    (p : Part g memo F S T S' t) : Dfs g F S T S' := by
  induction p with
  | none D => exact D
  | all D => exact D
  | visit h₁ h₂ _ _ ih => exact .fresh h₁ h₂ ih
  | here D₁ D₂ _ _ => exact .cons D₁ D₂
  | later D₁ _ ih => exact .cons D₁ ih

/-- An object finished by its walk leaves the frontier. -/
theorem Good.pop {m : Nat} {S S' A : List Nat} {T : List Slot} {s : State}
    (D : Dfs g (.resume m 0 (g m)) (m :: S) T S') (hg : Good g s (m :: A) S')
    (hT : ∀ x ∈ T, x ∈ s.reads) : Good g s A S' := by
  intro n hn hA
  by_cases hnm : n = m
  · subst hnm
    obtain ⟨-, h₁, h₂⟩ := D.finished
    exact ⟨fun k hk => hT _ (by simpa using h₁ k hk), h₂⟩
  · exact hg n hn (by simp [hnm, hA])

/-- What the probe of a frame leaves: the reads it added are a prefix `t` of the frame's slots,
read resumably; a negative answer read them all and finished the frame. -/
def Probed (g : Graph) (r : Result) (R : List Slot) (A : List Nat) (F : Frame) (S : List Nat)
    (T : List Slot) (S' : List Nat) : Prop :=
  ∃ t, r.state.reads = R ++ t ∧ Part g r.state.memo F S T S' t ∧
    (r.needs = false → t = T ∧ Good g r.state A S')

/-- The probe of a frame from a state in step with the depth-first walk that reached it: the
slots read so far are `R`, each of an object seen; the seen objects off the frontier `A` are
finished, and every frontier object blocks the probe. -/
theorem probe {F : Frame} {S S' : List Nat} {T : List Slot} (D : Dfs g F S T S') :
    ∀ (fuel : Nat) (s : State) (R : List Slot) (A : List Nat),
      s.reads = R → (R ++ T).Nodup → (∀ x ∈ R, x.1 ∈ S) → Good g s A S →
      (∀ a ∈ A, a ∈ S ∧ Blocks s a) → MemoOK g s →
      (∀ d ∈ s.records, d ∈ S ∨ g d = []) →
      (match F with
        | .visit _ => VisitedOK g s none
        | .resume n i _ => n ∈ A ∧ VisitedOK g s (if i = 0 then some n else none)) →
      Probed g (match F with
        | .visit m => check g o fuel s m
        | .resume n i cs => walk o (check g o fuel) n i s cs) R A F S T S' := by
  induction D with
  | @seen m S hm =>
    intro fuel s R A hR _ _ hg hA _ _ _
    have hc := check_behind (g := g) (o := o) (fun x => x ∈ S ∧ x ∉ A) fuel s m
      (fun z hz => ⟨(hg z hz.1 hz.2).1, fun c hc => by
        rcases (hg z hz.1 hz.2).2 c hc with h | h
        · by_cases hcA : c ∈ A
          · exact Or.inr (Or.inl (hA c hcA).2)
          · exact Or.inl ⟨h, hcA⟩
        · exact Or.inr (Or.inr h)⟩)
      (by by_cases hmA : m ∈ A
          · exact Or.inr (Or.inl (hA m hmA).2)
          · exact Or.inl ⟨hm, hmA⟩)
    refine ⟨[], by simp [hc, hR], .none (.seen hm), fun _ => ⟨rfl, ?_⟩⟩
    exact hg.mono (check_mono fuel s m).reads
  | @leaf m S hm =>
    intro fuel s R A hR _ _ hg _ _ _ _
    have hc := check_behind (g := g) (o := o) (fun _ => False) fuel s m (fun _ h => h.elim)
      (Or.inr (Or.inr hm))
    exact ⟨[], by simp [hc, hR], .none (.leaf hm), fun _ => ⟨rfl, hg.mono (check_mono fuel s m).reads⟩⟩
  | @fresh m S T S' hmS hgm D ih =>
    intro fuel s R A hR hnd hRS hg hA hmemo hrec hvis
    simp only at hvis
    have hunread : (m, 0) ∉ s.reads := fun h => hmS (hRS _ (hR ▸ h))
    cases fuel with
    | zero => exact ⟨[], by simp [check, hR], .none (.fresh hmS hgm D), fun h => by simp [check] at h⟩
    | succ fuel =>
      simp only [check]
      split
      · exact ⟨[], by simp [hR], .none (.fresh hmS hgm D), fun h => by simp at h⟩
      · split
        · rename_i b hb
          refine ⟨[], by simp [hR], .none (.fresh hmS hgm D), fun h => ?_⟩
          simp only at h
          subst h
          rcases hmemo m hb with h | h
          · exact absurd h hgm
          · exact absurd h hunread
        · rename_i hmn
          split
          · exact ⟨[], by simp [State.settle, hR], .none (.fresh hmS hgm D), fun h => by simp at h⟩
          · split
            · rename_i hv
              refine ⟨[], by simp [hR], .none (.fresh hmS hgm D), fun _ => ?_⟩
              rcases hvis m hv with h | h | h
              · exact absurd h hgm
              · exact absurd h hunread
              · cases h
            · rename_i hv
              -- The walk of `m`, one level deeper in the depth-first walk.
              generalize hs₁ : { s with visited := m :: s.visited } = s₁
              have hm₁ : Mono s s₁ := by
                rw [← hs₁]
                exact ⟨List.prefix_refl _, fun _ _ h => h, fun _ h => List.mem_cons_of_mem _ h, rfl, rfl⟩
              have hp := ih fuel s₁ R (m :: A) (by rw [← hs₁]; exact hR) hnd
                (fun x hx => List.mem_cons_of_mem _ (hRS x hx))
                (by
                  intro n hn hnA
                  simp only [List.mem_cons, not_or] at hn hnA
                  rcases hn with rfl | hn
                  · exact absurd rfl hnA.1
                  · obtain ⟨h₁, h₂⟩ := hg n hn hnA.2
                    exact ⟨fun k hk => hm₁.reads.subset (h₁ k hk),
                      fun c hc => (h₂ c hc).imp_left (List.mem_cons_of_mem _)⟩)
                (by
                  intro a ha
                  simp only [List.mem_cons] at ha
                  rcases ha with rfl | ha
                  · exact ⟨List.mem_cons_self .., Or.inr (Or.inr (by rw [← hs₁]; exact List.mem_cons_self ..))⟩
                  · exact ⟨List.mem_cons_of_mem _ (hA a ha).1, Blocks.mono hm₁ (hA a ha).2⟩)
                (by rw [← hs₁]; exact hmemo)
                (by
                  intro d hd
                  rw [← hs₁] at hd
                  exact (hrec d hd).imp_left (List.mem_cons_of_mem _))
                (by
                  refine ⟨List.mem_cons_self .., fun v hv' => ?_⟩
                  rw [← hs₁] at hv' ⊢
                  simp only [List.mem_cons] at hv'
                  rcases hv' with rfl | hv'
                  · simp
                  · exact (hvis v hv').imp_right (Or.imp_right (fun h => by cases h)))
              simp only at hp
              generalize walk o (check g o fuel) m 0 s₁ (g m) = r at hp ⊢
              obtain ⟨t, hreads, hpart, hneg⟩ := hp
              have hsettle : ∀ b, (r.state.settle m b).reads = r.state.reads := fun _ => rfl
              have pop : r.needs = false → Good g r.state A S' := fun h =>
                Good.pop D (hneg h).2 (fun x hx => by rw [hreads, (hneg h).1]; exact List.mem_append_right _ hx)
              split
              · refine ⟨t, by rw [hsettle, hreads], .visit hmS hgm (by simp [State.settle]) ?_,
                  fun h => by simp at h⟩
                exact hpart.mono (fun n h => by
                  simp only [State.settle]; split
                  · rfl
                  · exact h)
              · rename_i hneeds
                have hn : r.needs = false := by simpa using hneeds
                obtain ⟨ht, -⟩ := hneg hn
                rw [ht] at hreads
                split
                · exact ⟨T, by rw [hsettle, hreads], .all (.fresh hmS hgm D), fun h => by simp at h⟩
                · split
                  · exact ⟨T, hreads, .all (.fresh hmS hgm D), fun _ => ⟨rfl, pop hn⟩⟩
                  · exact ⟨T, by rw [hsettle, hreads], .all (.fresh hmS hgm D),
                      fun _ => ⟨rfl, (pop hn).mono (List.prefix_refl _)⟩⟩
  | @nil n i S =>
    intro fuel s R A hR _ _ hg _ _ _ _
    exact ⟨[], by simp [walk, hR], .none .nil, fun _ => ⟨rfl, hg⟩⟩
  | @cons n i c cs S S₁ S₂ T₁ T₂ D₁ D₂ ih₁ ih₂ =>
    intro fuel s R A hR hnd hRS hg hA hmemo hrec hres
    obtain ⟨hnA, hvis⟩ := hres
    have hnS : n ∈ S := (hA n hnA).1
    have hfresh : (n, i) ∉ R := by
      intro h
      have := (List.nodup_append.mp hnd).2.2 _ h _ (List.mem_cons_self ..)
      exact this rfl
    have hread : (s.read (n, i)).reads = R ++ [(n, i)] := by
      rw [read_reads, if_neg (by rw [hR]; exact hfresh), hR]
    have hm₀ := read_mono s (n, i)
    have hvis₀ : VisitedOK g (s.read (n, i)) none := by
      intro v hv
      simp only [read_visited] at hv
      rcases hvis v hv with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (hm₀.reads.subset h))
      · split at h
        · cases h; subst ‹i = 0›; exact Or.inr (Or.inl (mem_read s (n, 0)))
        · cases h
    have hnd₁ : ((R ++ [(n, i)]) ++ T₁).Nodup :=
      hnd.sublist (by simp)
    have hp₁ := ih₁ fuel (s.read (n, i)) (R ++ [(n, i)]) A hread hnd₁
      (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hRS x hx
        · exact hnS)
      (hg.mono hm₀.reads) (fun a ha => ⟨(hA a ha).1, Blocks.mono hm₀ (hA a ha).2⟩)
      (by intro m h; rcases hmemo m (by simpa using h) with h' | h'
          · exact Or.inl h'
          · exact Or.inr (hm₀.reads.subset h'))
      (fun d hd => hrec d (by simpa using hd)) hvis₀
    simp only at hp₁
    have hmemo₀ : MemoOK g (s.read (n, i)) := by
      intro m h; rcases hmemo m (by simpa using h) with h' | h'
      · exact Or.inl h'
      · exact Or.inr (hm₀.reads.subset h')
    simp only [walk, step]
    split
    · -- A draft handle: the probe stops at the slot.
      exact ⟨[(n, i)], by simp [hread], .here D₁ D₂ (.none D₁), fun h => by simp at h⟩
    · have hok := check_ok (g := g) (o := o) fuel (s.read (n, i)) c hmemo₀ hvis₀
      have hmono := check_mono (g := g) (o := o) fuel (s.read (n, i)) c
      generalize check g o fuel (s.read (n, i)) c = r at hp₁ hok hmono ⊢
      obtain ⟨t₁, hr₁, hpart₁, hneg₁⟩ := hp₁
      split
      · exact ⟨(n, i) :: t₁, by simp [hr₁], .here D₁ D₂ hpart₁, fun h => by simp_all⟩
      · rename_i hneeds
        have hn : r.needs = false := by simpa using hneeds
        obtain ⟨ht₁, hg₁⟩ := hneg₁ hn
        rw [ht₁] at hr₁
        have hp₂ := ih₂ fuel r.state (R ++ [(n, i)] ++ T₁) A hr₁
          (by simpa [List.append_assoc] using hnd)
          (fun x hx => by
            simp only [List.mem_append, List.mem_singleton] at hx
            rcases hx with (hx | rfl) | hx
            · exact D₁.sub (hRS x hx)
            · exact D₁.sub hnS
            · exact (D₁.owns x hx).2)
          hg₁ (fun a ha => ⟨D₁.sub (hA a ha).1, Blocks.mono (hm₀.trans hmono) (hA a ha).2⟩)
          hok.1 (fun d hd => by
            rw [hmono.records] at hd
            exact (hrec d (by simpa using hd)).imp_left D₁.sub)
          ⟨hnA, by simpa using hok.2⟩
        simp only at hp₂
        obtain ⟨t₂, hr₂, hpart₂, hneg₂⟩ := hp₂
        refine ⟨(n, i) :: (T₁ ++ t₂), by simp [hr₂], .later D₁ hpart₂, fun h => ?_⟩
        obtain ⟨ht₂, hg₂⟩ := hneg₂ h
        exact ⟨by rw [ht₂], hg₂⟩

end Probe

/-! ## Discovery resumes the depth-first walk where the probe left it -/

section Resume

variable {g : Graph} {o : Oracle} {qfuel : Nat}

theorem with_visited_nil {s : State} (h : s.visited = []) : { s with visited := [] } = s := by
  cases s; simp_all

/-- A question about an object settled as needing a copy answers yes and changes nothing. -/
theorem question_memo_true {s : State} {m : Nat} (hm : s.memo m = some true) (hv : s.visited = []) :
    question g o qfuel s m = (true, s) := by
  rw [question_eq]
  cases qfuel with
  | zero => simp [check, with_visited_nil hv]
  | succ fuel =>
    simp only [check]
    split
    · simp [with_visited_nil hv]
    · simp [hm, with_visited_nil hv]

/-- Every record was resolved. -/
def RecordsOK (s : State) : Prop := ∀ n ∈ s.records, n ∈ s.done

theorem slots_preserve {P : State → Prop} {f : State → Nat → State}
    (hr : ∀ s x, P s → P (s.read x)) (hf : ∀ s c, P s → P (f s c)) (n : Nat) :
    ∀ (cs : List Nat) i s, P s → P (slots f n i s cs) := by
  intro cs
  induction cs with
  | nil => intro i s h; exact h
  | cons c cs ih => intro i s h; exact ih _ _ (hf _ _ (hr _ _ h))

theorem disc_records : ∀ fuel s n, RecordsOK s → RecordsOK (disc g o qfuel fuel s n) := by
  intro fuel
  induction fuel with
  | zero => intro s n h; exact h
  | succ fuel ih =>
    intro s n h
    simp only [disc]
    split
    · exact h
    · have hq : RecordsOK (if o.changed s n then (true, s) else question g o qfuel s n).2 := by
        split
        · exact h
        · obtain ⟨hm, -⟩ := question_mono (g := g) (o := o) qfuel s n
          intro d hd; rw [hm.records] at hd; rw [hm.done]; exact h d hd
      generalize (if o.changed s n then (true, s) else question g o qfuel s n) = q at hq ⊢
      split
      · refine slots_preserve (fun s x h d hd => by simpa using h d (by simpa using hd))
          (ih) n (g n) 0 _ ?_
        intro d hd
        simp only [List.mem_cons] at hd ⊢
        rcases hd with rfl | hd
        · exact Or.inl rfl
        · exact Or.inr (hq d hd)
      · intro d hd; exact List.mem_cons_of_mem _ (hq d hd)

/-- A visited frame read resumably is read resumably from its first slot. -/
theorem Part.enter {memo : Nat → Option Bool} {m : Nat} {S S' : List Nat} {T t : List Slot}
    (p : Part g memo (.visit m) S T S' t) (D : Dfs g (.resume m 0 (g m)) (m :: S) T S') :
    Part g memo (.resume m 0 (g m)) (m :: S) T S' t := by
  cases p with
  | none => exact .none D
  | all => exact .all D
  | visit _ _ _ p' => exact p'

theorem closed_of_good {s : State} {A S : List Nat} (hg : Good g s A S) (hA : ∀ a ∈ A, a ∈ s.done) :
    Closed g s (fun x => x ∈ S ∧ x ∉ A) (· ∈ s.done) := by
  intro z hz
  obtain ⟨h₁, h₂⟩ := hg z hz.1 hz.2
  refine ⟨h₁, fun c hc => ?_⟩
  rcases h₂ c hc with h | h
  · by_cases hcA : c ∈ A
    · exact Or.inr (Or.inl (hA c hcA))
    · exact Or.inl ⟨h, hcA⟩
  · exact Or.inr (Or.inr h)

/-- The question of discovery about an object the depth-first walk is about to enter, from a state
in step with it: the probe of the object, its pending answers settled when it answers no. -/
theorem question_probe {m : Nat} {S S' : List Nat} {T : List Slot}
    (D : Dfs g (.visit m) S T S') (s : State) (R : List Slot) (A : List Nat)
    (hR : s.reads = R) (hnd : (R ++ T).Nodup) (hRS : ∀ x ∈ R, x.1 ∈ S) (hg : Good g s A S)
    (hA : ∀ a ∈ A, a ∈ S ∧ a ∈ s.records) (hmemo : MemoOK g s)
    (hrec : ∀ d ∈ s.records, d ∈ S ∨ g d = []) (hvis : s.visited = []) :
    ∃ t, (question g o qfuel s m).2.reads = R ++ t ∧
      Part g (question g o qfuel s m).2.memo (.visit m) S T S' t ∧
      ((question g o qfuel s m).1 = false → t = T ∧ Good g (question g o qfuel s m).2 A S') := by
  have hp := probe (o := o) D qfuel s R A hR hnd hRS hg (fun a ha => ⟨(hA a ha).1, Or.inl (hA a ha).2⟩)
    hmemo hrec (by simp [VisitedOK, hvis])
  simp only at hp
  rw [question_eq, with_visited_nil hvis]
  generalize check g o qfuel s m = r at hp ⊢
  obtain ⟨t, h₁, h₂, h₃⟩ := hp
  simp only
  split
  · exact ⟨t, h₁, h₂, fun h => by simp at h⟩
  · rename_i hneg
    obtain ⟨e₁, -, -, -, e₅, -, -⟩ := settlePending_spec r.state.visited r.state
    have hn : r.needs = false := by simpa using hneg
    refine ⟨t, by simpa [e₁] using h₁, h₂.mono (fun n h => e₅ n true h), fun _ => ?_⟩
    exact ⟨(h₃ hn).1, (h₃ hn).2.mono (by simp [e₁])⟩

/-- What discovery of a frame leaves: the frame's slots all read, in depth-first order after the
earlier reads `R`, the frame finished, and every resolved object seen. -/
def Resumed (g : Graph) (s : State) (R : List Slot) (A : List Nat) (T : List Slot)
    (S' : List Nat) : Prop :=
  s.reads = R ++ T ∧ Good g s A S' ∧ ∀ d ∈ s.done, d ∈ S' ∨ g d = []

/-- Discovery of a frame read up to `t` resumably, from a state in step with the depth-first walk
that reached the frame: the frontier `A` holds records, the seen objects off it are finished,
every resolved object is seen, and no question is open. With fuel for one nested object per
object the frame enters, discovery reads the rest of the frame's slots in depth-first order. -/
theorem resume {F : Frame} {S S' : List Nat} {T : List Slot} (D : Dfs g F S T S') :
    ∀ (fuel : Nat) (s : State) (R t : List Slot) (A : List Nat),
      Part g s.memo F S T S' t → s.reads = R ++ t → (R ++ T).Nodup → (∀ x ∈ R, x.1 ∈ S) →
      Good g s A S → (∀ a ∈ A, a ∈ S ∧ a ∈ s.records) → MemoOK g s → DoneOK s → RecordsOK s →
      (∀ d ∈ s.done, d ∈ S ∨ g d = []) → s.visited = [] → S'.length ≤ S.length + fuel →
      (match F with
        | .visit _ => True
        | .resume n _ _ => n ∈ A) →
      Resumed g (match F with
        | .visit m => disc g o qfuel fuel s m
        | .resume n i cs => slots (disc g o qfuel fuel) n i s cs) R A T S' := by
  induction D with
  | @seen m S hm =>
    intro fuel s R t A hp hR _ _ hg hA _ hdone hrec hdS _ _ _
    have ht : t = [] := by
      cases hp with
      | none => rfl
      | all => rfl
      | visit h => exact absurd hm h
    subst ht
    have hb := disc_behind (g := g) (o := o) (qfuel := qfuel) (fun x => x ∈ S ∧ x ∉ A) fuel s m
      (closed_of_good hg (fun a ha => hrec a (hA a ha).2)) hdone
      (by by_cases hmA : m ∈ A
          · exact Or.inr (Or.inl (hrec m (hA m hmA).2))
          · exact Or.inl ⟨hm, hmA⟩)
    refine ⟨by rw [hb.1, hR], hg.mono (disc_grows fuel s m).reads, fun d hd => ?_⟩
    rcases hb.2 d hd with h | h | h
    · exact hdS d h
    · exact Or.inl h.1
    · exact Or.inr h
  | @leaf m S hm =>
    intro fuel s R t A hp hR _ _ hg _ _ hdone _ hdS _ _ _
    have ht : t = [] := by
      cases hp with
      | none => rfl
      | all => rfl
      | visit _ h => exact absurd hm h
    subst ht
    have hb := disc_behind (g := g) (o := o) (qfuel := qfuel) (fun _ => False) fuel s m
      (fun _ h => h.elim) hdone (Or.inr (Or.inr hm))
    refine ⟨by rw [hb.1, hR], hg.mono (disc_grows fuel s m).reads, fun d hd => ?_⟩
    rcases hb.2 d hd with h | h | h
    · exact hdS d h
    · exact h.elim
    · exact Or.inr h
  | @fresh m S T S' hmS hgm D' ih =>
    intro fuel s R t A hp hR hnd hRS hg hA hmemo hdone hrec hdS hvis hfuel _
    have hmd : m ∉ s.done := fun h => (hdS m h).elim hmS hgm
    have hmS' : m ∈ S' := D'.sub (List.mem_cons_self ..)
    have hAS : ∀ a ∈ A, a ∈ S' := fun a ha => D'.sub (List.mem_cons_of_mem _ (hA a ha).1)
    -- A frame read entirely: discovery walks behind it.
    have behind : t = T → Resumed g (disc g o qfuel fuel s m) R A T S' := by
      intro ht
      subst ht
      have hgT : Good g s A S' := Good.extend (.fresh hmS hgm D') hg
        (fun x hx => by rw [hR]; exact List.mem_append_right _ hx)
      have hb := disc_behind (g := g) (o := o) (qfuel := qfuel) (fun x => x ∈ S' ∧ x ∉ A) fuel s m
        (closed_of_good hgT (fun a ha => hrec a (hA a ha).2)) hdone
        (Or.inl ⟨hmS', fun h => hmS (hA m h).1⟩)
      refine ⟨by rw [hb.1, hR], hgT.mono (disc_grows fuel s m).reads, fun d hd => ?_⟩
      rcases hb.2 d hd with h | h | h
      · exact (hdS d h).imp_left (fun h => D'.sub (List.mem_cons_of_mem _ h))
      · exact Or.inl h.1
      · exact Or.inr h
    -- The fuel covers the object entered.
    cases fuel with
    | zero =>
      exfalso
      obtain ⟨L, hL, -, -⟩ := (Dfs.fresh hmS hgm D').extends
      have : m ∈ L := by
        have h := hmS'
        rw [hL] at h
        rcases List.mem_append.mp h with h | h
        · exact h
        · exact absurd h hmS
      have hpos := List.length_pos_of_mem this
      rw [hL] at hfuel
      simp at hfuel
      omega
    | succ fuel =>
      -- An active object becomes a record and its slots are resolved, one level deeper.
      have active : ∀ (s₁ : State) (t₁ : List Slot),
          Part g s₁.memo (.resume m 0 (g m)) (m :: S) T S' t₁ → s₁.reads = R ++ t₁ →
          Good g s₁ A S → (∀ a ∈ A, a ∈ s₁.records) → MemoOK g s₁ → DoneOK s₁ → RecordsOK s₁ →
          (∀ d ∈ s₁.done, d ∈ S ∨ g d = []) → s₁.visited = [] →
          Resumed g (slots (disc g o qfuel fuel) m 0
            { s₁ with done := m :: s₁.done, records := m :: s₁.records } (g m)) R A T S' := by
        intro s₁ t₁ hp₁ hR₁ hg₁ hA₁ hm₁ hd₁ hr₁ hdS₁ hv₁
        have h := ih fuel { s₁ with done := m :: s₁.done, records := m :: s₁.records } R t₁ (m :: A)
          hp₁ hR₁ hnd (fun x hx => List.mem_cons_of_mem _ (hRS x hx))
          (by
            intro n hn hnA
            simp only [List.mem_cons, not_or] at hn hnA
            rcases hn with rfl | hn
            · exact absurd rfl hnA.1
            · obtain ⟨e₁, e₂⟩ := hg₁ n hn hnA.2
              exact ⟨e₁, fun c hc => (e₂ c hc).imp_left (List.mem_cons_of_mem _)⟩)
          (by
            intro a ha
            simp only [List.mem_cons] at ha ⊢
            rcases ha with rfl | ha
            · exact ⟨Or.inl rfl, Or.inl rfl⟩
            · exact ⟨Or.inr (hA a ha).1, Or.inr (hA₁ a ha)⟩)
          hm₁
          (by
            intro d hd
            simp only [List.mem_cons] at hd
            rcases hd with rfl | hd
            · exact Or.inl (List.mem_cons_self ..)
            · exact (hd₁ d hd).imp_left (List.mem_cons_of_mem _))
          (by
            intro d hd
            simp only [List.mem_cons] at hd ⊢
            rcases hd with rfl | hd
            · exact Or.inl rfl
            · exact Or.inr (hr₁ d hd))
          (by
            intro d hd
            simp only [List.mem_cons] at hd ⊢
            rcases hd with rfl | hd
            · exact Or.inl (Or.inl rfl)
            · exact (hdS₁ d hd).imp_left Or.inr)
          hv₁ (by simp; omega) (List.mem_cons_self ..)
        obtain ⟨e₁, e₂, e₃⟩ := h
        exact ⟨e₁, Good.pop D' e₂ (fun x hx => by rw [e₁]; exact List.mem_append_right _ hx), e₃⟩
      simp only [disc, if_neg hmd]
      cases hp with
      | all _ =>
        have := behind rfl
        simpa only [disc, if_neg hmd] using this
      | none _ =>
        split
        · rename_i hc
          exact active s [] (.none D') (by simp [hR]) hg (fun a ha => (hA a ha).2) hmemo hdone
            hrec hdS hvis
        · rename_i hc
          have hq := question_probe (o := o) (qfuel := qfuel) (.fresh hmS hgm D') s R A
            (by simpa using hR) hnd hRS hg hA hmemo
            (fun d hd => hdS d (hrec d hd)) hvis
          obtain ⟨hqm, hqv⟩ := question_mono (g := g) (o := o) qfuel s m
          have hqd := ask_doneOK (g := g) (o := o) (qfuel := qfuel) s m hdone
          rw [if_neg hc] at hqd
          have hqo := question_ok (g := g) (o := o) qfuel s m hmemo
          have hqf := question_false (g := g) (o := o) qfuel s m
          generalize question g o qfuel s m = q at hq hqm hqv hqd hqo hqf ⊢
          obtain ⟨t', h₁, h₂, h₃⟩ := hq
          split
          · rename_i hpos
            exact active q.2 t' (h₂.enter D') h₁ (hg.mono hqm.reads)
              (fun a ha => hqm.records ▸ (hA a ha).2) hqo hqd
              (fun d hd => by rw [hqm.done]; exact hrec d (hqm.records ▸ hd))
              (fun d hd => hdS d (hqm.done ▸ hd)) hqv
          · rename_i hneg
            have hn : q.1 = false := by simpa using hneg
            obtain ⟨ht', hg'⟩ := h₃ hn
            subst ht'
            refine ⟨h₁, hg', fun d hd => ?_⟩
            simp only [List.mem_cons] at hd
            rcases hd with rfl | hd
            · exact Or.inl hmS'
            · exact (hdS d (hqm.done ▸ hd)).imp_left (fun h => D'.sub (List.mem_cons_of_mem _ h))
      | visit _ _ hm' hp' =>
        have hq : (if o.changed s m then (true, s) else question g o qfuel s m) = (true, s) := by
          split
          · rfl
          · exact question_memo_true hm' hvis
        rw [hq]
        exact active s t hp' hR hg (fun a ha => (hA a ha).2) hmemo hdone hrec hdS hvis
  | @nil n i S =>
    intro fuel s R t A hp hR _ _ hg _ _ _ _ hdS _ _ _
    have ht : t = [] := by
      cases hp with
      | none => rfl
      | all => rfl
    subst ht
    exact ⟨by simp [slots, hR], hg, hdS⟩
  | @cons n i c cs S S₁ S₂ T₁ T₂ D₁ D₂ ih₁ ih₂ =>
    intro fuel s R t A hp hR hnd hRS hg hA hmemo hdone hrec hdS hvis hfuel hnA
    simp only at hnA
    have hnS : n ∈ S := (hA n hnA).1
    have hlen₁ : S.length ≤ S₁.length := D₁.length
    have hlen₂ : S₁.length ≤ S₂.length := D₂.length
    have hAS₁ : ∀ a ∈ A, a ∈ S₁ ∧ a ∈ s.records := fun a ha => ⟨D₁.sub (hA a ha).1, (hA a ha).2⟩
    simp only [slots]
    -- The child, then the later slots, each as its part of the frame says.
    have rest : ∀ (s₁ : State) (t₂ : List Slot), Part g s₁.memo (.resume n (i + 1) cs) S₁ T₂ S₂ t₂ →
        s₁.reads = R ++ [(n, i)] ++ T₁ ++ t₂ → Good g s₁ A S₁ → (∀ a ∈ A, a ∈ s₁.records) →
        MemoOK g s₁ → DoneOK s₁ → RecordsOK s₁ → (∀ d ∈ s₁.done, d ∈ S₁ ∨ g d = []) →
        s₁.visited = [] →
        Resumed g (slots (disc g o qfuel fuel) n (i + 1) s₁ cs) R A ((n, i) :: (T₁ ++ T₂)) S₂ := by
      intro s₁ t₂ hp₂ hR₁ hg₁ hA₁ hm₁ hd₁ hr₁ hdS₁ hv₁
      have h := ih₂ fuel s₁ (R ++ [(n, i)] ++ T₁) t₂ A hp₂ hR₁ (by simpa [List.append_assoc] using hnd)
        (fun x hx => by
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with (hx | rfl) | hx
          · exact D₁.sub (hRS x hx)
          · exact D₁.sub hnS
          · exact (D₁.owns x hx).2)
        hg₁ (fun a ha => ⟨(hAS₁ a ha).1, hA₁ a ha⟩) hm₁ hd₁ hr₁ hdS₁ hv₁ (by omega) hnA
      obtain ⟨e₁, e₂, e₃⟩ := h
      exact ⟨by rw [e₁]; simp, e₂, e₃⟩
    generalize hTT : (n, i) :: (T₁ ++ T₂) = TT at hp hR hnd
    cases hp with
    | all _ =>
      subst hTT
      -- The whole frame was read: discovery walks behind it.
      have hgT : Good g s A S₂ := Good.extend (.cons D₁ D₂) hg
        (fun x hx => by rw [hR]; exact List.mem_append_right _ hx)
      have hfin := (Dfs.cons D₁ D₂).finished.2
      have hb := slots_behind (g := g) (fun x => x ∈ S₂ ∧ x ∉ A)
        (fun s c hs hd' hc' => disc_behind (o := o) (qfuel := qfuel) _ fuel s c hs hd' hc')
        (disc_grows fuel) (disc_doneOK fuel) n (c :: cs) i s
        (closed_of_good hgT (fun a ha => hrec a (hA a ha).2)) hdone
        (fun j hj => by rw [hR]; exact List.mem_append_right _ (hfin.1 j hj))
        (fun c' hc' => by
          rcases hfin.2 c' hc' with h | h
          · by_cases hcA : c' ∈ A
            · exact Or.inr (Or.inl (hrec c' (hA c' hcA).2))
            · exact Or.inl ⟨h, hcA⟩
          · exact Or.inr (Or.inr h))
      simp only [slots] at hb
      refine ⟨by rw [hb.1, hR], hgT.mono (by rw [hb.1]; exact List.prefix_refl _), fun d hd => ?_⟩
      · rcases hb.2 d hd with h | h | h
        · exact (hdS d h).imp_left (fun h => D₂.sub (D₁.sub h))
        · exact Or.inl h.1
        · exact Or.inr h
    | none _ =>
      subst hTT
      have hfresh : (n, i) ∉ R := by
        intro h
        have := (List.nodup_append.mp hnd).2.2 _ h _ (List.mem_cons_self ..)
        exact this rfl
      have hread : (s.read (n, i)).reads = R ++ [(n, i)] := by
        rw [read_reads, if_neg (by rw [hR]; simpa using hfresh), hR]; simp
      have hm₀ := read_grows s (n, i)
      have h₁ := ih₁ fuel (s.read (n, i)) (R ++ [(n, i)]) [] A (.none D₁) (by simpa using hread)
        (hnd.sublist (by simp))
        (fun x hx => by
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact hRS x hx
          · exact hnS)
        (hg.mono hm₀.reads) (fun a ha => ⟨(hA a ha).1, by simpa using (hA a ha).2⟩)
        (fun m h => by
          rcases hmemo m (by simpa using h) with h' | h'
          · exact Or.inl h'
          · exact Or.inr (hm₀.reads.subset h'))
        (fun d hd => by simpa using hdone d (by simpa using hd))
        (fun d hd => by simpa using hrec d (by simpa using hd))
        (fun d hd => hdS d (by simpa using hd)) (by simpa using hvis) (by omega) trivial
      simp only at h₁
      have hg₁ := disc_grows (g := g) (o := o) (qfuel := qfuel) fuel (s.read (n, i)) c
      obtain ⟨e₁, e₂, e₃⟩ := h₁
      exact rest _ [] (.none D₂) (by rw [e₁]; simp) e₂
        (fun a ha => hg₁.records a (by simpa using (hA a ha).2))
        (disc_ok fuel _ c (fun m h => by
          rcases hmemo m (by simpa using h) with h' | h'
          · exact Or.inl h'
          · exact Or.inr (hm₀.reads.subset h')))
        (disc_doneOK fuel _ c (fun d hd => by simpa using hdone d (by simpa using hd)))
        (disc_records fuel _ c (fun d hd => by simpa using hrec d (by simpa using hd)))
        e₃ (hg₁.visited (by simpa using hvis))
    | here D₁' _ hpc =>
      obtain ⟨rfl, rfl⟩ := Dfs.det D₁ D₁'
      simp only [List.cons.injEq, List.append_cancel_left_eq, true_and] at hTT
      subst hTT
      have hmem : (n, i) ∈ s.reads := by rw [hR]; simp
      rw [read_of_mem hmem]
      have h₁ := ih₁ fuel s (R ++ [(n, i)]) _ A hpc (by rw [hR]; simp) (hnd.sublist (by simp))
        (fun x hx => by
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact hRS x hx
          · exact hnS)
        hg hA hmemo hdone hrec hdS hvis (by omega) trivial
      simp only at h₁
      have hg₁ := disc_grows (g := g) (o := o) (qfuel := qfuel) fuel s c
      obtain ⟨e₁, e₂, e₃⟩ := h₁
      exact rest _ [] (.none D₂) (by rw [e₁]; simp) e₂ (fun a ha => hg₁.records a (hA a ha).2)
        (disc_ok fuel s c hmemo) (disc_doneOK fuel s c hdone) (disc_records fuel s c hrec) e₃
        (hg₁.visited hvis)
    | later D₁' hp₂ =>
      obtain ⟨rfl, rfl⟩ := Dfs.det D₁ D₁'
      have hT₂ := (Dfs.det D₂ hp₂.dfs).1
      subst hT₂
      have hmem : (n, i) ∈ s.reads := by rw [hR]; simp
      rw [read_of_mem hmem]
      -- The child was read entirely: discovery walks behind it.
      have hgT : Good g s A S₁ := Good.extend D₁ hg
        (fun x hx => by rw [hR]; simp [hx])
      have hb := disc_behind (g := g) (o := o) (qfuel := qfuel) (fun x => x ∈ S₁ ∧ x ∉ A) fuel s c
        (closed_of_good hgT (fun a ha => hrec a (hA a ha).2)) hdone
        (by rcases D₁.visit_mem with h | h
            · by_cases hcA : c ∈ A
              · exact Or.inr (Or.inl (hrec c (hA c hcA).2))
              · exact Or.inl ⟨h, hcA⟩
            · exact Or.inr (Or.inr h))
      have hg₁ := disc_grows (g := g) (o := o) (qfuel := qfuel) fuel s c
      exact rest _ _ (hp₂.mono (fun n h => hg₁.memo n true h)) (by rw [hb.1, hR]; simp)
        (hgT.mono hg₁.reads) (fun a ha => hg₁.records a (hA a ha).2)
        (disc_ok fuel s c hmemo) (disc_doneOK fuel s c hdone) (disc_records fuel s c hrec)
        (fun d hd => by
          rcases hb.2 d hd with h | h | h
          · exact (hdS d h).imp_left D₁.sub
          · exact Or.inl h.1
          · exact Or.inr h)
        (hg₁.visited hvis)

end Resume

/-! ## Every getter once, in depth-first order -/

section Main

variable {g : Graph} {o : Oracle}

/-- A slot the walk reads exists, when each resumed object continues its own slots. -/
theorem Dfs.valid {F : Frame} {S S' : List Nat} {T : List Slot} (D : Dfs g F S T S')
    (hF : ∀ n i cs, F = .resume n i cs → i + cs.length = (g n).length) :
    ∀ x ∈ T, x.2 < (g x.1).length := by
  induction D with
  | seen => simp
  | leaf => simp
  | nil => simp
  | fresh _ _ _ ih => exact ih fun n i cs h => by cases h; simp
  | @cons n i c cs S S₁ S₂ T₁ T₂ D₁ D₂ ih₁ ih₂ =>
    have hn := hF n i (c :: cs) rfl
    intro x hx
    simp only [List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · simp at hn ⊢; omega
    · exact ih₁ (fun _ _ _ h => by cases h) x hx
    · exact ih₂ (fun n' i' cs' h => by cases h; simp at hn ⊢; omega) x hx

/-- An object reachable from the root through slots. -/
inductive Reach (g : Graph) (root : Nat) : Nat → Prop
  | root : Reach g root root
  | step {n c : Nat} : Reach g root n → c ∈ g n → Reach g root c

/-- The walk from the root enters every reachable object that has slots. -/
theorem Dfs.reach {root : Nat} {T : List Slot} {S' : List Nat} (D : Dfs g (.visit root) [] T S')
    {n : Nat} (h : Reach g root n) : n ∈ S' ∨ g n = [] := by
  induction h with
  | root => exact D.visit_mem
  | @step n c _ hc ih =>
    rcases ih with ih | ih
    · exact (D.finished.1 n ih (by simp)).2 c hc
    · rw [ih] at hc; cases hc

/-- The walk from the root reads exactly the slots of the reachable objects, each once. -/
theorem Dfs.slots_iff {root : Nat} {T : List Slot} {S' : List Nat}
    (D : Dfs g (.visit root) [] T S') (x : Slot) :
    x ∈ T ↔ Reach g root x.1 ∧ x.2 < (g x.1).length := by
  constructor
  · intro hx
    refine ⟨?_, D.valid (fun _ _ _ h => by cases h) x hx⟩
    -- Every entered object is reachable.
    have key : ∀ {F : Frame} {S S'' : List Nat} {T' : List Slot}, Dfs g F S T' S'' →
        (∀ m ∈ S, Reach g root m) → (∀ n i cs, F = .resume n i cs → Reach g root n ∧ ∀ c ∈ cs, c ∈ g n) →
        (∀ n, F = .visit n → Reach g root n) → (∀ m ∈ S'', Reach g root m) ∧ ∀ y ∈ T', Reach g root y.1 := by
      intro F S S'' T' D'
      induction D' with
      | seen => intro h _ _; exact ⟨h, by simp⟩
      | leaf => intro h _ _; exact ⟨h, by simp⟩
      | nil => intro h _ _; exact ⟨h, by simp⟩
      | @fresh n S T S' _ _ _ ih =>
        intro h _ hv
        have hn := hv n rfl
        exact ih (fun m hm => by
            rcases List.mem_cons.mp hm with rfl | hm
            · exact hn
            · exact h m hm)
          (fun n' i cs he => by cases he; exact ⟨hn, fun c hc => hc⟩) (fun _ he => by cases he)
      | @cons n i c cs S S₁ S₂ T₁ T₂ _ _ ih₁ ih₂ =>
        intro h hr _
        obtain ⟨hn, hcs⟩ := hr n i (c :: cs) rfl
        obtain ⟨a₁, b₁⟩ := ih₁ h (fun _ _ _ he => by cases he)
          (fun _ he => by cases he; exact .step hn (hcs c (List.mem_cons_self ..)))
        obtain ⟨a₂, b₂⟩ := ih₂ a₁ (fun _ _ _ he => by
            cases he; exact ⟨hn, fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')⟩)
          (fun _ he => by cases he)
        refine ⟨a₂, fun y hy => ?_⟩
        simp only [List.mem_cons, List.mem_append] at hy
        rcases hy with rfl | hy | hy
        · exact hn
        · exact b₁ y hy
        · exact b₂ y hy
    exact (key D (by simp) (fun _ _ _ h => by cases h) (fun _ h => by cases h; exact .root)).2 x hx
  · rintro ⟨hr, hk⟩
    rcases D.reach hr with h | h
    · exact (D.finished.1 x.1 h (by simp)).1 x.2 hk
    · rw [h] at hk; simp at hk

/-- `produce` reads each slot of the result for the first time in depth-first order: the question
about the result, then discovery, with fuel for one nested object per object entered, read exactly
the depth-first walk's slots, in its order. The probe's fuel is any. -/
theorem run_reads {root : Nat} {T : List Slot} {S' : List Nat} (D : Dfs g (.visit root) [] T S')
    (qfuel fuel : Nat) (hfuel : S'.length ≤ fuel) : (run g o qfuel fuel root).reads = T := by
  have hnd : T.Nodup := D.nodup (fun _ _ _ h => by cases h)
  have hq := question_probe (o := o) (qfuel := qfuel) D initial [] [] rfl (by simpa using hnd)
    (by simp) (by intro n hn; simp at hn) (by simp) (by intro n h; simp [initial] at h)
    (by simp [initial]) rfl
  obtain ⟨hqm, hqv⟩ := question_mono (g := g) (o := o) qfuel initial root
  have hqo := question_ok (g := g) (o := o) qfuel initial root (by intro n h; simp [initial] at h)
  obtain ⟨t, h₁, h₂, -⟩ := hq
  have h := resume (o := o) (qfuel := qfuel) D fuel (question g o qfuel initial root).2 [] t [] h₂
    (by simpa using h₁) (by simpa using hnd) (by simp) (by intro n hn; simp at hn) (by simp) hqo
    (by intro d hd; rw [hqm.done] at hd; simp [initial] at hd)
    (by intro d hd; rw [hqm.records] at hd; simp [initial] at hd)
    (by intro d hd; rw [hqm.done] at hd; simp [initial] at hd) hqv (by simpa using hfuel) trivial
  simpa [run] using h.1

/-- Each getter of a reachable object runs once, after the recipe, in depth-first order: the
getter slots `produce` reads for the first time, which is when a getter runs, are the depth-first
walk's getter slots in its order, with no repeats, and include every getter of every reachable
object. -/
theorem getters_once {root : Nat} {T : List Slot} {S' : List Nat}
    (D : Dfs g (.visit root) [] T S') (getter : Slot → Bool) (qfuel fuel : Nat)
    (hfuel : S'.length ≤ fuel) :
    (run g o qfuel fuel root).reads.filter getter = T.filter getter ∧
      ((run g o qfuel fuel root).reads.filter getter).Nodup ∧
      ∀ n k, Reach g root n → k < (g n).length → getter (n, k) = true →
        (n, k) ∈ (run g o qfuel fuel root).reads.filter getter := by
  rw [run_reads D qfuel fuel hfuel]
  refine ⟨rfl, (D.nodup (fun _ _ _ h => by cases h)).filter _, fun n k hr hk hgt => ?_⟩
  exact List.mem_filter.mpr ⟨(D.slots_iff (n, k)).mpr ⟨hr, hk⟩, hgt⟩

/-- The objects of `U` not yet seen. -/
def unseen (U S : List Nat) : List Nat := U.filter (fun x => decide (x ∉ S))

theorem filter_length_mono {p q : Nat → Bool} (h : ∀ x, p x = true → q x = true) (l : List Nat) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons]
    by_cases hp : p x = true
    · rw [if_pos hp, if_pos (h x hp)]; simp only [List.length_cons]; omega
    · rw [if_neg hp]; split <;> (try simp only [List.length_cons]) <;> omega

theorem filter_length_lt {p q : Nat → Bool} (h : ∀ x, p x = true → q x = true) {l : List Nat}
    {y : Nat} (hy : y ∈ l) (hq : q y = true) (hp : p y = false) :
    (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => simp at hy
  | cons x xs ih =>
    simp only [List.filter_cons]
    rcases List.mem_cons.mp hy with rfl | hy'
    · rw [if_neg (by simp [hp]), if_pos hq]; simp only [List.length_cons]
      exact Nat.lt_succ_of_le (filter_length_mono h xs)
    · have := ih hy'
      by_cases hpx : p x = true
      · rw [if_pos hpx, if_pos (h x hpx)]; simp only [List.length_cons]; omega
      · rw [if_neg hpx]; split <;> (try simp only [List.length_cons]) <;> omega

theorem unseen_mono {U S S' : List Nat} (h : ∀ x ∈ S, x ∈ S') :
    (unseen U S').length ≤ (unseen U S).length :=
  filter_length_mono (fun x hx => by
    simp only [decide_eq_true_eq] at hx ⊢; exact fun h' => hx (h x h')) U

theorem unseen_lt {U S : List Nat} {n : Nat} (hn : n ∈ U) (hS : n ∉ S) :
    (unseen U (n :: S)).length < (unseen U S).length :=
  filter_length_lt (fun x hx => by
    simp only [decide_eq_true_eq, List.mem_cons, not_or] at hx ⊢; exact hx.2) hn (by simp [hS])
    (by simp)

/-- On a finite graph, the walk from any object exists: every object reachable lies in a list
`U` closed under children. -/
theorem Dfs.exists {U : List Nat} (hU : ∀ n ∈ U, ∀ c ∈ g n, c ∈ U) :
    ∀ k (S : List Nat), (unseen U S).length ≤ k → (∀ m ∈ S, m ∈ U) →
      (∀ n, n ∈ U → ∃ T S', Dfs g (.visit n) S T S' ∧ ∀ m ∈ S', m ∈ U) ∧
      (∀ n i (cs : List Nat), (∀ c ∈ cs, c ∈ U) → ∃ T S', Dfs g (.resume n i cs) S T S' ∧ ∀ m ∈ S', m ∈ U) := by
  intro k
  induction k with
  | zero =>
    intro S hk hS
    have hall : ∀ n ∈ U, n ∈ S := by
      intro n hn
      by_cases h : n ∈ S
      · exact h
      · exfalso
        have : n ∈ unseen U S := List.mem_filter.mpr ⟨hn, by simp [h]⟩
        have := List.length_pos_of_mem this
        omega
    have visit : ∀ n, n ∈ U → ∃ T S', Dfs g (.visit n) S T S' ∧ ∀ m ∈ S', m ∈ U :=
      fun n hn => ⟨[], S, .seen (hall n hn), hS⟩
    refine ⟨visit, fun n i cs hcs => ?_⟩
    induction cs generalizing i with
    | nil => exact ⟨[], S, .nil, hS⟩
    | cons c cs ih =>
      obtain ⟨T₂, S₂, D₂, h₂⟩ := ih (i + 1) (fun c' h => hcs c' (List.mem_cons_of_mem _ h))
      exact ⟨(n, i) :: ([] ++ T₂), S₂, .cons (.seen (hall c (hcs c (List.mem_cons_self ..)))) D₂, h₂⟩
  | succ k ih =>
    intro S hk hS
    -- Resumed frames, from any seen list with as few unseen objects, given visits.
    have resumeFrom : ∀ (cs : List Nat) (S₀ : List Nat) n i, (unseen U S₀).length ≤ k + 1 →
        (∀ m ∈ S₀, m ∈ U) → (∀ c ∈ cs, c ∈ U) →
        (∀ S₁ : List Nat, (unseen U S₁).length ≤ k + 1 → (∀ m ∈ S₁, m ∈ U) →
          ∀ c ∈ U, ∃ T S', Dfs g (.visit c) S₁ T S' ∧ ∀ m ∈ S', m ∈ U) →
        ∃ T S', Dfs g (.resume n i cs) S₀ T S' ∧ ∀ m ∈ S', m ∈ U := by
      intro cs
      induction cs with
      | nil => intro S₀ n i _ hS₀ _ _; exact ⟨[], S₀, .nil, hS₀⟩
      | cons c cs ihc =>
        intro S₀ n i hk₀ hS₀ hcs hv
        obtain ⟨T₁, S₁, D₁, h₁⟩ := hv S₀ hk₀ hS₀ c (hcs c (List.mem_cons_self ..))
        have hk₁ : (unseen U S₁).length ≤ k + 1 :=
          Nat.le_trans (unseen_mono (fun x hx => D₁.sub hx)) hk₀
        obtain ⟨T₂, S₂, D₂, h₂⟩ := ihc S₁ n (i + 1) hk₁ h₁
          (fun c' h => hcs c' (List.mem_cons_of_mem _ h)) hv
        exact ⟨(n, i) :: (T₁ ++ T₂), S₂, .cons D₁ D₂, h₂⟩
    have visit : ∀ S₁ : List Nat, (unseen U S₁).length ≤ k + 1 → (∀ m ∈ S₁, m ∈ U) →
        ∀ c ∈ U, ∃ T S', Dfs g (.visit c) S₁ T S' ∧ ∀ m ∈ S', m ∈ U := by
      intro S₁ hk₁ hS₁ c hc
      by_cases hcS : c ∈ S₁
      · exact ⟨[], S₁, .seen hcS, hS₁⟩
      · by_cases hgc : g c = []
        · exact ⟨[], S₁, .leaf hgc, hS₁⟩
        · have hlt := unseen_lt hc hcS
          have hk' : (unseen U (c :: S₁)).length ≤ k := by omega
          obtain ⟨-, hres⟩ := ih (c :: S₁) hk' (fun m hm => by
            rcases List.mem_cons.mp hm with rfl | hm
            · exact hc
            · exact hS₁ m hm)
          obtain ⟨T, S', D', h'⟩ := hres c 0 (g c) (fun c' h => hU c hc c' h)
          exact ⟨T, S', .fresh hcS hgc D', h'⟩
    exact ⟨fun n hn => visit S hk hS n hn,
      fun n i cs hcs => resumeFrom cs S n i hk hS hcs visit⟩

/-- On a finite graph, with fuel for as many nested objects as the graph holds, `produce`'s first
reads of the result's slots are the depth-first walk's: they exist, and they are the walk. -/
theorem run_dfs {U : List Nat} (hU : ∀ n ∈ U, ∀ c ∈ g n, c ∈ U) {root : Nat} (hr : root ∈ U)
    (qfuel fuel : Nat) (hfuel : U.length ≤ fuel) :
    ∃ T S', Dfs g (.visit root) [] T S' ∧ (run g o qfuel fuel root).reads = T := by
  obtain ⟨h, -⟩ := Dfs.exists hU (unseen U []).length [] (Nat.le_refl _) (by simp)
  obtain ⟨T, S', D, hS'⟩ := h root hr
  refine ⟨T, S', D, run_reads D qfuel fuel ?_⟩
  obtain ⟨L, hL, hnd, -⟩ := D.extends
  rw [List.append_nil] at hL
  subst hL
  exact Nat.le_trans (List.Subperm.length_le (List.subperm_of_subset hnd hS')) hfuel

end Main

/-! ## The same depth-first walk as `serialize`'s

`Serialization.DFS.Recursive` is the depth-first walk `serialize`'s encoder refines
(`recursive_refines_stack`). Its edge events, read as slots, are this module's walk: the two
differ only in that `Recursive` also marks objects without slots as seen, which reads nothing. -/

section Serialization

variable {g : Graph}

/-- The slots of a trace's edge events. -/
def edges : List SerializationDFS.Event → List Slot
  | [] => []
  | .enter _ :: es => edges es
  | .edge p i _ :: es => (p, i) :: edges es

theorem edges_append (a b : List SerializationDFS.Event) : edges (a ++ b) = edges a ++ edges b := by
  induction a with
  | nil => rfl
  | cons e es ih => cases e <;> simp [edges, ih]

def ofFrame : SerializationDFS.Frame → Frame
  | .visit n => .visit n
  | .resume n i cs => .resume n i cs

theorem Dfs.of_recursive {f : SerializationDFS.Frame} {memo final : List Nat}
    {trace : List SerializationDFS.Event} (h : SerializationDFS.Recursive g f memo trace final) :
    ∀ S : List Nat, (∀ n, g n ≠ [] → (n ∈ memo ↔ n ∈ S)) →
      ∃ S', Dfs g (ofFrame f) S (edges trace) S' ∧ ∀ n, g n ≠ [] → (n ∈ final ↔ n ∈ S') := by
  induction h with
  | @seen node memo hm =>
    intro S hS
    by_cases hg : g node = []
    · exact ⟨S, .leaf hg, hS⟩
    · exact ⟨S, .seen ((hS node hg).mp hm), hS⟩
  | @fresh node memo trace final hm h' ih =>
    intro S hS
    by_cases hg : g node = []
    · rw [hg] at h'
      cases h' with
      | empty => exact ⟨S, by simpa [edges, ofFrame] using Dfs.leaf (S := S) hg, fun n hn => by
          have : n ≠ node := fun h => hn (h ▸ hg)
          simp [this, hS n hn]⟩
    · obtain ⟨S', D, hS'⟩ := ih (node :: S) (fun n hn => by simp [hS n hn])
      exact ⟨S', by simpa [edges, ofFrame] using Dfs.fresh (fun h => hm ((hS node hg).mpr h)) hg D, hS'⟩
  | empty => intro S hS; exact ⟨S, .nil, hS⟩
  | @child parent index node children memo middle final first second _ _ ih₁ ih₂ =>
    intro S hS
    obtain ⟨S₁, D₁, h₁⟩ := ih₁ S hS
    obtain ⟨S₂, D₂, h₂⟩ := ih₂ S₁ h₁
    refine ⟨S₂, ?_, h₂⟩
    simpa [edges, edges_append, ofFrame] using Dfs.cons D₁ D₂

/-- The order `produce` calls getters in is the order of the edge events of the depth-first walk
`Serialization.DFS` models for `serialize`. -/
theorem dfs_eq_serialization {root : Nat} {T : List Slot} {S' final : List Nat}
    {trace : List SerializationDFS.Event} (D : Dfs g (.visit root) [] T S')
    (h : SerializationDFS.Recursive g (.visit root) [] trace final) : T = edges trace := by
  obtain ⟨S'', D', -⟩ := Dfs.of_recursive h [] (by simp)
  exact (Dfs.det D D').1

end Serialization

namespace Example

/-- Object 0 holds 1, 2 and a primitive (3); 1 and 2 share 4, which reaches 5 and back to 0. -/
def graph : Graph := fun n => match n with
  | 0 => [1, 2, 3] | 1 => [4] | 2 => [4, 5] | 4 => [5] | 5 => [0] | _ => []

/-- Object 2 is a written draft. -/
def oracle : Oracle := ⟨fun _ _ => false, fun _ n => n == 2, fun _ _ => false, fun _ _ => false⟩

/-- The probe stops at 2 after reading four slots; discovery reads the rest in depth-first
order. -/
example : (question graph oracle 10 initial 0).2.reads = [(0, 0), (1, 0), (4, 0), (5, 0), (0, 1)] ∧
    (run graph oracle 10 10 0).reads =
      [(0, 0), (1, 0), (4, 0), (5, 0), (0, 1), (2, 0), (2, 1), (0, 2)] := by decide

/-- With fuel for too few nested objects, discovery stops before the walk's end. -/
example : (run graph oracle 10 1 0).reads ≠
    [(0, 0), (1, 0), (4, 0), (5, 0), (0, 1), (2, 0), (2, 1), (0, 2)] := by decide

/-- The probe's answers do not change the order: with every object a written draft, the probe
reads nothing, and discovery reads the same slots in the same order. -/
example : (run graph ⟨fun _ _ => false, fun _ _ => true, fun _ _ => false, fun _ _ => false⟩
    10 10 0).reads = [(0, 0), (1, 0), (4, 0), (5, 0), (0, 1), (2, 0), (2, 1), (0, 2)] := by decide

end Example

end Reconcile.GetterOrder
