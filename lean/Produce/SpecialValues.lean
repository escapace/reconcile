/-!
# Special-value decision

`produce` gives the recipe a writable copy of each `Date`, buffer, view, `URL`, `URLSearchParams`
or Temporal value it reads through a draft, and registers the copy with the value it was made from
(`cloneSpecialValueAfterMiss` in `src/draft-session.ts`). Reading a view copies its buffer first,
or takes the buffer's existing copy, and makes the view's copy over it; reading a URL does the
same with its `searchParams`, so the copies stay linked whichever the recipe reads first. After the
recipe returns, finalization (`src/finalization.ts`) decides, for each such value the result holds,
whether it stays itself, takes its registered copy, goes back to the original a copy was made from,
or gets a fresh copy.

This module models that decision over a finite scenario (`Value`, `Scenario`): the special values
with their kinds and dependencies, what the recipe read and changed, and which values the result
holds. `choose` is `chooseSpecial` (`src/graph/provenance.ts`), `factsWith` is `specialFacts`,
`resolveWith` is `materializeContainerSlot` with `materializeSpecial`, and `depOf` is the
dependency a result object holds. `resolve` reads the sets of the sealed pass, and `outcome` is
its result in closed form.

- Every slot holding a value, from `current` or not, or its copy resolves to `outcome` of that
  value (`resolve_eq_outcome`), so one value has one object in the result (`resolve_shared`).
- A copy the recipe left equal gives back the original (`copy_unchanged`), a changed copy is the
  result's value (`copy_changed`), and a value the recipe did not read stays itself unless its
  dependency's copy changed (`unread_kept`, `fresh_iff`). A Temporal value always stays itself
  (`temporal_kept`).
- Each object the result holds is over the result's object for its dependency: a view over the
  result's buffer and a URL owning the result's `searchParams` (`coherent`). A buffer and its
  views are copied exactly when the buffer's bytes changed (`view_together`), a URL the result
  holds and its `searchParams` exactly when either changed (`url_together`).
- `specialFacts` produces 8 of the 24 combinations of facts (`facts_reachable`,
  `reachable_count`). Each fact `chooseSpecial` reads matters: a decision that ignores one breaks
  one of these promises (`Counterexamples`), and so does a sealed pass that does not force the
  `searchParams` copy of a replaced URL.
- Discovery decides each value before planning it, and its decision is the sealed pass's
  (`first_eq_sealed`); a decision reads the forced copies only at its own value
  (`resolve_reads_own`), and only `searchParams` copies are forced (`ownerForced_params`), so a
  URL decides the same in both passes and discovery forces every copy the sealed pass reads.

The runtime obligation (_Special-value decision_ in the Lean guide):

- **Content equivalence.** `SpecialPolicy.equivalent` compares the contents `differs` names: a
  date's time, a buffer's bytes, a view's shape and its buffer's bytes, a URL's `href`, which
  includes its query, and a `URLSearchParams`' text; a Temporal value's copy is always equal. A
  URL's `dependencyEquivalent` finds its `searchParams` copy equal exactly when its text is
  unchanged, through the carrier every registered `searchParams` copy has.
- **Registration.** A copy exists exactly for a value read through a draft and for the dependency
  of one (`copied`); a view's copy is over its buffer's copy and a URL's copy owns its
  `searchParams`' copy. A view the recipe makes over a buffer's copy is its own value
  (`Value.authored`).
- **Sealed replay.** A planned value is one discovery decided to copy afresh, and a forced copy
  belongs to a URL the result holds and replaces; discovery reaches every such URL, since a URL
  with a copy, or whose `searchParams` has one, makes its region active. Discovery's own decisions
  stand only when it planned and forced nothing, and then they read the empty sets, which are the
  final ones.

The SpecialValues bridge runs `chooseSpecial` on all 24 combinations and `produce` on scenarios
that reach the 8 reachable ones.
-/

namespace Reconcile.SpecialValues

/-- `SpecialFacts.origin`: the value has a registered copy (`base`), is one (`copy`), or
neither. -/
inductive Origin where
  | base
  | copy
  | untracked
  deriving DecidableEq, Repr

/-- `SpecialFacts` in `src/types.ts`. -/
structure Facts where
  origin : Origin
  forced : Bool
  dependenciesStable : Bool
  equivalent : Bool
  deriving DecidableEq, Repr

/-- `SpecialDecision`: the original a copy was made from, the registered copy, a fresh copy or
the value itself. -/
inductive Decision where
  | base
  | copy
  | fresh
  | source
  deriving DecidableEq, Repr

/-- `chooseSpecial`, with `SPECIAL_REPLACEMENT` (`src/constants.ts`) inlined. -/
def choose (f : Facts) : Decision :=
  match f.origin with
  | .copy => if f.equivalent then .base else .source
  | .base => if !f.forced && f.dependenciesStable && f.equivalent then .source else .copy
  | .untracked => if !f.forced && f.dependenciesStable && f.equivalent then .source else .fresh

/-- The special kinds. A view depends on its buffer and a URL on its `searchParams`. -/
inductive Kind where
  | date
  | buffer
  | view
  | url
  | params
  | temporal
  deriving DecidableEq, Repr, Inhabited

/-- One special value and what the recipe did to it. -/
structure Value where
  kind : Kind
  /-- The value its copy depends on: a view's buffer, a URL's `searchParams`. -/
  dep : Option Nat
  /-- A view the recipe made over its dependency's registered copy: not a value of `current`, it
  has no copy of its own. -/
  authored : Bool
  /-- The recipe read the value through a draft. -/
  read : Bool
  /-- The recipe left the copy's own content different: a date's time, a buffer's bytes, a
  `URLSearchParams`' text, or a URL's `href` outside its query. -/
  edit : Bool
  deriving DecidableEq, Repr

/-- Past the end of a scenario every value is an unread date. -/
instance : Inhabited Value := ⟨⟨.date, none, false, false, false⟩⟩

/-- The special values, by index. -/
abbrev Scenario := List Value

/-- What a slot of the result holds: the value itself, or its registered copy. -/
inductive Ref where
  | value (i : Nat)
  | copy (i : Nat)
  deriving DecidableEq, Repr

/-- What the result holds: a value itself, its registered copy, or a fresh copy of it. -/
inductive Obj where
  | value (i : Nat)
  | copy (i : Nat)
  | fresh (i : Nat)
  deriving DecidableEq, Repr

section

variable (s : Scenario)

/-- The value at index `i`. -/
def val (i : Nat) : Value := s.getD i default

/-- A registered copy exists: the recipe read the value, or read a value that depends on it. -/
def copied (i : Nat) : Bool :=
  !(val s i).authored &&
    ((val s i).read || (List.range s.length).any fun j =>
      (val s j).read && !(val s j).authored && (val s j).dep == some i)

/-- Whether the dependency's own content changed. -/
def depEdit (i : Nat) : Bool :=
  match (val s i).dep with
  | some d => (val s d).edit
  | none => false

/-- Whether a registered copy compares unequal to its value under `SpecialPolicy.equivalent`: a
view by its buffer's bytes, a URL by its `href`, which includes its query, a Temporal value never,
the others by their own content. -/
def differs (i : Nat) : Bool :=
  match (val s i).kind with
  | .view => depEdit s i
  | .url => (val s i).edit || depEdit s i
  | .temporal => false
  | _ => (val s i).edit

/-- The comparison `stableSpecialDependencies` makes for the dependency: a dependency that is a
registered copy agrees when finalization keeps that copy, which for a buffer is when it changed;
any other agrees when it has no copy or its copy is equal. -/
def agrees (i : Nat) : Bool :=
  match (val s i).dep with
  | none => true
  | some d => if (val s i).authored then differs s d else !copied s d || !differs s d

/-- `untrackedSpecialsToClone` as the sealed pass reads it: a value without a copy whose dependency
does not agree, which discovery copied afresh. -/
def planned (i : Nat) : Bool := !copied s i && !agrees s i

/-- `stableSpecialDependencies`: the dependency is not planned for a fresh copy, unless it is a
registered copy, which is never planned, and it agrees. -/
def stable (i : Nat) : Bool :=
  agrees s i && match (val s i).dep with
    | some d => (val s i).authored || !planned s d
    | none => true

/-- A URL the result holds is replaced: its copy differs, or, unread, its dependency does not
stay. -/
def replaced (u : Nat) : Bool := if copied s u then differs s u else !stable s u

/-- `forcedOwnedCopies` as the sealed pass reads it: the registered copy of a `searchParams` whose
URL the result holds (`held`) and replaces. -/
def ownerForced (held : Nat → Bool) (p : Nat) : Bool :=
  copied s p && (List.range s.length).any fun u =>
    held u && (val s u).kind == .url && (val s u).dep == some p && replaced s u

/-- `specialFacts`, given the values planned for a fresh copy (`untrackedSpecialsToClone`) and
the forced copies (`forcedOwnedCopies`): a copy compares with its value unless it is forced; a
planned value is `forced`, and then neither its dependency nor its copy is compared. -/
def factsWith (plan owned : Nat → Bool) : Ref → Facts
  | .copy i => ⟨.copy, false, true, !owned i && !differs s i⟩
  | .value i =>
    let forced := plan i
    let stable := forced || stable s i
    ⟨if copied s i then .base else .untracked, forced, stable,
      !copied s i || forced || !stable || !differs s i⟩

/-- `materializeSpecial` on a registered copy, for a decision function `c`: `base` gives back the
value it was made from; otherwise it is `source` and the copy stays. -/
def ofCopyWith (c : Facts → Decision) (plan owned : Nat → Bool) (i : Nat) : Obj :=
  match c (factsWith s plan owned (.copy i)) with
  | .base => .value i
  | _ => .copy i

/-- `materializeSpecial` on a value that is not a copy: `copy` resolves the registered copy, as
`materializeContainerSlot(copy, false)`; `fresh` makes a fresh copy; otherwise it stays. -/
def ofValueWith (c : Facts → Decision) (plan owned : Nat → Bool) (i : Nat) : Obj :=
  match c (factsWith s plan owned (.value i)) with
  | .copy => ofCopyWith s c plan owned i
  | .fresh => .fresh i
  | _ => .value i

/-- `materializeContainerSlot` on a special value: a value with a copy, in a slot that is not
current-backed or whose copy is forced, resolves its copy instead. -/
def resolveWith (c : Facts → Decision) (plan owned : Nat → Bool) : Ref → Bool → Obj
  | .copy i, _ => ofCopyWith s c plan owned i
  | .value i, backed =>
    if copied s i && (!backed || owned i) then ofCopyWith s c plan owned i
    else ofValueWith s c plan owned i

/-- The facts the sealed pass reads, when the result holds the URLs `held`. -/
def factsOf (held : Nat → Bool) : Ref → Facts := factsWith s (planned s) (ownerForced s held)

/-- The runtime's resolution, with the sets the sealed pass reads. -/
def resolve (held : Nat → Bool) : Ref → Bool → Obj :=
  resolveWith s choose (planned s) (ownerForced s held)

/-- The dependency a result object holds: a value its own (a view the recipe made holds the
buffer's copy), a copy the copy of its dependency, and a fresh copy the dependency as finalization
resolves it from a slot that is not current-backed. -/
def depOf (held : Nat → Bool) : Obj → Option Obj
  | .value i => (val s i).dep.map fun d => if (val s i).authored then .copy d else .value d
  | .copy i => (val s i).dep.map .copy
  | .fresh i => (val s i).dep.map fun d =>
      resolve s held (if (val s i).authored then .copy d else .value d) false

/-- The decision in closed form. -/
def outcome (held : Nat → Bool) (i : Nat) : Obj :=
  if copied s i then (if differs s i || ownerForced s held i then .copy i else .value i)
  else if stable s i then .value i else .fresh i

/-- The value a reference names. -/
def Ref.index : Ref → Nat
  | .value i => i
  | .copy i => i

end

theorem stable_agrees (s : Scenario) (i : Nat) (h : stable s i = true) : agrees s i = true := by
  simp only [stable, Bool.and_eq_true] at h
  exact h.1

/-- Every slot resolves to `outcome` of its value. A copy exists only for a copied value. -/
theorem resolve_eq_outcome (s : Scenario) (held : Nat → Bool) (r : Ref) (backed : Bool)
    (hr : ∀ i, r = .copy i → copied s i = true) :
    resolve s held r backed = outcome s held r.index := by
  cases r with
  | copy i =>
    have hc := hr i rfl
    simp only [resolve, resolveWith, ofCopyWith, factsWith, choose, outcome, hc, Ref.index,
      if_true]
    rcases Bool.eq_false_or_eq_true (differs s i) with hd | hd <;>
      rcases Bool.eq_false_or_eq_true (ownerForced s held i) with hf | hf <;> simp [hd, hf]
  | value i =>
    have hsa := stable_agrees s i
    simp only [resolve, Ref.index, outcome]
    cases hc : copied s i <;> cases hb : backed <;> cases hf : ownerForced s held i <;>
      cases hd : differs s i <;> cases ha : agrees s i <;> cases hs : stable s i <;>
      simp_all [resolveWith, ofValueWith, ofCopyWith, factsWith, choose, planned]

/-- Whether a slot is current-backed does not change what it resolves to, and a value and its copy
resolve to the same object. -/
theorem resolve_shared (s : Scenario) (held : Nat → Bool) (i : Nat) (backed : Bool)
    (hc : copied s i = true) :
    resolve s held (.value i) backed = resolve s held (.copy i) false := by
  rw [resolve_eq_outcome s held _ backed (by simp), resolve_eq_outcome s held _ false
    (by intro j h; cases h; exact hc)]
  rfl

/-- A copy the recipe left equal gives back the original. -/
theorem copy_unchanged (s : Scenario) (held : Nat → Bool) (i : Nat) (hc : copied s i = true)
    (hd : differs s i = false) (hf : ownerForced s held i = false) :
    outcome s held i = .value i := by
  simp [outcome, hc, hd, hf]

/-- A changed copy is the result's value. -/
theorem copy_changed (s : Scenario) (held : Nat → Bool) (i : Nat) (hc : copied s i = true)
    (hd : differs s i = true) : outcome s held i = .copy i := by
  simp [outcome, hc, hd]

/-- A value without a copy stays itself when its dependency stays. -/
theorem unread_kept (s : Scenario) (held : Nat → Bool) (i : Nat) (hc : copied s i = false)
    (hs : stable s i = true) : outcome s held i = .value i := by
  simp [outcome, hc, hs]

/-- Only a value without a copy whose dependency does not stay gets a fresh copy. -/
theorem fresh_iff (s : Scenario) (held : Nat → Bool) (i : Nat) :
    outcome s held i = .fresh i ↔ copied s i = false ∧ stable s i = false := by
  unfold outcome
  cases copied s i <;> cases differs s i <;> cases ownerForced s held i <;> cases stable s i <;>
    simp

/-- The fact combinations `specialFacts` can produce: a copy is never forced and its dependencies
are not compared; a value with a copy is never forced, and is compared only when its dependencies
are stable; a value without a copy is equivalent, and stable when forced. -/
def Reachable (f : Facts) : Bool :=
  match f.origin with
  | .copy => !f.forced && f.dependenciesStable
  | .base => !f.forced && (f.dependenciesStable || f.equivalent)
  | .untracked => f.equivalent && (!f.forced || f.dependenciesStable)

/-- Discovery's first decisions (nothing planned) and the sealed pass's (`planned`) read only
reachable facts, whatever copies are forced. -/
theorem facts_reachable (s : Scenario) (plan owned : Nat → Bool)
    (hplan : ∀ i, plan i = true → copied s i = false) (r : Ref) :
    Reachable (factsWith s plan owned r) = true := by
  cases r with
  | copy i => simp [factsWith, Reachable]
  | value i =>
    have hp := hplan i
    cases hc : copied s i <;> cases hq : plan i <;> cases hs : stable s i <;>
      cases hd : differs s i <;>
      simp_all [factsWith, Reachable]

/-- Eight of the 24 combinations are reachable. -/
theorem reachable_count :
    ([Origin.base, .copy, .untracked].flatMap fun o => [false, true].flatMap fun a =>
      [false, true].flatMap fun b => [false, true].map fun c =>
        (⟨o, a, b, c⟩ : Facts)).countP (Reachable ·) = 8 := by decide

/-- Discovery decides a value before planning it: with nothing planned, the decision is the one
the sealed pass makes reading the value as `forced` when discovery planned it. -/
theorem first_eq_sealed (s : Scenario) (owned : Nat → Bool) (r : Ref) (backed : Bool) :
    resolveWith s choose (fun _ => false) owned r backed =
      resolveWith s choose (planned s) owned r backed := by
  have hsa := stable_agrees s r.index
  cases r with
  | copy i => rfl
  | value i =>
    simp only [Ref.index] at hsa
    cases hc : copied s i <;> cases hb : backed <;> cases hf : owned i <;>
      cases hd : differs s i <;> cases ha : agrees s i <;> cases hs : stable s i <;>
      simp_all [resolveWith, ofValueWith, ofCopyWith, factsWith, choose, planned]

/-- A decision reads the forced copies only at its own value. Only a `searchParams` copy is ever
forced (`ownerForced_params`), so a URL's decision is the same in discovery and in the sealed
pass. -/
theorem resolve_reads_own (s : Scenario) (c : Facts → Decision) (plan owned owned' : Nat → Bool)
    (r : Ref) (backed : Bool) (h : owned r.index = owned' r.index) :
    resolveWith s c plan owned r backed = resolveWith s c plan owned' r backed := by
  cases r <;> simp_all [resolveWith, ofValueWith, ofCopyWith, factsWith, Ref.index]

/-- The scenarios the runtime produces: a view depends on a buffer and a URL on a
`searchParams`, neither of which depends on anything or is made by the recipe; nothing else has a
dependency; a value the recipe made is a view over a buffer that has a copy; an edit needs a copy;
and one `searchParams` belongs to one URL. -/
structure WF (s : Scenario) : Prop where
  dep_kind : ∀ i d, (val s i).dep = some d →
    ((val s i).kind = .view ∧ (val s d).kind = .buffer) ∨
      ((val s i).kind = .url ∧ (val s d).kind = .params)
  dep_leaf : ∀ i d, (val s i).dep = some d → (val s d).dep = none ∧ (val s d).authored = false
  authored : ∀ i, (val s i).authored = true →
    (val s i).kind = .view ∧ ∃ d, (val s i).dep = some d ∧ copied s d = true
  edit_copied : ∀ i, (val s i).edit = true → copied s i = true
  owner : ∀ u v p, (val s u).kind = .url → (val s v).kind = .url → (val s u).dep = some p →
    (val s v).dep = some p → u = v

/-- `WF` as a finite check over the scenario's indices; past its end every value is a date with
no dependency. -/
def check (s : Scenario) : Bool :=
  (List.range s.length).all fun i =>
    (match (val s i).dep with
      | none => true
      | some d =>
        (((val s i).kind == .view && (val s d).kind == .buffer) ||
            ((val s i).kind == .url && (val s d).kind == .params)) &&
          (val s d).dep == none && !(val s d).authored) &&
    (!(val s i).authored ||
      ((val s i).kind == .view && match (val s i).dep with
        | some d => copied s d
        | none => false)) &&
    (!(val s i).edit || copied s i) &&
    (List.range s.length).all fun j =>
      !((val s i).kind == .url && (val s j).kind == .url && (val s i).dep != none &&
        (val s i).dep == (val s j).dep) || i == j

theorem val_of_ge {s : Scenario} {i : Nat} (h : s.length ≤ i) :
    val s i = ⟨.date, none, false, false, false⟩ := by
  simp only [val, List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]
  rfl

theorem check_sound {s : Scenario} (h : check s = true) : WF s := by
  have hall : ∀ i, i < s.length → _ := fun i hi => List.all_eq_true.mp h i (List.mem_range.mpr hi)
  have range : ∀ i, (val s i).dep ≠ none ∨ (val s i).authored = true ∨ (val s i).edit = true ∨
      (val s i).kind = .url → i < s.length := by
    intro i hi
    apply Nat.lt_of_not_le
    intro hle
    rw [val_of_ge hle] at hi
    simp at hi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i d hd
    have hi := hall i (range i (Or.inl (by simp [hd])))
    simp only [hd, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hi
    exact hi.1.1.1.1.1
  · intro i d hd
    have hi := hall i (range i (Or.inl (by simp [hd])))
    simp only [hd, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hi
    exact ⟨hi.1.1.1.1.2, hi.1.1.1.2⟩
  · intro i ha
    have hi := hall i (range i (Or.inr (Or.inl ha)))
    simp only [ha, Bool.and_eq_true, Bool.not_true, Bool.false_or, beq_iff_eq] at hi
    obtain ⟨⟨⟨_, hk, hdep⟩, _⟩, _⟩ := hi
    refine ⟨hk, ?_⟩
    cases hd : (val s i).dep with
    | none => rw [hd] at hdep; cases hdep
    | some d => rw [hd] at hdep; exact ⟨d, rfl, hdep⟩
  · intro i he
    have hi := hall i (range i (Or.inr (Or.inr (Or.inl he))))
    simp only [he, Bool.and_eq_true, Bool.not_true, Bool.false_or] at hi
    exact hi.1.2
  · intro u v p hu hv hdu hdv
    have hi := hall u (range u (Or.inr (Or.inr (Or.inr hu))))
    simp only [Bool.and_eq_true] at hi
    have hj := List.all_eq_true.mp hi.2 v (List.mem_range.mpr (range v (Or.inr (Or.inr (Or.inr hv)))))
    simpa [hu, hv, hdu, hdv] using hj

section Lemmas

variable {s : Scenario}

theorem lt_of_dep {i d : Nat} (h : (val s i).dep = some d) : i < s.length := by
  apply Nat.lt_of_not_le
  intro hle
  rw [val_of_ge hle] at h
  cases h

/-- A value with a dependency is copied only because it was read, and its dependency then is
copied too. -/
theorem copied_dep (hs : WF s) {i d : Nat} (hd : (val s i).dep = some d)
    (hc : copied s i = true) : copied s d = true ∧ (val s i).read = true ∧
      (val s i).authored = false := by
  have hleaf := hs.dep_leaf i d hd
  simp only [copied, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, List.any_eq_true,
    List.mem_range, beq_iff_eq] at hc
  obtain ⟨ha, hr | ⟨j, _, hj⟩⟩ := hc
  · refine ⟨?_, hr, ha⟩
    simp only [copied, hleaf.2, Bool.not_false, Bool.true_and, Bool.or_eq_true,
      List.any_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq]
    exact Or.inr ⟨i, lt_of_dep hd, ⟨hr, ha⟩, hd⟩
  · exact absurd (hs.dep_leaf j i hj.2).1 (by rw [hd]; simp)

/-- Only a `searchParams` copy is owner-forced. -/
theorem ownerForced_params (hs : WF s) {held : Nat → Bool} {p : Nat}
    (h : ownerForced s held p = true) : (val s p).kind = .params := by
  simp only [ownerForced, Bool.and_eq_true, List.any_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨_, u, _, ⟨⟨_, hk⟩, hd⟩, _⟩ := h
  rcases hs.dep_kind u p hd with h | h
  · rw [h.1] at hk; cases hk
  · exact h.2

/-- A dependency is never planned for a fresh copy. -/
theorem planned_dep (hs : WF s) {i d : Nat} (hd : (val s i).dep = some d) :
    planned s d = false := by
  simp [planned, agrees, (hs.dep_leaf i d hd).1]

/-- A value without a dependency stays unless its copy changed or is owner-forced. -/
theorem outcome_leaf (held : Nat → Bool) {i : Nat} (hd : (val s i).dep = none) :
    outcome s held i =
      if copied s i && (differs s i || ownerForced s held i) then .copy i else .value i := by
  simp only [outcome, stable, agrees, hd, Bool.and_true]
  cases copied s i <;> simp

/-- A copy other than a `searchParams` copy is never forced. -/
theorem ownerForced_of_kind (hs : WF s) {held : Nat → Bool} {p : Nat}
    (hk : (val s p).kind ≠ .params) : ownerForced s held p = false := by
  cases h : ownerForced s held p
  · rfl
  · exact absurd (ownerForced_params hs h) hk

/-- The `searchParams` copy of a URL the result holds is forced exactly when the URL is
replaced. -/
theorem ownerForced_owner (hs : WF s) {held : Nat → Bool} {u p : Nat}
    (hk : (val s u).kind = .url) (hd : (val s u).dep = some p) (hh : held u = true) :
    ownerForced s held p = (copied s p && replaced s u) := by
  cases hr : replaced s u
  · cases h : ownerForced s held p
    · simp
    · exfalso
      simp only [ownerForced, Bool.and_eq_true, List.any_eq_true, List.mem_range,
        beq_iff_eq] at h
      obtain ⟨_, v, _, ⟨⟨_, hkv⟩, hdv⟩, hr'⟩ := h
      have hv : v = u := hs.owner v u p (by simpa using hkv) hk hdv hd
      subst hv
      rw [hr] at hr'
      cases hr'
  · cases hcp : copied s p
    · simp [ownerForced, hcp]
    · simp only [ownerForced, hcp, Bool.true_and, Bool.and_true, List.any_eq_true,
        List.mem_range, Bool.and_eq_true, beq_iff_eq]
      exact ⟨u, lt_of_dep hd, ⟨⟨hh, by simp [hk]⟩, hd⟩, hr⟩

end Lemmas

/-- Each object the result holds is over the result's object for its dependency: a view over the
result's buffer, a URL owning the result's `searchParams`. A URL needs to be held for its
`searchParams` copy to be forced. -/
theorem coherent (s : Scenario) (hs : WF s) (held : Nat → Bool) (i : Nat) (hh : held i = true) :
    depOf s held (outcome s held i) = (val s i).dep.map (outcome s held) := by
  cases hd : (val s i).dep with
  | none =>
    unfold outcome
    split <;> (try split) <;> simp [depOf, hd]
  | some d =>
    have hleaf := hs.dep_leaf i d hd
    have hpd := planned_dep hs hd
    show depOf s held (outcome s held i) = some (outcome s held d)
    -- A fresh copy is over the dependency's resolution.
    have hfresh : (val s i).authored = true → copied s d = true →
        depOf s held (.fresh i) = some (outcome s held d) := by
      intro ha hcd
      simp only [depOf, hd, ha, if_true, Option.map_some]
      rw [resolve_eq_outcome s held (.copy d) false (by intro j h; cases h; exact hcd)]
      rfl
    have hfresh' : (val s i).authored = false → depOf s held (.fresh i) = some (outcome s held d) := by
      intro ha
      simp only [depOf, hd, ha, Bool.false_eq_true, if_false, Option.map_some]
      rw [resolve_eq_outcome s held (.value d) false (by simp)]
      rfl
    rw [outcome_leaf held hleaf.1]
    have hdd : differs s d = (val s d).edit := by
      rcases hs.dep_kind i d hd with h | h <;> simp [differs, h.2]
    have hdi : depEdit s i = (val s d).edit := by simp [depEdit, hd]
    cases ha : (val s i).authored
    · have hst : stable s i = (!copied s d || !(val s d).edit) := by
        simp [stable, agrees, hd, ha, hpd, hdd]
      rcases hs.dep_kind i d hd with ⟨hk, hkd⟩ | ⟨hk, hkd⟩
      · -- A view: copied exactly when its buffer's bytes changed.
        have hfd : ownerForced s held d = false := ownerForced_of_kind hs (by rw [hkd]; decide)
        have hfi : ownerForced s held i = false := ownerForced_of_kind hs (by rw [hk]; decide)
        have hdv : differs s i = (val s d).edit := by simp [differs, hk, hdi]
        cases hc : copied s i
        · cases hs' : stable s i
          · have ho : outcome s held i = .fresh i := by simp [outcome, hc, hs']
            rw [ho, hfresh' ha, outcome_leaf held hleaf.1]
          · have ho : outcome s held i = .value i := by simp [outcome, hc, hs']
            rw [ho, hdd, hfd]
            rw [hst] at hs'
            cases hcd : copied s d <;> cases he : (val s d).edit <;> simp_all [depOf]
        · obtain ⟨hcd, _, _⟩ := copied_dep hs hd hc
          have ho : outcome s held i = if (val s d).edit then .copy i else .value i := by
            simp [outcome, hc, hdv, hfi]
          rw [ho, hdd, hfd, hcd]
          cases (val s d).edit <;> simp [depOf, hd, ha]
      · -- A URL: a replaced one forces its `searchParams` copy.
        have hfd := ownerForced_owner hs hk hd hh
        have hfi : ownerForced s held i = false := ownerForced_of_kind hs (by rw [hk]; decide)
        have hdu : differs s i = ((val s i).edit || (val s d).edit) := by
          simp [differs, hk, hdi]
        cases hc : copied s i
        · have hr : replaced s i = !stable s i := by simp [replaced, hc]
          rw [hfd, hr]
          cases hs' : stable s i
          · have ho : outcome s held i = .fresh i := by simp [outcome, hc, hs']
            rw [ho, hfresh' ha, outcome_leaf held hleaf.1, hfd, hr, hs']
          · have ho : outcome s held i = .value i := by simp [outcome, hc, hs']
            rw [ho, hdd]
            rw [hst] at hs'
            cases hcd : copied s d <;> cases he : (val s d).edit <;> simp_all [depOf]
        · obtain ⟨hcd, _, _⟩ := copied_dep hs hd hc
          have hr : replaced s i = differs s i := by simp [replaced, hc]
          have ho : outcome s held i = if differs s i then .copy i else .value i := by
            simp [outcome, hc, hfi]
          rw [ho, hfd, hr, hdd, hcd, hdu]
          cases (val s i).edit <;> cases (val s d).edit <;> simp [depOf, hd, ha]
    · -- A view the recipe made over its buffer's copy: it stays exactly when that copy changed.
      obtain ⟨hk, d', hd', hcd⟩ := hs.authored i ha
      rw [hd] at hd'
      cases hd'
      have hkd : (val s d).kind = .buffer := by
        rcases hs.dep_kind i d hd with h | h
        · exact h.2
        · rw [hk] at h; cases h.1
      have hfd : ownerForced s held d = false := ownerForced_of_kind hs (by rw [hkd]; decide)
      have hnc : copied s i = false := by simp [copied, ha]
      have hst : stable s i = (val s d).edit := by simp [stable, agrees, hd, ha, hdd]
      cases he : (val s d).edit
      · have ho : outcome s held i = .fresh i := by simp [outcome, hnc, hst, he]
        rw [ho, hfresh ha hcd, outcome_leaf held hleaf.1]
      · have ho : outcome s held i = .value i := by simp [outcome, hnc, hst, he]
        rw [ho, hdd, hfd, hcd, he]
        simp [depOf, hd, ha]

/-- A buffer and its views are copied together, exactly when the buffer's bytes changed. -/
theorem view_together (s : Scenario) (hs : WF s) (held : Nat → Bool) (v b : Nat)
    (hd : (val s v).dep = some b) (hk : (val s v).kind = .view) (ha : (val s v).authored = false) :
    (outcome s held v ≠ .value v ↔ (val s b).edit = true) ∧
      (outcome s held b ≠ .value b ↔ (val s b).edit = true) := by
  have hkd : (val s b).kind = .buffer := by
    rcases hs.dep_kind v b hd with h | h
    · exact h.2
    · rw [hk] at h; cases h.1
  have hfb : ownerForced s held b = false := by
    cases h : ownerForced s held b
    · rfl
    · have := ownerForced_params hs h; rw [hkd] at this; cases this
  have hfv : ownerForced s held v = false := by
    cases h : ownerForced s held v
    · rfl
    · have := ownerForced_params hs h; rw [hk] at this; cases this
  have hdb : differs s b = (val s b).edit := by simp [differs, hkd]
  have hdv : differs s v = (val s b).edit := by simp [differs, hk, depEdit, hd]
  have hb := outcome_leaf (s := s) held (hs.dep_leaf v b hd).1
  rw [hdb, hfb] at hb
  have hpb := planned_dep hs hd
  constructor
  · unfold outcome
    rw [hdv, hfv]
    cases hcv : copied s v
    · have hst : stable s v = !(copied s b && (val s b).edit) := by
        simp [stable, agrees, hd, ha, hpb, hdb]
      rw [hst]
      cases hcb : copied s b
      · have he : (val s b).edit = false := by
          cases h : (val s b).edit
          · rfl
          · rw [hs.edit_copied b h] at hcb; cases hcb
        simp [he]
      · cases (val s b).edit <;> simp
    · cases (val s b).edit <;> simp
  · rw [hb]
    cases hcb : copied s b
    · have he : (val s b).edit = false := by
        cases h : (val s b).edit
        · rfl
        · rw [hs.edit_copied b h] at hcb; cases hcb
      simp [he]
    · cases (val s b).edit <;> simp

/-- A URL the result holds and its `searchParams` are copied together, exactly when either
changed. -/
theorem url_together (s : Scenario) (hs : WF s) (held : Nat → Bool) (u p : Nat)
    (hd : (val s u).dep = some p) (hk : (val s u).kind = .url) (hh : held u = true) :
    (outcome s held u ≠ .value u ↔ ((val s u).edit || (val s p).edit) = true) ∧
      (outcome s held p ≠ .value p ↔ ((val s u).edit || (val s p).edit) = true) := by
  have ha : (val s u).authored = false := by
    cases h : (val s u).authored
    · rfl
    · rw [(hs.authored u h).1] at hk; cases hk
  have hkd : (val s p).kind = .params := by
    rcases hs.dep_kind u p hd with h | h
    · rw [hk] at h; cases h.1
    · exact h.2
  have hfu : ownerForced s held u = false := by
    cases h : ownerForced s held u
    · rfl
    · have := ownerForced_params hs h; rw [hk] at this; cases this
  have hdp : differs s p = (val s p).edit := by simp [differs, hkd]
  have hdu : differs s u = ((val s u).edit || (val s p).edit) := by
    simp [differs, hk, depEdit, hd]
  have hpp := planned_dep hs hd
  have hst : stable s u = !(copied s p && (val s p).edit) := by
    simp [stable, agrees, hd, ha, hpp, hdp]
  have heu : (val s u).edit = true → copied s u = true := hs.edit_copied u
  have hep : (val s p).edit = true → copied s p = true := hs.edit_copied p
  -- The URL is replaced exactly when either changed.
  have hrep : replaced s u = ((val s u).edit || (val s p).edit) := by
    unfold replaced
    rw [hdu, hst]
    cases hcu : copied s u
    · have : (val s u).edit = false := by
        cases h : (val s u).edit
        · rfl
        · rw [heu h] at hcu; cases hcu
      cases hcp : copied s p
      · have : (val s p).edit = false := by
          cases h : (val s p).edit
          · rfl
          · rw [hep h] at hcp; cases hcp
        simp [*]
      · simp [*]
    · rfl
  have hfp : ownerForced s held p = (copied s p && ((val s u).edit || (val s p).edit)) := by
    cases hr : ((val s u).edit || (val s p).edit)
    · cases h : ownerForced s held p
      · simp
      · exfalso
        simp only [ownerForced, Bool.and_eq_true, List.any_eq_true, List.mem_range,
          beq_iff_eq] at h
        obtain ⟨_, v, _, ⟨⟨_, hkv⟩, hdv⟩, hr'⟩ := h
        have hv : v = u := hs.owner v u p (by simpa using hkv) hk hdv hd
        subst hv
        rw [hrep, hr] at hr'
        cases hr'
    · cases hcp : copied s p
      · simp [ownerForced, hcp]
      · simp only [ownerForced, hcp, Bool.true_and, List.any_eq_true, List.mem_range,
          Bool.and_eq_true, beq_iff_eq]
        exact ⟨u, lt_of_dep hd, ⟨⟨hh, by simp [hk]⟩, hd⟩, by rw [hrep, hr]⟩
  have hb := outcome_leaf (s := s) held (hs.dep_leaf u p hd).1
  constructor
  · unfold outcome
    rw [hdu, hfu, hst]
    cases hcu : copied s u
    · have : (val s u).edit = false := by
        cases h : (val s u).edit
        · rfl
        · rw [heu h] at hcu; cases hcu
      cases hcp : copied s p
      · have : (val s p).edit = false := by
          cases h : (val s p).edit
          · rfl
          · rw [hep h] at hcp; cases hcp
        simp [*]
      · cases (val s p).edit <;> simp [*]
    · cases (val s u).edit <;> cases (val s p).edit <;> simp
  · rw [hb, hdp, hfp]
    cases hcp : copied s p
    · have : (val s p).edit = false := by
        cases h : (val s p).edit
        · rfl
        · rw [hep h] at hcp; cases hcp
      have : (val s u).edit = false := by
        cases h : (val s u).edit
        · rfl
        · obtain ⟨hpc, _, _⟩ := copied_dep hs hd (heu h); rw [hpc] at hcp; cases hcp
      simp [*]
    · cases (val s u).edit <;> cases (val s p).edit <;> simp

/-- A Temporal value is immutable, so it always stays itself. -/
theorem temporal_kept (s : Scenario) (hs : WF s) (held : Nat → Bool) (i : Nat)
    (hk : (val s i).kind = .temporal) : outcome s held i = .value i := by
  have hd : (val s i).dep = none := by
    cases h : (val s i).dep with
    | none => rfl
    | some d => rcases hs.dep_kind i d h with h' | h' <;> rw [hk] at h' <;> cases h'.1
  have hf : ownerForced s held i = false := by
    cases h : ownerForced s held i
    · rfl
    · have := ownerForced_params hs h; rw [hk] at this; cases this
  rw [outcome_leaf held hd]
  simp [differs, hk, hf]

/-! ## Counterexamples

Each fact `chooseSpecial` reads matters: dropping one makes a scenario the runtime produces break a
promise above. -/

namespace Counterexamples

/-- A value without dependencies. -/
def plain (kind : Kind) (read edit : Bool) : Value := ⟨kind, none, false, read, edit⟩

/-- A date the recipe read and left unchanged. -/
def readDate : Scenario := [plain .date true false]
/-- A date the recipe read and changed. -/
def changedDate : Scenario := [plain .date true true]
/-- A buffer whose bytes changed and an unread view over it. -/
def unreadView : Scenario := [plain .buffer true true, ⟨.view, some 0, false, false, false⟩]
/-- A URL whose path changed and its unchanged `searchParams`. -/
def changedURL : Scenario := [⟨.url, some 1, false, true, true⟩, plain .params false false]

def all : Nat → Bool := fun _ => true

example : WF readDate ∧ WF changedDate ∧ WF unreadView ∧ WF changedURL :=
  ⟨check_sound (by decide), check_sound (by decide), check_sound (by decide),
    check_sound (by decide)⟩

/-- The sets the sealed pass reads for a scenario whose URLs the result all holds. -/
def sealedWith (s : Scenario) (c : Facts → Decision) : Ref → Bool → Obj :=
  resolveWith s c (planned s) (ownerForced s all)

/-- The sets discovery reads at its first decision of a value: nothing planned or forced yet. -/
def firstWith (s : Scenario) (c : Facts → Decision) : Ref → Bool → Obj :=
  resolveWith s c (fun _ => false) (fun _ => false)

/-- Origin: deciding a copy as a value with a copy keeps an unchanged copy, so a value and its
copy resolve to different objects. -/
example : sealedWith readDate (fun f => choose { f with origin := .base }) (.copy 0) false =
      .copy 0 ∧
    resolve readDate all (.copy 0) false = .value 0 ∧
    resolve readDate all (.value 0) true = .value 0 := by decide

/-- Equivalence: deciding as if every copy were equal loses a change. -/
example : sealedWith changedDate (fun f => choose { f with equivalent := true }) (.value 0)
      true = .value 0 ∧
    resolve changedDate all (.value 0) true = .copy 0 := by decide

/-- Stable dependencies: at discovery's first decision, an unread view over a changed buffer would
stay over the original buffer while the result holds the buffer's copy. -/
example : firstWith unreadView (fun f => choose { f with dependenciesStable := true })
      (.value 1) true = .value 1 ∧
    depOf unreadView all (.value 1) = some (.value 0) ∧
    resolve unreadView all (.value 0) true = .copy 0 ∧
    firstWith unreadView choose (.value 1) true = .fresh 1 ∧
    resolve unreadView all (.value 1) true = .fresh 1 ∧
    depOf unreadView all (.fresh 1) = some (.copy 0) := by decide

/-- Forced: the sealed pass compares neither the dependency nor the copy of a planned view, so a
decision that ignores `forced` keeps it over the original buffer. -/
example : factsOf unreadView all (.value 1) = ⟨.untracked, true, true, true⟩ ∧
    sealedWith unreadView (fun f => choose { f with forced := false }) (.value 1) true =
      .value 1 := by decide

/-- Owner forcing: without it the `searchParams` of a URL whose copy is kept would stay the
original, which the URL's copy does not own. -/
example : resolve changedURL all (.value 0) true = .copy 0 ∧
    depOf changedURL all (.copy 0) = some (.copy 1) ∧
    resolve changedURL all (.value 1) true = .copy 1 ∧
    resolveWith changedURL choose (planned changedURL) (fun _ => false) (.value 1) true =
      .value 1 := by decide

/-- One `searchParams` shared by two URLs, which `WF.owner` excludes: replacing one URL forces
the copy, which the other URL, kept, does not own. -/
def sharedParams : Scenario :=
  [⟨.url, some 2, false, true, true⟩, ⟨.url, some 2, false, false, false⟩, plain .params false false]

example : depOf sharedParams all (outcome sharedParams all 1) = some (.value 2) ∧
    outcome sharedParams all 2 = .copy 2 := by decide

end Counterexamples

end Reconcile.SpecialValues
