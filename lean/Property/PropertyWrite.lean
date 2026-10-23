/-! Writing one property of an existing object, as `reconcile` does.

An object's content is its own properties; its prototype, including accessors on it, is
behavior that `reconcile` keeps and never writes or overrides. `reconcile` writes a changed own
property by ordinary assignment, so an own setter runs and an own accessor is kept. A key that
`current` lacks but whose assignment would reach an accessor on the prototype cannot be written
without overriding that behavior, so the check that runs before any write rejects it; the one
exception is `__proto__`, whose inherited accessor replaces the prototype and which is always
defined as an own data property.

The model is one key of one ordinary object: its own descriptor, the first descriptor
`OrdinarySet` finds on the prototype chain, and extensibility. A setter is application code, so
its effect is an arbitrary function of the slot and the value; `Storing` names the setters that
store what they receive. Equality is `SameValue`.

`admissible` is the per-key part of `canPublishProperties`, `publish` is `publishProperty`, and
`reconcileKey` is `reconcile` on a root object whose only key is this one, including the
readback of `matches`. Native correspondence requires `Reflect.get`, `Reflect.set`,
`Reflect.defineProperty`, `Object.getOwnPropertyDescriptor` and `Object.getPrototypeOf` to behave
as the ordinary internal methods on the target and every prototype, and the runtime's prototype
walk to return the descriptor `OrdinarySet` would consult. The walk reads a descriptor of
`Object.prototype` or `Array.prototype` only for a key that `in` reports there, and goes past
either one only when it does not own that key; for any other key it stops there, since `in` has
already searched the rest of the chain.
A proxy whose traps forward to an ordinary object, such as a Vue reactive proxy, meets this; other
exotic objects are outside the model. -/
namespace Reconcile.PropertyWrite

structure Attrs where
  writable : Bool
  enumerable : Bool
  configurable : Bool
  deriving DecidableEq, Repr

/-- An own property. An accessor's getter returns `stored`. -/
inductive Own (V : Type) where
  | data (value : V) (attrs : Attrs)
  | accessor (stored : V) (setter enumerable configurable : Bool)
  deriving DecidableEq, Repr

/-- The first descriptor on the prototype chain, as `OrdinarySet` sees it. -/
inductive Inherited where
  | none
  | data (writable : Bool)
  | accessor (setter : Bool)
  deriving DecidableEq, Repr

structure Slot (V : Type) where
  own : Option (Own V)
  inherited : Inherited
  extensible : Bool
  deriving DecidableEq, Repr

/-- Application code reachable from a write: an own setter and an inherited setter. -/
structure Env (V : Type) where
  ownSetter : Slot V → V → Slot V
  inheritedSetter : Slot V → V → Slot V

inductive Event where
  | ownSetter
  | inheritedSetter
  deriving DecidableEq, Repr

structure Outcome (V : Type) where
  ok : Bool
  slot : Slot V
  events : List Event

inductive Status where
  | done
  | rejectedBeforeWriting
  | rejectedAfterWriting
  deriving DecidableEq, Repr

structure Result (V : Type) where
  status : Status
  slot : Slot V
  events : List Event

variable {V : Type} [DecidableEq V]

/-- The attributes of a property created by assignment or by `defineData`. -/
def plain : Attrs := ⟨true, true, true⟩

/-- `[[Get]]` of an own property. -/
def read : Own V → V
  | .data value _ => value
  | .accessor stored .. => stored

/-- `OrdinarySet` with the target as receiver. -/
def set (env : Env V) (s : Slot V) (v : V) : Outcome V :=
  match s.own with
  | some (.data _ a) =>
    if a.writable then ⟨true, { s with own := some (.data v a) }, []⟩ else ⟨false, s, []⟩
  | some (.accessor _ true _ _) => ⟨true, env.ownSetter s v, [.ownSetter]⟩
  | some (.accessor _ false _ _) => ⟨false, s, []⟩
  | none =>
    match s.inherited with
    | .accessor true => ⟨true, env.inheritedSetter s v, [.inheritedSetter]⟩
    | .accessor false => ⟨false, s, []⟩
    | .data false => ⟨false, s, []⟩
    | .data true | .none =>
      if s.extensible then ⟨true, { s with own := some (.data v plain) }, []⟩
      else ⟨false, s, []⟩

/-- `ValidateAndApplyPropertyDescriptor` for a complete data descriptor. -/
def define (s : Slot V) (v : V) (a : Attrs) : Outcome V :=
  let done : Outcome V := ⟨true, { s with own := some (.data v a) }, []⟩
  match s.own with
  | none => if s.extensible then done else ⟨false, s, []⟩
  | some (.accessor _ _ _ c) => if c then done else ⟨false, s, []⟩
  | some (.data old b) =>
    if b.configurable then done
    else if !a.configurable && a.enumerable == b.enumerable &&
        (b.writable || (!a.writable && decide (old = v))) then done
    else ⟨false, s, []⟩

/-- Assignment, then a definition when assignment left no own property. -/
def assign (env : Env V) (s : Slot V) (v : V) (a : Attrs) : Outcome V :=
  let o := set env s v
  if o.ok && o.slot.own.isSome then o
  else let d := define o.slot v a; { d with events := o.events ++ d.events }

def inheritedAccessor : Inherited → Bool
  | .accessor _ => true
  | _ => false

/-- The per-key check before any write. `proto` marks the key `__proto__`. -/
def admissible (s : Slot V) (v : V) (proto : Bool) : Bool :=
  match s.own with
  | some (.data x a) => a.configurable || a.writable || decide (x = v)
  | some (.accessor stored setter _ _) => setter || decide (stored = v)
  | none => s.extensible && (proto || !inheritedAccessor s.inherited)

/-- The write of `publishProperty`. -/
def publish (env : Env V) (s : Slot V) (v : V) (proto : Bool) : Outcome V :=
  match s.own with
  | some own =>
    if read own = v then ⟨true, s, []⟩
    else match own with
      | .accessor .. => set env s v
      | .data _ a => assign env s v a
  | none =>
    if proto || inheritedAccessor s.inherited then define s v plain else assign env s v plain

/-- The readback of `matches`: the own property exists and reads as `v`. -/
def readsAs (s : Slot V) (v : V) : Bool :=
  match s.own with
  | some own => decide (read own = v)
  | none => false

/-- `reconcile` on a root object whose only key is this one. -/
def reconcileKey (env : Env V) (s : Slot V) (v : V) (proto : Bool) : Result V :=
  if admissible s v proto then
    let o := publish env s v proto
    if o.ok && readsAs o.slot v then ⟨.done, o.slot, o.events⟩
    else ⟨.rejectedAfterWriting, o.slot, o.events⟩
  else ⟨.rejectedBeforeWriting, s, []⟩

/-! ### An alternative rule

`admissibleOld`, `publishOld` and `reconcileOld` are an alternative rule, kept for comparison. It
replaces a configurable own accessor with a data property without calling its setter, does not
check inherited accessors before writing, assigns through an inherited setter and then defines an
own data property over it, and redefines a non-configurable getter-only accessor with a value,
which throws a `TypeError`; the model records that as a failure. -/

def admissibleOld (s : Slot V) (v : V) : Bool :=
  match s.own with
  | some (.data x a) => a.configurable || a.writable || decide (x = v)
  | some (.accessor stored setter _ c) => c || setter || decide (stored = v)
  | none => s.extensible

def publishOld (env : Env V) (s : Slot V) (v : V) (proto : Bool) : Outcome V :=
  match s.own with
  | some own =>
    if read own = v then ⟨true, s, []⟩
    else match own with
      | .accessor _ _ e true => define s v ⟨true, e, true⟩
      | .accessor _ _ _ false =>
        let o := set env s v
        if o.ok && o.slot.own.isSome then o else { o with ok := false }
      | .data _ a => assign env s v a
  | none => if proto then define s v plain else assign env s v plain

def reconcileOld (env : Env V) (s : Slot V) (v : V) (proto : Bool) : Result V :=
  if admissibleOld s v then
    let o := publishOld env s v proto
    if o.ok && readsAs o.slot v then ⟨.done, o.slot, o.events⟩
    else ⟨.rejectedAfterWriting, o.slot, o.events⟩
  else ⟨.rejectedBeforeWriting, s, []⟩

/-! ### Guarantees -/

theorem define_events (s : Slot V) (v : V) (a : Attrs) : (define s v a).events = [] := by
  unfold define
  split
  · split <;> rfl
  · split <;> rfl
  · split
    · rfl
    · split <;> rfl

/-- A check that fails writes nothing and runs no setter. -/
theorem reconcileKey_rejected (env : Env V) (s : Slot V) (v : V) (proto : Bool)
    (h : admissible s v proto = false) :
    reconcileKey env s v proto = ⟨.rejectedBeforeWriting, s, []⟩ := by
  simp [reconcileKey, h]

/-- A changed own accessor is written only by assignment, so its own setter runs and nothing
defines over it. -/
theorem publish_accessor (env : Env V) (s : Slot V) (v stored : V) (setter e c proto : Bool)
    (hs : s.own = some (.accessor stored setter e c)) (hv : stored ≠ v) :
    publish env s v proto = set env s v ∧
      ((set env s v).slot = env.ownSetter s v ∨ (set env s v).slot = s) := by
  constructor
  · simp [publish, hs, read, hv]
  · cases setter <;> simp [set, hs]

omit [DecidableEq V] in
theorem set_events_subset (env : Env V) (s : Slot V) (v : V) (hi : inheritedAccessor s.inherited = false ∨ s.own.isSome) :
    Event.inheritedSetter ∉ (set env s v).events := by
  obtain ⟨own, inh, ext⟩ := s
  rcases own with _ | ⟨x, ⟨w, e, c⟩⟩ | ⟨x, st, e, c⟩
  · rcases inh with _ | ⟨w⟩ | ⟨st⟩ <;> (try cases w) <;> (try cases st) <;> cases ext <;>
      simp_all [set, inheritedAccessor]
  · cases w <;> simp [set]
  · cases st <;> simp [set]

/-- `reconcile` never runs a setter on the prototype, whatever the slot and setters do. -/
theorem reconcileKey_no_inherited_setter (env : Env V) (s : Slot V) (v : V) (proto : Bool) :
    Event.inheritedSetter ∉ (reconcileKey env s v proto).events := by
  unfold reconcileKey
  split
  · rename_i hadm
    have hp : Event.inheritedSetter ∉ (publish env s v proto).events := by
      unfold publish
      split
      · rename_i own hown
        split
        · simp
        · cases own with
          | accessor => exact set_events_subset env s v (.inr (by simp [hown]))
          | data x a =>
            unfold assign
            dsimp only
            have := set_events_subset env s v (.inr (by simp [hown]))
            split
            · exact this
            · simp [define_events, this]
      · rename_i hown
        split
        · simp [define_events]
        · rename_i hproto
          have hi : inheritedAccessor s.inherited = false := by
            simpa using (Bool.not_eq_true _).mp hproto |> fun h => (Bool.or_eq_false_iff.mp h).2
          unfold assign
          dsimp only
          have := set_events_subset env s v (.inl hi)
          split
          · exact this
          · simp [define_events, this]
    dsimp only
    split <;> exact hp
  · simp

/-- A write that `reconcile` reports as done reads back as `v`. -/
theorem reconcileKey_sound (env : Env V) (s : Slot V) (v : V) (proto : Bool)
    (h : (reconcileKey env s v proto).status = .done) :
    readsAs (reconcileKey env s v proto).slot v = true := by
  unfold reconcileKey at *
  by_cases ha : admissible s v proto = true
  · by_cases hr : (publish env s v proto).ok = true ∧ readsAs (publish env s v proto).slot v = true
    · simp_all
    · simp_all
  · simp_all

/-- Setters that store the value they receive. -/
def Storing (env : Env V) : Prop :=
  ∀ s v stored setter e c, s.own = some (.accessor stored setter e c) →
    env.ownSetter s v = { s with own := some (.accessor v setter e c) }

/-- With storing setters, the check before writing decides the outcome exactly. -/
theorem reconcileKey_complete (env : Env V) (hstore : Storing env) (s : Slot V) (v : V)
    (proto : Bool) (h : admissible s v proto = true) :
    (reconcileKey env s v proto).status = .done := by
  obtain ⟨own, inh, ext⟩ := s
  rcases own with _ | ⟨x, ⟨w, e, c⟩⟩ | ⟨x, st, e, c⟩
  · cases proto <;> rcases inh with _ | ⟨w⟩ | ⟨st⟩ <;> (try cases w) <;> (try cases st) <;>
      cases ext <;>
      simp_all [reconcileKey, admissible, publish, assign, set, define, readsAs, read,
        inheritedAccessor, plain]
  · by_cases hx : x = v
    · simp_all [reconcileKey, admissible, publish, readsAs, read]
    · cases w <;> cases c <;>
        simp_all [reconcileKey, admissible, publish, assign, set, define, readsAs, read]
  · by_cases hx : x = v
    · simp_all [reconcileKey, admissible, publish, readsAs, read]
    · have hst : st = true := by simpa [admissible, hx] using h
      subst hst
      have := hstore ⟨some (.accessor x true e c), inh, ext⟩ v x true e c rfl
      simp_all [reconcileKey, admissible, publish, set, readsAs, read]

/-- A key the object lacks becomes an own data property holding `v`, and no setter runs: a key
whose assignment would reach an accessor is defined. For an object `reconcile` keeps, the check
before writing has already rejected that case; an object it adds is new, as in `construct`. -/
theorem publish_missing (env : Env V) (s : Slot V) (v : V) (proto : Bool)
    (hown : s.own = none) (hext : s.extensible = true) :
    publish env s v proto = ⟨true, { s with own := some (.data v plain) }, []⟩ := by
  obtain ⟨own, inh, ext⟩ := s
  simp only at hown hext
  subst hown hext
  cases proto <;> rcases inh with _ | ⟨w⟩ | ⟨st⟩ <;> (try cases w) <;> (try cases st) <;>
    simp [publish, assign, set, define, inheritedAccessor]

/-! ### Agreement with the alternative rule -/

/-- Where no accessor is involved, `reconcileKey` and the alternative rule agree. -/
theorem reconcileKey_eq_old (env : Env V) (s : Slot V) (v : V) (proto : Bool)
    (hown : ∀ x st e c, s.own ≠ some (.accessor x st e c))
    (hi : proto = true ∨ inheritedAccessor s.inherited = false) :
    reconcileKey env s v proto = reconcileOld env s v proto := by
  obtain ⟨own, inh, ext⟩ := s
  rcases own with _ | ⟨x, a⟩ | ⟨x, st, e, c⟩
  · rcases hi with hi | hi <;> simp_all [reconcileKey, reconcileOld, admissible, admissibleOld,
      publish, publishOld]
  · simp [reconcileKey, reconcileOld, admissible, admissibleOld, publish, publishOld]
  · exact absurd rfl (hown x st e c)

/-! ### Examples and counterexamples -/

/-- An own setter stores its value, as the native fixtures' setters do; an inherited setter
stores outside the object. -/
def storing : Env Nat :=
  ⟨fun s v => match s.own with
    | some (.accessor _ st e c) => { s with own := some (.accessor v st e c) }
    | _ => s,
   fun s _ => s⟩

private def vue2 : Slot Nat := ⟨some (.accessor 0 true true true), .none, true⟩

/-- A configurable own accessor, as Vue 2 defines: the alternative rule replaces it with a data
property without calling its setter, and `reconcileKey` assigns through the setter. -/
example : reconcileOld storing vue2 1 false =
    ⟨.done, ⟨some (.data 1 ⟨true, true, true⟩), .none, true⟩, []⟩ := rfl
example : reconcileKey storing vue2 1 false =
    ⟨.done, ⟨some (.accessor 1 true true true), .none, true⟩, [.ownSetter]⟩ := rfl

private def classAccessor : Slot Nat := ⟨none, .accessor true, true⟩

/-- An accessor on the prototype: the alternative rule runs its setter and then defines an own
data property over it, and `reconcileKey` rejects the key before writing. -/
example : reconcileOld storing classAccessor 1 false =
    ⟨.done, ⟨some (.data 1 plain), .accessor true, true⟩, [.inheritedSetter]⟩ := rfl
example : reconcileKey storing classAccessor 1 false =
    ⟨.rejectedBeforeWriting, classAccessor, []⟩ := rfl

/-- `__proto__` is defined as an own data property; the inherited accessor is not run. -/
example : reconcileKey storing classAccessor 1 true =
    ⟨.done, ⟨some (.data 1 plain), .accessor true, true⟩, []⟩ := rfl

/-- A configurable getter-only accessor: the alternative rule replaces it, and `reconcileKey`
rejects the write that cannot take effect before writing. -/
example : (reconcileOld storing ⟨some (.accessor 0 false true true), .none, true⟩ 1 false).status =
    .done := rfl
example : (reconcileKey storing ⟨some (.accessor 0 false true true), .none, true⟩ 1 false).status =
    .rejectedBeforeWriting := rfl

/-- A setter that ignores its value: the write runs the setter and fails the readback. -/
example : (reconcileKey ⟨fun s _ => s, fun s _ => s⟩ vue2 1 false).status = .rejectedAfterWriting :=
  rfl

/-! ### Writing a property of a new object

`snapshot`, `produce` and `reconcile` build new objects whose values are data properties. A new
object has no own properties yet, and on `Object.prototype` or a null prototype the only accessor
assignment can reach is `__proto__`'s, so assignment creates the same data property as a
definition; on any other prototype, including a class's, the property is defined. -/

/-- The write that creates one property of a new object. `standard` marks `Object.prototype` or
a null prototype; `proto` marks the key `__proto__`. -/
def construct (env : Env V) (s : Slot V) (v : V) (standard proto : Bool) : Outcome V :=
  if standard && !proto then set env s v else define s v plain

/-- A new object's property is an own data property holding `v`, and no setter runs. On a
standard prototype, assignment reaches no accessor and no read-only property. -/
theorem construct_data (env : Env V) (s : Slot V) (v : V) (standard proto : Bool)
    (hown : s.own = none) (hext : s.extensible = true)
    (hstd : standard = true → proto = false → s.inherited = .none ∨ s.inherited = .data true) :
    construct env s v standard proto = ⟨true, { s with own := some (.data v plain) }, []⟩ := by
  unfold construct
  by_cases h : (standard && !proto) = true
  · rw [if_pos h]
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases hstd h.1 h.2 with hi | hi <;> simp [set, hown, hi, hext]
  · rw [if_neg h]
    simp [define, hown, hext]

/-! A new object's property keeps its source's enumerability, which key listing, spread and JSON
observe. Writability and configurability protect the source, as its extensibility does, and are
not copied: the new property is writable and configurable. This covers the copies `snapshot`
makes and the objects `reconcile` adds; a `produce` draft instead follows its object's attributes,
so a rebuilt object keeps those its draft holds. -/

/-- The attributes a new object's property takes from a source property with this enumerability. -/
def copied (enumerable : Bool) : Attrs := ⟨true, enumerable, true⟩

theorem copied_true : copied true = plain := rfl

/-- The write that creates a new object's property from a source property: `construct` for an
enumerable one, and a definition for a non-enumerable one, which assignment cannot create. -/
def constructFrom (env : Env V) (s : Slot V) (v : V) (standard proto enumerable : Bool) :
    Outcome V :=
  if enumerable then construct env s v standard proto else define s v (copied false)

/-- A new object's property holds `v` with its source's enumerability, and no setter runs. -/
theorem constructFrom_data (env : Env V) (s : Slot V) (v : V) (standard proto enumerable : Bool)
    (hown : s.own = none) (hext : s.extensible = true)
    (hstd : standard = true → proto = false → s.inherited = .none ∨ s.inherited = .data true) :
    constructFrom env s v standard proto enumerable =
      ⟨true, { s with own := some (.data v (copied enumerable)) }, []⟩ := by
  cases enumerable
  · simp [constructFrom, define, hown, hext]
  · simp only [constructFrom, if_true]
    exact construct_data env s v standard proto hown hext hstd

/-- Assignment that reaches an inherited setter, which `construct_data` excludes on a standard
prototype, runs the setter and leaves the new object without an own property; on any other
prototype `construct` defines the property. -/
example : (construct storing ⟨none, .accessor true, true⟩ 1 true false).events = [.inheritedSetter] ∧
    (construct storing ⟨none, .accessor true, true⟩ 1 true false).slot.own = none := ⟨rfl, rfl⟩
example : construct storing ⟨none, .accessor true, true⟩ 1 false false =
    ⟨true, ⟨some (.data 1 plain), .accessor true, true⟩, []⟩ := rfl


/-! ### New objects under any `Object.prototype`

`construct` assumes `Object.prototype` unmodified. Any code can add a property to it, as data or
as an accessor, or make one read-only, as `Object.freeze` and hardened environments do; then an
assignment to a new object on it runs a setter or fails. The runtime asks `key in
Object.prototype`, which reads only `Object.prototype`'s own keys because its prototype is always
null, and assigns only where that is false. A new object's slot lists the inherited descriptor
assignment would reach: none on a null prototype, and `Object.prototype`'s own descriptor for the
key on `Object.prototype`, `.none` where it has none. -/

/-- The write that creates one property of a new object. `standard` marks `Object.prototype` or a
null prototype, and `inObject` that `Object.prototype` has an own property of the key. -/
def constructOn (env : Env V) (s : Slot V) (v : V) (standard inObject : Bool) : Outcome V :=
  if standard && !inObject then set env s v else define s v plain

/-- A new object's property is an own data property holding `v`, and no setter runs, wherever
assignment reaches nothing. -/
theorem constructOn_data (env : Env V) (s : Slot V) (v : V) (standard inObject : Bool)
    (hown : s.own = none) (hext : s.extensible = true)
    (hstd : standard = true → inObject = false → s.inherited = .none) :
    constructOn env s v standard inObject = ⟨true, { s with own := some (.data v plain) }, []⟩ := by
  unfold constructOn
  by_cases h : (standard && !inObject) = true
  · rw [if_pos h]
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    simp [set, hown, hstd h.1 h.2, hext]
  · rw [if_neg h]
    simp [define, hown, hext]

/-- A new object on a null prototype, or on `Object.prototype` holding `held` for the key. -/
def fresh (onObject : Bool) (held : Inherited) : Slot V :=
  ⟨none, if onObject then held else .none, true⟩

/-- Whatever `Object.prototype` holds, a new object's property on a standard prototype is an own
data property holding `v`, and no setter runs. On a null prototype `inObject` may be anything; on
`Object.prototype` it is what `key in Object.prototype` reports. -/
theorem constructOn_fresh (env : Env V) (v : V) (onObject : Bool) (held : Inherited)
    (inObject : Bool) (hin : onObject = true → inObject = decide (held ≠ .none)) :
    constructOn env (fresh onObject held) v true inObject =
      ⟨true, { (fresh onObject held : Slot V) with own := some (.data v plain) }, []⟩ := by
  apply constructOn_data env _ v true inObject rfl rfl
  intro _ hi
  cases onObject
  · rfl
  · have := hin rfl
    simp only [fresh, if_true]
    cases held <;> simp_all

/-- Where `construct`'s premise holds, as on an unmodified `Object.prototype`, whose keys reach no
accessor but `__proto__` and no read-only property, the guarded write has exactly its outcome. -/
theorem constructOn_eq_construct (env : Env V) (s : Slot V) (v : V) (standard proto inObject : Bool)
    (hown : s.own = none) (hext : s.extensible = true)
    (hstd : standard = true → proto = false → s.inherited = .none ∨ s.inherited = .data true)
    (hnone : standard = true → inObject = false → s.inherited = .none) :
    constructOn env s v standard inObject = construct env s v standard proto := by
  rw [constructOn_data env s v standard inObject hown hext hnone,
    construct_data env s v standard proto hown hext hstd]

/-- `constructFrom` under any `Object.prototype`: a non-enumerable property is always defined. -/
def constructFromOn (env : Env V) (s : Slot V) (v : V) (standard inObject enumerable : Bool) :
    Outcome V :=
  if enumerable then constructOn env s v standard inObject else define s v (copied false)

theorem constructFromOn_fresh (env : Env V) (v : V) (onObject : Bool) (held : Inherited)
    (inObject enumerable : Bool) (hin : onObject = true → inObject = decide (held ≠ .none)) :
    constructFromOn env (fresh onObject held) v true inObject enumerable =
      ⟨true, { (fresh onObject held : Slot V) with own := some (.data v (copied enumerable)) },
        []⟩ := by
  cases enumerable
  · simp [constructFromOn, define, fresh]
  · simp only [constructFromOn, if_true]
    exact constructOn_fresh env v onObject held inObject hin

/-- A setter added to `Object.prototype`: `construct` runs it and leaves no own property; the
guarded write defines the property. -/
example : (construct storing (fresh true (.accessor true)) 1 true false).events =
      [.inheritedSetter] ∧
    (construct storing (fresh true (.accessor true)) 1 true false).slot.own = none := ⟨rfl, rfl⟩
example : constructOn storing (fresh true (.accessor true)) 1 true true =
    ⟨true, ⟨some (.data 1 plain), .accessor true, true⟩, []⟩ := rfl

/-- A read-only property of a frozen `Object.prototype`: `construct`'s assignment fails, and the
guarded write defines the property. -/
example : (construct storing (fresh true (.data false)) 1 true false).ok = false := rfl
example : constructOn storing (fresh true (.data false)) 1 true true =
    ⟨true, ⟨some (.data 1 plain), .data false, true⟩, []⟩ := rfl


/-! ### A recipe's assignment through an inherited setter

A `produce` recipe assigns to a draft, which must behave as the object would. An assignment of a
key the object lacks that reaches a setter on its prototype calls the setter with the draft as
receiver. A hardened environment's setter, such as one `node --frozen-intrinsics` or SES puts on
`Object.prototype`, defines the key on its receiver as data that assignment would create. A draft
refuses reflective definitions, which its result could not carry; it accepts exactly this one,
the key being assigned, defined as assignment would while the draft still lacks it. -/

/-- What an inherited setter defines on its receiver for the key being assigned. -/
inductive Defines (V : Type) where
  | nothing
  | data (value : V) (attrs : Attrs)
  deriving DecidableEq, Repr

/-- Assignment on an ordinary object lacking the key, through an inherited setter. -/
def throughSetter (s : Slot V) : Defines V → Outcome V
  | .nothing => ⟨true, s, [.inheritedSetter]⟩
  | .data v a =>
    let d := define s v a
    { d with events := .inheritedSetter :: d.events }

/-- The same assignment on a draft: the setter's definition is accepted when it is the one
assignment would make, and refused otherwise. -/
def draftThroughSetter (s : Slot V) : Defines V → Outcome V
  | .nothing => ⟨true, s, [.inheritedSetter]⟩
  | .data v a =>
    if a = plain then
      let d := define s v a
      { d with events := .inheritedSetter :: d.events }
    else ⟨false, s, [.inheritedSetter]⟩

/-- The alternative rule: the draft refuses every definition an inherited setter makes. -/
def draftThroughSetterOld (s : Slot V) : Defines V → Outcome V
  | .nothing => ⟨true, s, [.inheritedSetter]⟩
  | .data _ _ => ⟨false, s, [.inheritedSetter]⟩

/-- A setter that defines nothing, or defines the key as assignment would, has the same outcome
on a draft as on the object. -/
theorem draftThroughSetter_eq (s : Slot V) (d : Defines V)
    (hd : d = .nothing ∨ ∃ v, d = .data v plain) :
    draftThroughSetter s d = throughSetter s d := by
  rcases hd with rfl | ⟨v, rfl⟩ <;> simp [draftThroughSetter, throughSetter]

/-- Any other definition is refused, writing nothing, as the draft surface requires. -/
theorem draftThroughSetter_refused (s : Slot V) (v : V) (a : Attrs) (ha : a ≠ plain) :
    draftThroughSetter s (.data v a) = ⟨false, s, [.inheritedSetter]⟩ := by
  simp [draftThroughSetter, ha]

/-- The hardened setter's definition makes the lacking key an own data property, on the object and
on the draft alike. -/
theorem draftThroughSetter_tamed (s : Slot V) (v : V) (hown : s.own = none)
    (hext : s.extensible = true) :
    draftThroughSetter s (.data v plain) =
      ⟨true, { s with own := some (.data v plain) }, [.inheritedSetter]⟩ := by
  simp [draftThroughSetter, define, hown, hext]

/-- Under the alternative rule the draft refuses the hardened setter's definition, so the
assignment fails, where assignment on the object succeeds. -/
example : (draftThroughSetterOld (fresh true (.accessor true) : Slot Nat) (.data 1 plain)).ok =
      false ∧
    (throughSetter (fresh true (.accessor true) : Slot Nat) (.data 1 plain)).ok = true :=
  ⟨rfl, rfl⟩

/-! ## Assignment on a draft

A `produce` draft's `set` trap, with the draft as receiver, decides in its own order: an own
accessor, else the first one on the prototype chain, goes to its setter; a read-only own or
inherited data property refuses; an own data property takes the value, and writes nothing when
the value is already there; a lacking key is added only while the object is extensible. The
runtime's obligations are those of `set`, with the draft's own descriptors standing for the
object's and `Object.isExtensible` read from the object itself. -/

/-- The draft's assignment, in the runtime's order (`PropertyDraftState.set`, `writeProperty`). -/
def draftSet (env : Env V) (s : Slot V) (v : V) : Outcome V :=
  match s.own with
  | some (.accessor _ true _ _) => ⟨true, env.ownSetter s v, [.ownSetter]⟩
  | some (.accessor _ false _ _) => ⟨false, s, []⟩
  | some (.data current a) =>
    if !a.writable then ⟨false, s, []⟩
    else if current = v then ⟨true, s, []⟩
    else ⟨true, { s with own := some (.data v a) }, []⟩
  | none =>
    match s.inherited with
    | .accessor true => ⟨true, env.inheritedSetter s v, [.inheritedSetter]⟩
    | .accessor false => ⟨false, s, []⟩
    | .data false => ⟨false, s, []⟩
    | .data true | .none =>
      if !s.extensible then ⟨false, s, []⟩
      else ⟨true, { s with own := some (.data v plain) }, []⟩

/-- An assignment to a draft has the outcome it has on the object: the same success, slot and
setter calls. -/
theorem draftSet_eq (env : Env V) (s : Slot V) (v : V) : draftSet env s v = set env s v := by
  rcases s with ⟨own, inherited, extensible⟩
  rcases own with _ | ⟨current, a⟩ | ⟨stored, setter, e, c⟩
  · cases inherited with
    | none => cases extensible <;> rfl
    | data w => cases w <;> cases extensible <;> rfl
    | accessor h => cases h <;> rfl
  · by_cases hw : a.writable
    · by_cases hv : current = v
      · subst hv; simp [draftSet, set, hw]
      · simp [draftSet, set, hw, hv]
    · simp [draftSet, set, hw]
  · cases setter <;> rfl

/-- The previous draft rule added a lacking key whatever the object's extensibility. -/
def draftSetOld (env : Env V) (s : Slot V) (v : V) : Outcome V :=
  match s.own, s.inherited with
  | none, .data true | none, .none => ⟨true, { s with own := some (.data v plain) }, []⟩
  | _, _ => draftSet env s v

/-- On a frozen, sealed or otherwise non-extensible object, the previous rule accepted a new key
that assignment on the object refuses. -/
example (env : Env Nat) :
    (draftSetOld env ⟨none, .none, false⟩ 1).ok = true ∧
      (set env ⟨none, .none, false⟩ 1).ok = false :=
  ⟨rfl, rfl⟩

end Reconcile.PropertyWrite
