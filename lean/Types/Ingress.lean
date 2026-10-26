import Types.Atoms
import Types.RecognitionPlain

/-!
# One prototype read per object at ingress

Built-in ingress (`recognize` in `src/adapters/recognition.ts`, given a `PrototypeRead`) reads an
object's prototype once and decides both its kind (`Types.RecognitionPlain.recognize`) and, for
the plain-object fallback, whether it is an atom (`Types.Atoms.classify`), from that one read; a
separate atom split reads it again. The callers that meet the object first, capture, the snapshot
walk and draft creation, then hand the same prototype to its later readers before the first write:
discovery, the preflight's inherited-accessor check and a draft's target.

Both classifiers take the chain as input, so sharing the first read changes no decision; this
module states that the shared ingress decides as the two separate ones and counts the reads it
saves. The kind's capture then takes the same read (`capture_reads_once`), an object met at
several nodes is recognized at the first (`meetAll_once`), and Temporal capture takes the class
recognition found (`temporalCapture_passed`). That a later read would answer as the first did is
the runtime's stability obligation.
-/

namespace Reconcile.Types.Ingress

open Reconcile.Types

/-- One prototype as the two classifiers label it. -/
structure Proto where
  atom : Atoms.Proto
  recognition : RecognitionPlain.Proto

/-- The chain an object's prototype reads return, from its own prototype on. -/
structure Chain where
  protos : List Proto
  raises : Bool

def atoms (c : Chain) : Atoms.Chain := c.protos.map (·.atom)

def recognition (c : Chain) : RecognitionPlain.Chain := ⟨c.protos.map (·.recognition), c.raises⟩

/-- The outcome of ingress: a structural rank, the plain-object kind, an atom, or a raised read. -/
inductive Outcome where
  | structural (rank : Nat)
  | object
  | atom
  | raised
  deriving DecidableEq, Repr

/-- Recognition, then the atom split of the fallback rank 10 (`Atoms.ingress`). The split takes
the chain as input, so it decides the same whether it reads the prototype again or not. A branded
object is a typed array over a buffer the environment recognizes. -/
def ingress (isArray : Recognition.ProbeOutcome) (c : Chain) (brand : Bool)
    (ts : RecognitionPlain.Targets) : Outcome :=
  match RecognitionPlain.outcome
      (RecognitionPlain.recognize 10 isArray (recognition c) brand brand false ts) with
  | (some rank, _) =>
    match Atoms.ingress 10 rank (atoms c) with
    | .structural r => .structural r
    | .object => .object
    | .atom => .atom
  | (none, _) => .raised

/-- Reads of the object itself: recognition's one read, and for the plain-object fallback of an
object that is not an array, the atom split's own read unless it is shared. -/
def ownReads (shared : Bool) (isArray : Recognition.ProbeOutcome) (c : Chain) (brand : Bool)
    (ts : RecognitionPlain.Targets) : Nat :=
  if isArray = .hit then 0
  else 1 + (if !shared && ingress isArray c brand ts ∈ [.object, .atom] then 1 else 0)

/-- The atom split's reads of prototypes after the object's own: the walk `Atoms.classify`
makes past its first read. -/
def walkReads (c : Chain) : Nat := (Atoms.classify (atoms c)).2 - 1

/-- Sharing the first read reads the object once; a separate atom split read it twice for the
fallback. The walk over its prototypes is the same either way. -/
theorem ownReads_shared (isArray : Recognition.ProbeOutcome) (c : Chain) (brand : Bool)
    (ts : RecognitionPlain.Targets) (h : isArray ≠ .hit) :
    ownReads true isArray c brand ts = 1 ∧
      ownReads false isArray c brand ts =
        1 + (if ingress isArray c brand ts ∈ [.object, .atom] then 1 else 0) := by
  simp [ownReads, h]

/-- The atom split's walk past the first read is one read per prototype it passes. -/
theorem walkReads_eq (c : Chain) (h : (atoms c).head? ≠ some .array) :
    walkReads c = ((atoms c).takeWhile Atoms.walksOn).length := by
  unfold walkReads
  rw [Atoms.classify_reads _ h]
  omega

/-! ## Capture after ingress

Each kind's capture (`observe` in its type module, the snapshot walk's copy and a special value's
copy in `produce`) needs the object's prototype. Recognition already read it for every object that
is not an array, so the caller passes that read on, and the capture reads the prototype only when
it was not passed. -/

/-- Reads of the object itself by its kind's capture after ingress. Recognition does not read an
array's prototype, so the array's capture reads it once; any other captured kind reads it again
only when ingress did not pass its read on. An atom is kept by reference and an object whose read
raised is not captured, so neither is read again. -/
def captureReads (passed : Bool) (isArray : Recognition.ProbeOutcome) : Outcome → Nat
  | .atom | .raised => 0
  | _ => if isArray = .hit then 1 else if passed then 0 else 1

/-- The array probe decides an array before any prototype read. -/
theorem ingress_array (c : Chain) (brand : Bool) (ts : RecognitionPlain.Targets) :
    ingress .hit c brand ts = .structural 0 := rfl

/-- Ingress that shares its read and passes it on reads every object's prototype once, through
capture, whatever its kind. -/
theorem capture_reads_once (isArray : Recognition.ProbeOutcome) (c : Chain) (brand : Bool)
    (ts : RecognitionPlain.Targets) :
    ownReads true isArray c brand ts + captureReads true isArray (ingress isArray c brand ts) =
      1 := by
  cases isArray with
  | hit => rw [ingress_array]; rfl
  | miss =>
    simp only [ownReads, reduceCtorEq, if_false, Bool.not_true, Bool.false_and, Nat.add_zero]
    cases ingress .miss c brand ts <;> rfl
  | raised =>
    simp only [ownReads, reduceCtorEq, if_false, Bool.not_true, Bool.false_and, Nat.add_zero]
    cases ingress .raised c brand ts <;> rfl

/-- The runtime that read the prototype again in capture read a captured object that is not an
array twice, and the plain-object fallback a third time with a separate atom split. -/
theorem capture_reads_separate (isArray : Recognition.ProbeOutcome) (c : Chain) (brand : Bool)
    (ts : RecognitionPlain.Targets) (h : isArray ≠ .hit)
    (hc : ingress isArray c brand ts ≠ .atom ∧ ingress isArray c brand ts ≠ .raised) :
    ownReads false isArray c brand ts + captureReads false isArray (ingress isArray c brand ts) =
      if ingress isArray c brand ts = .object then 3 else 2 := by
  obtain ⟨hatom, hraised⟩ := hc
  simp only [ownReads, h, if_false, Bool.not_false, Bool.true_and]
  revert hatom hraised
  cases ingress isArray c brand ts <;> simp [captureReads, h]

/-! ## Objects met again

`reconcile` meets a current object at every node capture aligns it with, and discovery meets it
again at each further node it walks. Each meeting needs the object's kind and prototype. The
runtime recognizes the object at its first meeting and answers every later one from what that
recognition found: capture from the object's first aligned node, discovery from capture's
alignment and its own per-call memo. A later meeting would read the same answers, which is the
runtime's stability obligation, so the kinds are those of recognizing at every meeting. -/

/-- The kinds used at each meeting of `objects`, in order, and the objects recognized, in order.
`memo` holds the kind each object met so far was found to have; a later meeting takes it from
there. -/
def meetAll {α : Type} [DecidableEq α] (recognize : α → Outcome) :
    List (α × Outcome) → List α → List Outcome × List α
  | _, [] => ([], [])
  | memo, o :: rest =>
    match memo.lookup o with
    | some k => let r := meetAll recognize memo rest; (k :: r.1, r.2)
    | none =>
      let k := recognize o
      let r := meetAll recognize ((o, k) :: memo) rest
      (k :: r.1, o :: r.2)

/-- A memo whose kinds are the objects' own. -/
def Faithful {α : Type} (recognize : α → Outcome) (memo : List (α × Outcome)) : Prop :=
  ∀ o k, (o, k) ∈ memo → k = recognize o

theorem lookup_faithful {α : Type} [DecidableEq α] (recognize : α → Outcome)
    (memo : List (α × Outcome)) (h : Faithful recognize memo) (o : α) (k : Outcome)
    (hk : memo.lookup o = some k) : k = recognize o := by
  induction memo with
  | nil => simp at hk
  | cons head tail ih =>
    obtain ⟨o', k'⟩ := head
    by_cases ho : o = o'
    · subst ho
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hk
      exact hk ▸ h o k' (by simp)
    · have hne : (o == o') = false := by simpa using ho
      simp only [List.lookup, hne] at hk
      exact ih (fun o k hm => h o k (by simp [hm])) hk

theorem lookup_none {α : Type} [DecidableEq α] (memo : List (α × Outcome)) (o : α) :
    memo.lookup o = none ↔ ∀ k, (o, k) ∉ memo := by
  induction memo with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨o', k'⟩ := head
    by_cases ho : o = o'
    · subst ho
      simp only [List.lookup, beq_self_eq_true, reduceCtorEq, List.mem_cons, Prod.mk.injEq,
        true_and, false_iff, not_forall, not_not]
      exact ⟨k', Or.inl rfl⟩
    · have hne : (o == o') = false := by simpa using ho
      simp only [List.lookup, hne, ih, List.mem_cons, Prod.mk.injEq, ho, false_and, false_or]

/-- Every meeting uses the kind recognizing the object there would give. -/
theorem meetAll_kinds {α : Type} [DecidableEq α] (recognize : α → Outcome)
    (objects : List α) (memo : List (α × Outcome)) (h : Faithful recognize memo) :
    (meetAll recognize memo objects).1 = objects.map recognize := by
  induction objects generalizing memo with
  | nil => rfl
  | cons o rest ih =>
    unfold meetAll
    cases hk : memo.lookup o with
    | some k => simp only [List.map_cons, lookup_faithful recognize memo h o k hk, ih memo h]
    | none =>
      have h' : Faithful recognize ((o, recognize o) :: memo) := by
        intro o' k' hm
        rcases List.mem_cons.mp hm with he | hm
        · simp only [Prod.mk.injEq] at he
          rw [he.1, he.2]
        · exact h o' k' hm
      simp only [List.map_cons, ih _ h']

/-- The objects recognized are those met and not in the memo, each once. -/
theorem meetAll_reads {α : Type} [DecidableEq α] (recognize : α → Outcome)
    (objects : List α) (memo : List (α × Outcome)) :
    (meetAll recognize memo objects).2.Nodup ∧
      ∀ o, o ∈ (meetAll recognize memo objects).2 ↔ o ∈ objects ∧ memo.lookup o = none := by
  induction objects generalizing memo with
  | nil => simp [meetAll]
  | cons o rest ih =>
    unfold meetAll
    cases hk : memo.lookup o with
    | some k =>
      obtain ⟨hnodup, hmem⟩ := ih memo
      refine ⟨hnodup, fun o' => ?_⟩
      rw [hmem o']
      constructor
      · exact fun ⟨hr, hl⟩ => ⟨List.mem_cons_of_mem _ hr, hl⟩
      · rintro ⟨hr, hl⟩
        rcases List.mem_cons.mp hr with rfl | hr
        · rw [hl] at hk
          exact absurd hk (by simp)
        · exact ⟨hr, hl⟩
    | none =>
      obtain ⟨hnodup, hmem⟩ := ih ((o, recognize o) :: memo)
      have hlook : ∀ o', ((o, recognize o) :: memo).lookup o' = none ↔
          o' ≠ o ∧ memo.lookup o' = none := by
        intro o'
        by_cases ho : o' = o
        · subst ho
          simp [List.lookup]
        · have hne : (o' == o) = false := by simpa using ho
          simp [List.lookup, hne, ho]
      refine ⟨List.nodup_cons.mpr ⟨fun hin => ?_, hnodup⟩, fun o' => ?_⟩
      · exact ((hlook o).mp ((hmem o).mp hin).2).1 rfl
      · simp only [List.mem_cons, hmem o', hlook o']
        constructor
        · rintro (rfl | ⟨hr, hne, hl⟩)
          · exact ⟨Or.inl rfl, hk⟩
          · exact ⟨Or.inr hr, hl⟩
        · rintro ⟨rfl | hr, hl⟩
          · exact Or.inl rfl
          · by_cases ho : o' = o
            · exact Or.inl ho
            · exact Or.inr ⟨hr, ho, hl⟩

/-- A call that starts with no memo recognizes each object it meets exactly once, where
recognizing at every meeting reads it once per meeting. -/
theorem meetAll_once {α : Type} [DecidableEq α] (recognize : α → Outcome) (objects : List α) :
    (meetAll recognize [] objects).1 = objects.map recognize ∧
      (meetAll recognize [] objects).2.Nodup ∧
      ∀ o, o ∈ (meetAll recognize [] objects).2 ↔ o ∈ objects := by
  refine ⟨meetAll_kinds recognize objects [] (by simp [Faithful]), (meetAll_reads _ _ _).1,
    fun o => ?_⟩
  rw [(meetAll_reads recognize objects []).2 o]
  simp [List.lookup]

/-- One object aligned with two nodes, then another object: two recognitions, not three. -/
example : (meetAll (fun _ : Nat => Outcome.object) [] [0, 0, 1]).2 = [0, 1] := rfl

/-! ## The Temporal class

Recognition's Temporal probe reads the live namespace and its classes in order up to the first
class whose prototype is on the chain (`Types.Recognition.temporalTrace`), and Temporal capture
needs that class. Taking the class recognition selected probes nothing again; probing again, as
the runtime did, repeats recognition's trace. Both take the class at the selected rank, since a
repeated live read answers as the first did. -/

/-- The class capture uses and the probes it makes. -/
def temporalCapture (passed : Bool) (p0 p1 p2 p3 p4 p5 p6 p7 : Recognition.ProbeOutcome) :
    Recognition.ProbeTrace :=
  if passed then { selected := (Recognition.temporalTrace p0 p1 p2 p3 p4 p5 p6 p7).selected }
  else Recognition.temporalTrace p0 p1 p2 p3 p4 p5 p6 p7

/-- Passing the class on keeps the class and visits no probe; probing again visits recognition's
probes a second time. -/
theorem temporalCapture_passed (p0 p1 p2 p3 p4 p5 p6 p7 : Recognition.ProbeOutcome) :
    (temporalCapture true p0 p1 p2 p3 p4 p5 p6 p7).selected =
        (temporalCapture false p0 p1 p2 p3 p4 p5 p6 p7).selected ∧
      (temporalCapture true p0 p1 p2 p3 p4 p5 p6 p7).visited = [] ∧
      (temporalCapture false p0 p1 p2 p3 p4 p5 p6 p7).visited =
        (Recognition.temporalTrace p0 p1 p2 p3 p4 p5 p6 p7).visited :=
  ⟨rfl, rfl, rfl⟩

/-- A plain object: one shared read decides it, and it is not an atom. -/
example : ingress .miss ⟨[⟨.object, .object⟩], false⟩ false RecognitionPlain.absent = .object :=
  by decide

/-- A `RegExp`: recognition falls back, and the atom split finds its listed prototype. -/
example : ingress .miss ⟨[⟨.listed 0, .other 7⟩, ⟨.object, .object⟩], false⟩ false
    RecognitionPlain.absent = .atom := by decide

/-- A `Map`: recognition selects rank 2 and the atom split keeps it. -/
example : ingress .miss ⟨[⟨.data 3, .builtin 2⟩, ⟨.object, .object⟩], false⟩ false
    RecognitionPlain.absent = .structural 2 := by decide

end Reconcile.Types.Ingress
