/-!
# Finalization reads

`produce` answers three questions, and each answer is exact:

- **Provenance.** A slot's provenance, whether its value is backed by the current object, matters
  only for a value that has a special copy: the special-value decision reads it for no other
  slot. The observation records it only while the call holds a copy (`DraftObservation.copies` in
  `src/finalization.ts`). Copies only accumulate, and a pass that makes one is followed by a pass
  that observes every slot again and makes none, so the last observation sees every copy the
  decision sees and decides the same (`decisions_gated`).
- **Symbol keys.** A working copy lists its keys as `OrdinaryOwnPropertyKeys` does, strings before
  symbols, so its last key is a symbol exactly when it holds one (`lastSymbol_iff`). The copy starts
  holding a symbol exactly when its first key list ends in one and records each symbol written, so
  a copy that never did holds none and its string keys are all its keys (`keys_exact`,
  `PropertyDraftState.keys` in `src/types/shared/draft-properties.ts`).
- **Draft lookups.** The finalization walk looks each object's draft up once. Drafts are only added,
  each addition counted, and never replaced, so after a walk a draft found before is still that
  draft, and one absent before can exist only if the count moved (`reread_exact`, `checkState` in
  `src/finalization.ts`).
-/

namespace Reconcile.FinalizationReads

/-! ## Provenance -/

/-- A slot: the value it holds and whether that value is backed by the current object. -/
structure Slot where
  value : Nat
  backed : Bool

/-- An observation of `slots` that records provenance only while `copies` holds a value. -/
def observeGated (copies : List Nat) (slots : List Slot) : List (Option Bool) :=
  slots.map fun s => if copies.isEmpty then none else some s.backed

/-- An observation that records every slot's provenance. -/
def observeAll (slots : List Slot) : List (Option Bool) :=
  slots.map fun s => some s.backed

/-- The decision for one slot from the provenance recorded for it: a value with a copy takes
`choose` with that provenance, any other value `rest`, which reads none. -/
def decideSlot {D : Type} (copies : List Nat) (choose : Nat → Bool → D) (rest : Nat → D)
    (s : Slot) (recorded : Option Bool) : D :=
  if copies.contains s.value then choose s.value (recorded.getD false) else rest s.value

/-- The decisions for `slots` from one observation. -/
def decisions {D : Type} (copies : List Nat) (choose : Nat → Bool → D) (rest : Nat → D)
    (slots : List Slot) (observed : List (Option Bool)) : List D :=
  (slots.zip observed).map fun (s, r) => decideSlot copies choose rest s r

/-- With the copies the observation saw, recording provenance only while a copy exists decides
every slot as recording it always does. -/
theorem decisions_observe {D : Type} (copies : List Nat) (choose : Nat → Bool → D)
    (rest : Nat → D) (slots : List Slot) :
    decisions copies choose rest slots (observeGated copies slots) =
      decisions copies choose rest slots (observeAll slots) := by
  unfold decisions observeGated observeAll
  induction slots with
  | nil => rfl
  | cons s rest' ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.cons.injEq]
    refine ⟨?_, ih⟩
    unfold decideSlot
    by_cases h : s.value ∈ copies
    · have hne : copies ≠ [] := List.ne_nil_of_mem h
      simp [h, hne]
    · simp [h]

/-- One observation pass: the copies it found, and the copies it added by running getters. -/
structure Pass where
  added : List Nat

/-- The copies after `passes`, from `start`. -/
def copiesAfter (start : List Nat) (passes : List Pass) : List Nat :=
  passes.foldl (fun copies p => copies ++ p.added) start

/-- The decisions of a call whose finalization observes in `passes`, the last one deciding: each
pass observes with the copies made so far, a pass that adds copies is never last, so the last pass
adds none, and the decision sees the copies after every pass. Recording provenance only while a
copy exists decides as recording it always does. -/
theorem decisions_gated {D : Type} (start : List Nat) (earlier : List Pass) (last : Pass)
    (hlast : last.added = []) (choose : Nat → Bool → D) (rest : Nat → D) (slots : List Slot) :
    let seen := copiesAfter start earlier
    let final := copiesAfter start (earlier ++ [last])
    decisions final choose rest slots (observeGated seen slots) =
      decisions final choose rest slots (observeAll slots) := by
  intro seen final
  have hfinal : final = seen := by
    simp [final, seen, copiesAfter, List.foldl_append, hlast]
  rw [hfinal]
  exact decisions_observe seen choose rest slots

/-! ## Symbol keys -/

/-- A property key: a string or a symbol. -/
inductive Key where
  | str (name : String)
  | sym (id : Nat)
  deriving DecidableEq

def Key.isSymbol : Key → Bool
  | .sym _ => true
  | .str _ => false

/-- A working copy's keys in `OrdinaryOwnPropertyKeys` order: its string keys, then its symbols. -/
structure Store where
  names : List String
  symbols : List Nat

def Store.ownKeys (s : Store) : List Key := s.names.map .str ++ s.symbols.map .sym

def Store.stringKeys (s : Store) : List Key := s.names.map .str

/-- Whether a key list ends in a symbol. -/
def lastSymbol (keys : List Key) : Bool := (keys.getLast?.map Key.isSymbol).getD false

/-- A key list in `OrdinaryOwnPropertyKeys` order ends in a symbol exactly when it holds one. -/
theorem lastSymbol_iff (s : Store) : lastSymbol s.ownKeys = !s.symbols.isEmpty := by
  unfold lastSymbol Store.ownKeys
  rcases List.eq_nil_or_concat s.symbols with h | ⟨xs, x, h⟩
  · rw [h]
    rcases List.eq_nil_or_concat s.names with hn | ⟨ys, y, hn⟩
    · rw [hn]; rfl
    · rw [hn]; simp [Key.isSymbol]
  · rw [h]; simp [Key.isSymbol]

/-- A write to a working copy: a string key set, a symbol set, or a key deleted. -/
inductive Write where
  | setName (name : String)
  | setSymbol (id : Nat)
  | delete (key : Key)

def Write.apply : Write → Store → Store
  | .setName n, s => if s.names.contains n then s else { s with names := s.names ++ [n] }
  | .setSymbol i, s => if s.symbols.contains i then s else { s with symbols := s.symbols ++ [i] }
  | .delete (.str n), s => { s with names := s.names.filter (· != n) }
  | .delete (.sym i), s => { s with symbols := s.symbols.filter (· != i) }

/-- The flag after a write: a symbol write sets it. -/
def Write.flag : Write → Bool → Bool
  | .setSymbol _, _ => true
  | _, holds => holds

/-- The flag and copy after `writes` from flag `holds` and copy `s`. -/
def afterFrom (holds : Bool) (s : Store) (writes : List Write) : Bool × Store :=
  writes.foldl (fun (hs : Bool × Store) w => (w.flag hs.1, w.apply hs.2)) (holds, s)

/-- The flag and copy after `writes`, the flag starting as whether the first key list ends in a
symbol. -/
def afterWrites (start : Store) (writes : List Write) : Bool × Store :=
  afterFrom (lastSymbol start.ownKeys) start writes

/-- A copy whose flag is clear holds no symbol. -/
def Holds (holds : Bool) (s : Store) : Prop := holds = false → s.symbols = []

theorem holds_step (holds : Bool) (s : Store) (w : Write) (h : Holds holds s) :
    Holds (w.flag holds) (w.apply s) := by
  intro hflag
  cases w with
  | setName n =>
    simp only [Write.flag] at hflag
    have := h hflag
    simp only [Write.apply]
    split <;> simp [this]
  | setSymbol i => simp [Write.flag] at hflag
  | delete k =>
    simp only [Write.flag] at hflag
    have := h hflag
    cases k <;> simp [Write.apply, this]

theorem holds_after (holds : Bool) (s : Store) (writes : List Write) (h : Holds holds s) :
    Holds (afterFrom holds s writes).1 (afterFrom holds s writes).2 := by
  induction writes generalizing holds s with
  | nil => exact h
  | cons w ws ih => exact ih _ _ (holds_step holds s w h)

/-- Whatever the writes, a copy whose flag is clear lists all its keys as its string keys: the
symbol listing can be skipped. -/
theorem keys_exact (start : Store) (writes : List Write) :
    (afterWrites start writes).1 = false →
      (afterWrites start writes).2.ownKeys = (afterWrites start writes).2.stringKeys := by
  intro hflag
  have hstart : Holds (lastSymbol start.ownKeys) start := by
    intro h
    rw [lastSymbol_iff] at h
    simpa using h
  have hs := holds_after _ _ writes hstart hflag
  unfold afterWrites at hs ⊢
  generalize (afterFrom (lastSymbol start.ownKeys) start writes).2 = s at hs ⊢
  simp [Store.ownKeys, Store.stringKeys, hs]

/-! ## Draft lookups -/

/-- The drafts of a call: each object's draft, and how many drafts the call made. -/
structure Session where
  drafts : List (Nat × Nat)
  count : Nat

def Session.lookup (s : Session) (o : Nat) : Option Nat := s.drafts.lookup o

/-- An event of a walk: a draft made for an object that had none, counted, or any change that adds
no draft, such as a write through an existing one. -/
inductive Event where
  | draft (o d : Nat)
  | other

def Event.apply : Event → Session → Session
  | .draft o d, s =>
    if (s.lookup o).isSome then s else { drafts := (o, d) :: s.drafts, count := s.count + 1 }
  | .other, s => s

def walk (s : Session) (events : List Event) : Session := events.foldl (fun s e => e.apply s) s

theorem apply_keep (e : Event) (s : Session) (o d : Nat) (h : s.lookup o = some d) :
    (e.apply s).lookup o = some d := by
  cases e with
  | other => exact h
  | draft o' d' =>
    simp only [Event.apply]
    split
    · exact h
    · rename_i hn
      by_cases ho : o = o'
      · subst ho
        simp [h] at hn
      · have hb : (o == o') = false := by simpa using ho
        simpa [Session.lookup, List.lookup, hb] using h

theorem apply_mono (e : Event) (s : Session) : s.count ≤ (e.apply s).count := by
  cases e with
  | other => exact Nat.le_refl _
  | draft o' d' =>
    simp only [Event.apply]
    split <;> simp

theorem apply_same (e : Event) (s : Session) (o : Nat) (hc : (e.apply s).count = s.count) :
    (e.apply s).lookup o = s.lookup o := by
  cases e with
  | other => rfl
  | draft o' d' =>
    simp only [Event.apply] at hc ⊢
    split at hc
    · simp_all
    · simp at hc

theorem walk_mono (s : Session) (events : List Event) : s.count ≤ (walk s events).count := by
  induction events generalizing s with
  | nil => exact Nat.le_refl _
  | cons e es ih => exact Nat.le_trans (apply_mono e s) (ih (e.apply s))

/-- A walk never replaces a draft. -/
theorem walk_keep (s : Session) (events : List Event) (o d : Nat) (h : s.lookup o = some d) :
    (walk s events).lookup o = some d := by
  induction events generalizing s with
  | nil => exact h
  | cons e es ih => exact ih (e.apply s) (apply_keep e s o d h)

/-- A walk that counts no draft adds none. -/
theorem walk_same (s : Session) (events : List Event) (o : Nat)
    (hc : (walk s events).count = s.count) : (walk s events).lookup o = s.lookup o := by
  induction events generalizing s with
  | nil => rfl
  | cons e es ih =>
    have h1 := apply_mono e s
    have h2 := walk_mono (e.apply s) es
    have hc' : (walk (e.apply s) es).count = s.count := hc
    have happly : (e.apply s).count = s.count := by omega
    have hwalk : (walk (e.apply s) es).count = (e.apply s).count := by omega
    exact (ih (e.apply s) hwalk).trans (apply_same e s o happly)

/-- The draft the check reads after a walk: the one found before, if any; otherwise a fresh lookup
only when the walk made a draft. It is exactly the draft a fresh lookup finds. -/
theorem reread_exact (s : Session) (events : List Event) (o : Nat) :
    let after := walk s events
    (match s.lookup o with
      | some d => some d
      | none => if after.count ≠ s.count then after.lookup o else none) = after.lookup o := by
  intro after
  cases h : s.lookup o with
  | some d => exact (walk_keep s events o d h).symm
  | none =>
    simp only
    split
    · rfl
    · rename_i hc
      have := walk_same s events o (by simpa [after] using hc)
      rw [this, h]

end Reconcile.FinalizationReads
