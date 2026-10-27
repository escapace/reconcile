import Property.KeyOrder

/-!
# Finalization reads

`produce` answers three questions, and each answer is exact:

- **Provenance.** A slot's provenance, whether its value is backed by the current object, matters
  only for a value that has a special copy: the special-value decision reads it for no other
  slot. The observation records it only while the call holds a copy (`DraftObservation.copies` in
  `src/finalization.ts`). Copies only accumulate, and a pass that makes one is followed by a pass
  that observes every slot again and makes none, so the last observation sees every copy the
  decision sees and decides the same (`decisions_gated`).
- **Symbol keys.** A working copy lists its keys as `OrdinaryOwnPropertyKeys` does
  (`KeyOrder.ownKeys`), strings before symbols, so its last key is a symbol exactly when it holds
  one (`lastSymbol_iff`). The copy's flag starts set exactly when its first key list ends in a
  symbol and is set by each symbol written, so a copy whose flag is clear holds none and its string
  keys are all its keys (`keys_exact`, `PropertyDraftState.keys` in
  `src/types/shared/draft-properties.ts`).
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

/-! ## Symbol keys

A working copy is an ordinary object, so it lists its keys as `KeyOrder.ownKeys` does, and the
recipe's assignments and deletions are `KeyOrder`'s operations on it. -/

section SymbolKeys

open Reconcile.PropertyOrder Reconcile.PropertyPlacement Reconcile.KeyOrder

/-- Whether a key list ends in a symbol. -/
def lastSymbol (keys : List Key) : Bool := (keys.getLast?.map isSymbol).getD false

/-- `Object.getOwnPropertyNames`: the own keys that are not symbols, in own-key order. -/
def stringKeys (created : List Key) : List Key := (ownKeys created).filter fun k => !isSymbol k

/-- An object's own keys end in a symbol exactly when it holds one. -/
theorem lastSymbol_iff (created : List Key) :
    lastSymbol (ownKeys created) = !(created.filter isSymbol).isEmpty := by
  unfold lastSymbol
  rcases List.eq_nil_or_concat (created.filter isSymbol) with h | ⟨xs, x, h⟩
  · have hnone : ∀ k ∈ ownKeys created, isSymbol k = false := fun k hk => by
      by_contra hs
      have : k ∈ (ownKeys created).filter isSymbol := List.mem_filter.mpr ⟨hk, by simpa using hs⟩
      rw [ownKeys_filter_symbol, h] at this
      simp at this
    rw [h]
    rcases hl : (ownKeys created).getLast? with _ | k
    · rfl
    · simp [hnone k (List.mem_of_getLast? hl)]
  · have hx : isSymbol x = true := by
      have : x ∈ created.filter isSymbol := by rw [h]; simp
      exact (List.mem_filter.mp this).2
    unfold ownKeys
    rw [h]
    simp [hx]

/-- The flag after an operation: assigning a symbol sets it. -/
def flag : Op → Bool → Bool
  | .assign key, holds => holds || isSymbol key
  | .remove _, holds => holds

/-- The flag after `ops` from flag `holds`. -/
def flagAfter (holds : Bool) (ops : List Op) : Bool :=
  ops.foldl (fun holds op => flag op holds) holds

/-- An object whose flag is clear holds no symbol. -/
def Holds (holds : Bool) (created : List Key) : Prop := holds = false → created.filter isSymbol = []

theorem holds_step (holds : Bool) (created : List Key) (op : Op) (h : Holds holds created) :
    Holds (flag op holds) (KeyOrder.apply created op) := by
  intro hflag
  cases op with
  | assign key =>
    simp only [flag, Bool.or_eq_false_iff] at hflag
    have hs := h hflag.1
    simp only [KeyOrder.apply]
    split
    · exact hs
    · simp [List.filter_append, hs, hflag.2]
  | remove key =>
    simp only [KeyOrder.apply, ← List.erase_filter, h hflag, List.erase_nil]

theorem holds_after (holds : Bool) (created : List Key) (ops : List Op)
    (h : Holds holds created) : Holds (flagAfter holds ops) (KeyOrder.run created ops) := by
  induction ops generalizing holds created with
  | nil => exact h
  | cons op ops ih => exact ih _ _ (holds_step holds created op h)

/-- The flag starts as whether the copy's first key list ends in a symbol, and whatever the writes,
a copy whose flag is clear lists all its keys as its string keys: the symbol listing can be
skipped. -/
theorem keys_exact (start : List Key) (ops : List Op) :
    flagAfter (lastSymbol (ownKeys start)) ops = false →
      ownKeys (KeyOrder.run start ops) = stringKeys (KeyOrder.run start ops) := by
  intro hflag
  have hstart : Holds (lastSymbol (ownKeys start)) start := by
    intro h
    rw [lastSymbol_iff] at h
    simpa using h
  have hs := holds_after _ _ ops hstart hflag
  unfold stringKeys
  refine (List.filter_eq_self.mpr fun k hk => ?_).symm
  have : k ∉ (ownKeys (KeyOrder.run start ops)).filter isSymbol := by
    rw [ownKeys_filter_symbol, hs]
    simp
  simpa [List.mem_filter, hk] using this

end SymbolKeys

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
