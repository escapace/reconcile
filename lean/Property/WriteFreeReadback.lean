import Property.PropertyWrite
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Subperm

/-!
# Readback after a write-free publication

`reconcile` publishes every retained object and then reads each one back (`matches`) before it
accepts the plan. This module proves that when publication wrote nothing, the readback of a plain
object or an array would accept: the facts publication compared are the facts readback compares.
`publishGraph` in `src/publication/publication-engine.ts` therefore answers the readback of such
an attempt without reading again.

The premise is that reads are stable: with no write, no setter and no write trap has run, so the
readback would observe what publication observed. The model takes one observation for both.

It also proves that publishing a key with the slot the pre-write check observed equals publishing
with the live slot when the two agree (`publishKnown_eq`): the runtime takes presence and
attributes from the descriptor the check read, and still reads the value live.
-/

namespace Reconcile.WriteFreeReadback

open Reconcile.PropertyWrite

variable {K V : Type} [DecidableEq K] [DecidableEq V]

/-! ## One key -/

/-- `publishProperty`'s write-free branch: the key is own and reads as the wanted value. -/
def unchanged (s : Slot V) (v : V) : Bool :=
  match s.own with
  | some own => decide (read own = v)
  | none => false

/-- In the write-free branch publication keeps the slot, calls no setter and reads back as `v`. -/
theorem unchanged_publish (env : Env V) (s : Slot V) (v : V) (proto : Bool)
    (h : unchanged s v = true) :
    publish env s v proto = ⟨true, s, []⟩ ∧ readsAs s v = true := by
  unfold unchanged at h
  unfold publish readsAs
  split at h
  · rename_i own hown
    simp only [hown, decide_eq_true_eq] at h ⊢
    simp [h]
  · cases h

/-- The runtime's publication with the descriptor the pre-write check read: presence and
attributes come from `pre`, the value is read from the live slot `s`. -/
def publishKnown (env : Env V) (pre s : Slot V) (v : V) (proto : Bool) : Outcome V :=
  match pre.own with
  | some (.data _ a) =>
    match s.own with
    | some own => if read own = v then ⟨true, s, []⟩ else assign env s v a
    | none => publish env s v proto
  | _ => publish env s v proto

/-- With stable reads the pre-write slot is the live slot, and publication is unchanged. -/
theorem publishKnown_eq (env : Env V) (s : Slot V) (v : V) (proto : Bool) :
    publishKnown env s s v proto = publish env s v proto := by
  unfold publishKnown publish
  rcases hs : s.own with _ | own
  · simp
  · cases own <;> simp

/-! ## Plain objects -/

/-- `alignedPrefix` in `src/types/shared/property-publication.ts`: the shared prefix agrees. -/
def alignedPrefix : List K → List K → Bool
  | [], _ => true
  | _, [] => true
  | a :: as, b :: bs => decide (a = b) && alignedPrefix as bs

theorem alignedPrefix_prefix :
    ∀ (prev desired : List K), alignedPrefix prev desired = true →
      prev.length ≤ desired.length → prev <+: desired
  | [], _, _, _ => List.nil_prefix
  | _ :: _, [], _, h => by simp at h
  | a :: as, b :: bs, h, hl => by
    simp only [alignedPrefix, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, h⟩ := h
    exact List.cons_prefix_cons.2 ⟨rfl, alignedPrefix_prefix as bs h (by simpa using hl)⟩

/-- What publication observes of a plain object: its own keys in order and each key's slot. -/
structure Observed (K V : Type) where
  keys : List K
  slot : K → Slot V

/-- The own keys list exactly the keys with an own property. -/
def Listed (o : Observed K V) : Prop := ∀ k, k ∈ o.keys ↔ (o.slot k).own.isSome

/-- `publish` in `src/types/object.ts` writes nothing: the observed keys are aligned with the
requested ones and need no deletion, and every requested key is unchanged. -/
def objectWriteFree (desired : List K) (want : K → V) (o : Observed K V) : Bool :=
  alignedPrefix o.keys desired && decide (o.keys.length ≤ desired.length) &&
    desired.all fun k => unchanged (o.slot k) (want k)

/-- `matches` in `src/types/object.ts`: exactly the requested keys in order, each reading as the
wanted value. -/
def objectMatches (desired : List K) (want : K → V) (o : Observed K V) : Prop :=
  o.keys = desired ∧ ∀ k ∈ desired, readsAs (o.slot k) (want k) = true

theorem unchanged_isSome (s : Slot V) (v : V) (h : unchanged s v = true) : s.own.isSome := by
  unfold unchanged at h
  split at h <;> simp_all

theorem unchanged_readsAs (s : Slot V) (v : V) (h : unchanged s v = true) :
    readsAs s v = true := by
  unfold unchanged at h
  unfold readsAs
  split at h <;> simp_all

/-- A write-free publication of a plain object is followed by an accepting readback. -/
theorem object_writeFree_matches (desired : List K) (want : K → V) (o : Observed K V)
    (hnodup : desired.Nodup) (hlisted : Listed o)
    (h : objectWriteFree desired want o = true) : objectMatches desired want o := by
  simp only [objectWriteFree, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨haligned, hlength⟩, hall⟩ := h
  have hprefix := alignedPrefix_prefix o.keys desired haligned hlength
  have hsub : desired ⊆ o.keys := fun k hk =>
    (hlisted k).2 (unchanged_isSome _ _ (hall k hk))
  have hle : desired.length ≤ o.keys.length := (hnodup.subperm hsub).length_le
  refine ⟨hprefix.eq_of_length (le_antisymm hlength hle), fun k hk => ?_⟩
  exact unchanged_readsAs _ _ (hall k hk)

/-! ## Arrays -/

/-- What publication observes of an array: its `length` and each index's own value, or none for
a hole. -/
structure ObservedArray (V : Type) where
  length : Nat
  element : Nat → Option V

/-- `publish` in `src/types/array.ts` writes nothing: the length reads as requested, each present
slot reads as its wanted value and no requested hole is own. -/
def arrayWriteFree (length : Nat) (want : Nat → Option V) (o : ObservedArray V) : Bool :=
  decide (o.length = length) && (List.range length).all fun i => decide (o.element i = want i)

/-- `matches` in `src/types/array.ts`: the length, the holes and every present value. -/
def arrayMatches (length : Nat) (want : Nat → Option V) (o : ObservedArray V) : Prop :=
  o.length = length ∧ ∀ i < length, (o.element i).isSome = (want i).isSome ∧
    ∀ v, want i = some v → o.element i = some v

/-- A write-free publication of an array is followed by an accepting readback. -/
theorem array_writeFree_matches (length : Nat) (want : Nat → Option V) (o : ObservedArray V)
    (h : arrayWriteFree length want o = true) : arrayMatches length want o := by
  simp only [arrayWriteFree, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨hlength, hall⟩ := h
  refine ⟨hlength, fun i hi => ?_⟩
  rw [hall i hi]
  exact ⟨rfl, fun _ h => h⟩

/-! ## Examples and counterexamples -/

-- Requested `[a, b]` over an object holding exactly them: write-free, and readback accepts.
example : objectWriteFree [0, 1] (fun _ => 7)
    ⟨[0, 1], fun _ => ⟨some (.data 7 plain), .none, true⟩⟩ = true := by decide

/-- Counterexample for alignment: a non-configurable key out of order needs no write, yet the
readback rejects the order, so write-freedom alone does not decide readback. -/
example : (([0, 1].all fun k => unchanged
      ((fun _ => (⟨some (.data 7 ⟨true, true, false⟩), .none, true⟩ : Slot Nat)) k) 7) = true) ∧
    alignedPrefix [1, 0] [0, 1] = false := by decide

/-- Counterexample for `Listed`: a key list that omits an own property hides a key from
readback's order check. -/
example : objectWriteFree [0] (fun _ => 7)
    ⟨[], fun _ => ⟨some (.data 7 plain), .none, true⟩⟩ = true ∧
    ¬ objectMatches [0] (fun _ => 7)
      ⟨[], fun _ => ⟨some (.data 7 plain), .none, true⟩⟩ := by
  exact ⟨by decide, fun h => absurd h.1 (by decide)⟩

end Reconcile.WriteFreeReadback
