import Property.PropertyWrite
import Graph.CollectionPlan
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

The premise is that reads are stable: with no write, no setter and no write trap has run, and the
getters and read traps the call runs change nothing it reads, so the readback would observe what
publication observed. The model takes one observation for both.

It also proves that publishing a key with what the call read of it before its first write equals
publishing with the live slot when the two agree (`publishKnown_eq`, `publishPre_eq`,
`publishSeen_eq`), and that a decision such a read made stale can only make the readback reject
(`accepts_readsAs`, `acceptsRetry_readsAs`).
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

/-! ## Deciding from the pre-write read

`reconcile` reads each value of `current` once before its first write: capture reads the value at
a key and the preflight its descriptor. Publication decides from that read whether the key needs a
write (`publishPre`) and acts on the live slot only to write it, so a getter of `current` runs once
when the call writes nothing. After any write, readback reads every key again, so a decision that a
write in between made stale can only reject the attempt (`accepts_readsAs`), never accept a wrong
result; the counterexample below is such a rejection. -/

/-- Publication of one key, decided from `pre`, the slot as read before the call's first write; a
write acts on `s`, the slot when publication reaches the key. -/
def publishPre (env : Env V) (pre s : Slot V) (v : V) (proto : Bool) : Outcome V :=
  match pre.own with
  | some own =>
    if read own = v then ⟨true, s, []⟩
    else match own with
      | .accessor .. => set env s v
      | .data _ a => assign env s v a
  | none => publish env s v proto

/-- With stable reads the pre-write slot is the live slot, and the decision is `publish`'s. -/
theorem publishPre_eq (env : Env V) (s : Slot V) (v : V) (proto : Bool) :
    publishPre env s s v proto = publish env s v proto := by
  unfold publishPre publish
  rcases s.own with _ | own <;> rfl

/-- A key whose pre-write read already holds the wanted value is not written. -/
theorem publishPre_unchanged (env : Env V) (pre s : Slot V) (v : V) (proto : Bool)
    (h : unchanged pre v = true) : publishPre env pre s v proto = ⟨true, s, []⟩ := by
  unfold unchanged at h
  unfold publishPre
  split at h
  · simp only [decide_eq_true_eq] at h
    simp [h]
  · cases h

/-- One key of an attempt: its slot before the call's first write, its slot when publication
reaches it, the wanted value and whether the key is `__proto__`. -/
structure Key (V : Type) where
  pre : Slot V
  live : Slot V
  want : V
  proto : Bool

/-- Whether publication writes the key: its pre-write read does not hold the wanted value. -/
def Key.writes (k : Key V) : Bool := !unchanged k.pre k.want

/-- The key's slot after its publication, which readback observes. -/
def Key.after (env : Env V) (k : Key V) : Slot V := (publishPre env k.pre k.live k.want k.proto).slot

/-- The engine accepts an attempt when every publication succeeded and, if any key was written,
every key reads back as wanted; when none was, it answers the readback without reading. -/
def accepts (env : Env V) (keys : List (Key V)) : Bool :=
  keys.all (fun k => (publishPre env k.pre k.live k.want k.proto).ok) &&
    (!keys.any Key.writes || keys.all fun k => readsAs (k.after env) k.want)

/-- Deciding from pre-write reads never accepts a wrong result. With no write, reads are stable (no
setter or write trap ran), so each key's live slot is its pre-write slot and reads as wanted; after
a write, readback checked every key. -/
theorem accepts_readsAs (env : Env V) (keys : List (Key V))
    (stable : keys.any Key.writes = false → ∀ k ∈ keys, k.live = k.pre)
    (h : accepts env keys = true) : ∀ k ∈ keys, readsAs (k.after env) k.want = true := by
  intro k hk
  simp only [accepts, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.all_eq_true] at h
  rcases h.2 with hnone | hall
  · have hw : k.writes = false := by
      rw [List.any_eq_false] at hnone
      simpa using hnone k hk
    have hu : unchanged k.pre k.want = true := by simpa [Key.writes] using hw
    have hafter : k.after env = k.live := by
      simp [Key.after, publishPre_unchanged env k.pre k.live k.want k.proto hu]
    rw [hafter, stable hnone k hk]
    exact unchanged_readsAs _ _ hu
  · exact hall k hk

/-! ## Later passes

A later pass of the engine publishes again after the call wrote, so its readback always reads. A
node whose previous readback matched held exactly the values the previous pass wanted there; the
later pass decides each of its keys from that value (`publishSeen`) instead of reading it again, so
each pass calls a getter of `current` once, at its readback. A decision a write in between made
stale can only reject the pass (`acceptsRetry_readsAs`). -/

/-- `writeProperty` in `src/types/shared/property-publication.ts`: `publish` once a read has shown
that the key needs a write, deciding by the live slot without reading its value again. -/
def write (env : Env V) (s : Slot V) (v : V) (proto : Bool) : Outcome V :=
  match s.own with
  | some (.accessor ..) => set env s v
  | some (.data _ a) => assign env s v a
  | none => if proto || inheritedAccessor s.inherited then define s v plain else assign env s v plain

/-- Publication of one key decided from `seen`, a value read earlier: skipped when that is the
wanted value and written on the live slot otherwise. A later pass decides each key of a node its
previous readback matched from what that readback saw, and an array's first publication each index
from what capture read. -/
def publishSeen (env : Env V) (seen : V) (s : Slot V) (v : V) (proto : Bool) : Outcome V :=
  if seen = v then ⟨true, s, []⟩ else write env s v proto

/-- With stable reads the live slot still reads as `seen`, and the decision is `publish`'s. -/
theorem publishSeen_eq (env : Env V) (seen : V) (s : Slot V) (v : V) (proto : Bool)
    (h : readsAs s seen = true) : publishSeen env seen s v proto = publish env s v proto := by
  unfold readsAs at h
  unfold publishSeen publish write
  split at h
  · rename_i own hown
    simp only [decide_eq_true_eq] at h
    subst h
    by_cases hv : read own = v
    · simp [hv]
    · simp only [hv, if_false, hown]
      cases own <;> rfl
  · cases h

/-- One key of a later pass: the value its previous readback saw, its slot when publication
reaches it, the wanted value and whether the key is `__proto__`. -/
structure SeenKey (V : Type) where
  seen : V
  live : Slot V
  want : V
  proto : Bool

/-- The key's slot after its publication in the later pass, which readback observes. -/
def SeenKey.after (env : Env V) (k : SeenKey V) : Slot V :=
  (publishSeen env k.seen k.live k.want k.proto).slot

/-- The engine accepts a later pass when every publication succeeded and every key reads back as
wanted: only a call's first publication can be answered without reading. -/
def acceptsRetry (env : Env V) (keys : List (SeenKey V)) : Bool :=
  keys.all (fun k => (publishSeen env k.seen k.live k.want k.proto).ok) &&
    keys.all fun k => readsAs (k.after env) k.want

/-- Deciding a later pass from the previous readback never accepts a wrong result, however stale. -/
theorem acceptsRetry_readsAs (env : Env V) (keys : List (SeenKey V))
    (h : acceptsRetry env keys = true) : ∀ k ∈ keys, readsAs (k.after env) k.want = true := by
  simp only [acceptsRetry, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2

/-! ## Native contents

A `Map`'s or `Set`'s entries are published by `CollectionPlan`. A `Date`'s time, a buffer's bytes,
a Temporal value and a `URL`'s or `URLSearchParams`'s text are compared whole, with the same
built-in reads at publication and at readback; that both compare alike is a runtime obligation, not
modelled here. -/

/-- A collection publication that left the entries as they were reached the next entries
(`CollectionPlan.plan_eq`), so readback, which compares them with the next entries, accepts. -/
theorem collection_writeFree_matches {α β : Type} [DecidableEq α] (cur next : List (α × β))
    (p : Nat) (hc : (CollectionPlan.keys cur).Nodup) (hn : (CollectionPlan.keys next).Nodup)
    (hp : CollectionPlan.keys (cur.take p) = CollectionPlan.keys (next.take p))
    (h : CollectionPlan.plan cur next p = cur) : cur = next := by
  rw [← h]
  exact CollectionPlan.plan_eq cur next p hc hn hp

/-! ## Examples and counterexamples -/

/-- Counterexample for deciding from the live slot: a key read as 7 before the first write and
changed to 8 by another key's setter is not written, and readback rejects the attempt, which a live
decision would have rewritten. The extra rejection is the price of one read. -/
example :
    unchanged (⟨some (.data 7 plain), .none, true⟩ : Slot Nat) 7 = true ∧
      readsAs (publishPre storing ⟨some (.data 7 plain), .none, true⟩
        ⟨some (.data 8 plain), .none, true⟩ 7 false).slot 7 = false ∧
      readsAs (publish storing ⟨some (.data 8 plain), .none, true⟩ 7 false).slot 7 = true := by
  decide

/-- Counterexample for deciding a later pass from the previous readback: it saw 7, another key's
setter changed the slot to 8, and the pass skips the key; readback rejects it. -/
example :
    readsAs (publishSeen storing 7 ⟨some (.data 8 plain), .none, true⟩ 7 false).slot 7 = false ∧
      readsAs (publish storing ⟨some (.data 8 plain), .none, true⟩ 7 false).slot 7 = true := by
  decide

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
