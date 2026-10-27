import Mathlib.Data.List.Perm.Subperm
import Property.PropertyPlacement
import Spec.Reconcile
import Spec.Produce

/-!
# The promises: theorems about the reference models

Each theorem states a promise the documentation makes, about the executable reference the random
differential bridge compares with the runtime. The bridge carries the promise to the runtime; the
theorem shows the reference keeps it on every input, not only the generated ones.

- `retainPrefix`, which is greedy matching (`PropertyPlacement.matched`): the retained prefix is a
  prefix of `next`'s order, a subsequence of `cur`'s, and the longest such prefix
  (`retainPrefix_prefix`, `retainPrefix_sublist`, `retainPrefix_longest`). The keys or entries
  outside it are the moves. The keys that cannot move lie in it exactly when some in-place
  placement keeps them, so the admission rule rejects only when no placement exists
  (`retainPrefix_feasible_iff`).
- `reconcile`: a getter of `current` runs at most once per decision pass beyond its first read,
  and at most once when no pass writes (`get_bound`, `read_once_before_write`).
- `reconcile` reads of `next`: a getter of an object only `next` holds runs at most once
  (`freshGets_le_one`), and the walks that keep subtrees in place run each getter at most once
  (`captureReads_once`). An object kept in place is neither written nor read back; read as
  `current`, its getters run at most once, only where it is another node's candidate
  (`run_pinned`).
- `reconcile` writes: a retained key is written exactly when its value differs, a moved or added
  key always (`objectWrites_set_iff`, `objectWrites_delete_iff`); an array index, a map or set
  entry, a date's time and a buffer's bytes likewise, and a view takes none
  (`arraySlotWrites_set_iff`, `arraySlotWrites_delete_iff`, `arraySlotWrites_length_iff`,
  `entryWrites_set_iff`, `entryWrites_delete_iff`, `entryWrites_fresh_iff`, `writesOf_date`,
  `writesOf_buffer`, `writesOf_view`). The write theorems name array slots and map and set keys
  structurally (`ArraySlot`, `EntryKey`), because a map or set write reports its key as text,
  which two distinct keys can share. No write reaches a slot that already holds `next`'s value
  (`objectWrites_unchanged`, `arraySlotWrites_unchanged`, `entryWrites_unchanged`), and a kept
  node takes no write exactly when its object already holds `next`'s contents
  (`writesOf_nil_iff`).
- `reconcile` descriptors: a kept object keeps the slot of every retained key, an accessor with
  its setter included, and the attributes of every moved key, and adds the rest writable and
  configurable with `next`'s enumerability (`keptObject_attrs`); under the static checks an own
  getter or setter is never moved, so it stays an accessor (`keptObject_accessor`).
- `reconcile` decisions: a decision keeps at an unpinned node only a candidate of it, the object
  at its position (`decide_candidate`), never a forbidden one, and only one that passes the
  static checks (`decide_checked`). Every decision of the passes keeps each current object at one
  node at most, given that `same` maps distinct pinned nodes to distinct objects
  (`decide_injective`, `demote_injective`), keeps a pinned node's object nowhere else
  (`demote_pinned`) and keeps candidates only (`demote_candidate`); so write minimality holds for
  the object every unpinned node keeps (`demote_writesOf_nil_iff`).
- `reconcile` passes: demotion forbids only an object whose writes block, reaching a fixed slot
  or a setter that drops its value (`mem_blockedObjects`), and never one an earlier pass forbade,
  so every pass that continues forbids a new current object (`blocked_fresh`). The passes number
  at most one more than the current objects, whatever the budget (`demote_length_le`,
  `passes_le_cur`, and `passes_le` per pair of nodes): no plan is searched. The budget never cuts
  them short, so a call that succeeds keeps no object whose writes block: such an object is
  replaced (`demote_last_unblocked`, `run_last_unblocked`).
- `reconcile` demands: no demand asks a candidate's own node for another object, so a requirement
  the candidate could never meet does not reorder that node's candidates (`demands_satisfiable`);
  a candidate whose fixed slots require two objects at one node, or another object at a pinned
  node, is not admitted, so it reorders no node (`admitted_pins`, `demands_pinned`).
- `reconcile` copies: a node that keeps nothing holds a copy (`Obj.copy`, as `snapshot` makes it)
  and its origin is none (`publish_origins`, `publish_fresh`).
- `produce`: a current object is kept exactly when its subtree is unchanged, and the kept set is
  the greatest such set (`kept_closed`, `kept_greatest`).
- `snapshot`: one copy per source node, every origin fresh (`snapshot_size`, `snapshot_copy`,
  `snapshot_fresh`).

Four counterexamples each show, on one input, a wrong definition that a theorem rules out:
retaining only the common prefix, reading back after a write-free pass, writing every key and
re-adding a moved key as plain data. Two examples show that `writesOf_nil_iff` needs distinct keys
and identities that keep each object at one node, three that `decide_injective` needs each of its
premises, and two that an object kept in place can run a getter twice while `next` is read when it
is also inside an object that refers to `current`, or also a `Map` value.
-/

namespace Reconcile.Spec.Reconcile

open Reconcile.Spec

/-! ## Retention -/

section Retention

variable {K : Type} [DecidableEq K]

/-- The retained prefix is a prefix of `next`'s order. -/
theorem retainPrefix_prefix (cur next : List K) : (retainPrefix cur next).IsPrefix next :=
  PropertyPlacement.matched_prefix next cur

/-- The retained prefix is a subsequence of `cur`'s order: nothing in it moves. -/
theorem retainPrefix_sublist (cur next : List K) : (retainPrefix cur next).Sublist cur :=
  PropertyPlacement.matched_sublist next cur

/-- No longer prefix of `next` is a subsequence of `cur`: every key or entry outside the retained
prefix must move, so the retained prefix rule makes the fewest moves among prefix rules. -/
theorem retainPrefix_longest (cur next : List K) (p : List K) (hp : p.IsPrefix next)
    (hs : p.Sublist cur) : p.length ≤ (retainPrefix cur next).length :=
  PropertyPlacement.matched_maximal next cur p hp hs

/-- Given keys that neither order repeats, the keys of `cur` that cannot move all lie in the
retained prefix exactly when some in-place placement, which keeps them in `cur`'s order and
appends every other key, reaches `next`'s order: the admission rule (`objectAdmits`) rejects an
object only when no placement exists. -/
theorem retainPrefix_feasible_iff (cur next fixed : List K) (hc : cur.Nodup) (hn : next.Nodup)
    (hf : ∀ k ∈ fixed, k ∈ cur) :
    PropertyPlacement.Feasible cur next fixed ↔ ∀ k ∈ fixed, k ∈ retainPrefix cur next :=
  PropertyPlacement.feasible_iff cur next fixed hn hc hf

/-- An order retains all of itself. -/
theorem retainPrefix_self (l : List K) : retainPrefix l l = l :=
  (retainPrefix_prefix l l).eq_of_length_le
    (retainPrefix_longest l l l (List.prefix_refl l) (List.Sublist.refl l))

/-- When neither order repeats a key and the retained prefix holds every key of both, the orders
are equal. -/
theorem retainPrefix_all {cur next : List K} (hc : cur.Nodup) (hn : next.Nodup)
    (h1 : ∀ k ∈ cur, k ∈ retainPrefix cur next) (h2 : ∀ k ∈ next, k ∈ retainPrefix cur next) :
    cur = next := by
  have hp := retainPrefix_prefix cur next
  have hs := retainPrefix_sublist cur next
  rw [← hp.eq_of_length_le (hn.subperm h2).length_le,
    hs.eq_of_length_le (hc.subperm h1).length_le]

/-- A rule that retains only the common prefix of the two orders. -/
def commonPrefix (cur next : List K) : List K :=
  (next.zip cur).takeWhile (fun (a, b) => a == b) |>.map Prod.fst

/-- Retaining only the common prefix breaks the promise: with `b` and `c` swapped, `a, c` is still
a subsequence of `current`'s order, so only `b` must move, but the common prefix stops at `a`. -/
example :
    retainPrefix ["a", "b", "c"] ["a", "c", "b"] = ["a", "c"] ∧
    commonPrefix ["a", "b", "c"] ["a", "c", "b"] = ["a"] := by
  decide

end Retention

/-! ## Trace -/

theorem getCounts_le (captured : List (Nat × String)) (readbacks : List (List (Nat × String))) :
    ∀ e ∈ getCounts captured readbacks, e.2.2 ≤ 1 + readbacks.length := by
  intro e he
  simp only [getCounts, List.mem_map] at he
  obtain ⟨⟨i, k⟩, _, rfl⟩ := he
  simp only
  have := List.length_filter_le (fun l : List (Nat × String) => l.contains (i, k)) readbacks
  split <;> omega

theorem getCounts_le_one (captured : List (Nat × String)) :
    ∀ e ∈ getCounts captured [], e.2.2 ≤ 1 := by
  intro e he
  have := getCounts_le captured [] e he
  simpa using this

/-- The getter counts of a run: none when the call is rejected or has nothing to do, else the
capture reads and one readback per pass, and none when no pass writes. -/
theorem run_gets (input : Input) : (run input).gets = [] ∨
    ∃ captured readbacks, readbacks.length ≤ (run input).passes ∧
      ((run input).allWrites = [] → readbacks = []) ∧
      (run input).gets = getCounts captured readbacks := by
  simp only [run]
  split
  · split
    · exact Or.inl rfl
    · simp only [publish]
      refine Or.inr ⟨_, _, ?_, ?_, rfl⟩
      · split <;> simp
      · intro hw
        rw [hw]
        rfl
  · exact Or.inl rfl

/-- A getter of `current` runs at most once when its object is read, and once per pass that reads
it back: twice in a call that writes and never demotes. -/
theorem get_bound (input : Input) : ∀ e ∈ (run input).gets, e.2.2 ≤ 1 + (run input).passes := by
  rcases run_gets input with h | ⟨captured, readbacks, hlen, _, h⟩ <;> rw [h]
  · simp
  · intro e he
    have := getCounts_le captured readbacks e he
    omega

/-- A call that writes nothing runs each getter of `current` at most once: it reads nothing back.
The name refers to that readback; `get_bound` bounds the getters of a call that writes. -/
theorem read_once_before_write (input : Input) (hw : (run input).allWrites = []) :
    ∀ e ∈ (run input).gets, e.2.2 ≤ 1 := by
  rcases run_gets input with h | ⟨captured, readbacks, _, hnil, h⟩ <;> rw [h]
  · simp
  · rw [hnil hw]
    exact getCounts_le_one _

/-- A trace that reads every captured key back even when nothing is written. -/
def getCountsAlwaysReadback (captured : List (Nat × String)) : List (Nat × String × Nat) :=
  getCounts captured [captured]

/-- Reading back after a write-free pass breaks the promise: the getter of key `a` on object 0
would run twice although nothing was written. -/
example : (getCountsAlwaysReadback [(0, "a")]).contains (0, "a", 2) = true ∧
    (getCounts [(0, "a")] []).contains (0, "a", 1) = true := by
  decide

/-! ## Writes -/

/-- Whether `next`'s slot `(k, ns)` is written into a kept object: a key the object lacks or that
moves is assigned, a retained key only when its value differs. -/
def written (identity : Nat → Option Nat) (cFields : List (String × Slot))
    (retained : List String) (k : String) (ns : Slot) : Bool :=
  match cFields.lookup k with
  | some cs => !retained.contains k || differs identity cs.value ns.value
  | none => true

/-- A key is set exactly when some slot of `next` at it is `written`: `reconcile` assigns a
changed, moved or added property and leaves an unchanged retained one alone. -/
theorem objectWrites_set_iff (identity : Nat → Option Nat)
    (cFields nFields : List (String × Slot)) (k : String) :
    (k, "set") ∈ (objectWrites identity cFields nFields).1 ↔
      ∃ ns, (k, ns) ∈ nFields ∧
        written identity cFields (retainPrefix (cFields.map Prod.fst) (nFields.map Prod.fst))
          k ns = true := by
  simp only [objectWrites, List.mem_append, List.mem_filterMap]
  constructor
  · rintro (⟨⟨k', cs⟩, _, h⟩ | ⟨⟨k', ns⟩, hmem, h⟩)
    · split at h
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact absurd h.2 (by decide)
    · refine ⟨ns, ?_, ?_⟩
      · split at h
        · split at h
          · split at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h
              exact h.1 ▸ hmem
            · simp at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            exact h.1 ▸ hmem
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact h.1 ▸ hmem
      · simp only [written]
        split at h
        · rename_i cs hcs
          split at h
          · rename_i hr
            split at h
            · rename_i hd
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              rw [← h.1, hcs]
              simp [hd]
            · simp at h
          · rename_i hr
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.1, hcs]
            simp only [List.contains_iff_mem] at hr
            simp [hr]
        · rename_i hcs
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1, hcs]
  · rintro ⟨ns, hmem, hw⟩
    refine Or.inr ⟨(k, ns), hmem, ?_⟩
    simp only [written] at hw
    split at hw
    · rename_i cs hcs
      simp only [hcs]
      split
      · rename_i hr
        simp only [hr, Bool.not_true, Bool.false_or] at hw
        simp [hw]
      · rfl
    · rename_i hcs
      simp only [hcs]

theorem exists_lookup_of_mem {k : String} {fields : List (String × Slot)}
    (h : k ∈ fields.map Prod.fst) : ∃ cs, fields.lookup k = some cs := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
  exact Option.isSome_iff_exists.mp (List.lookup_isSome_iff.mpr ⟨p, hp, by simp⟩)

/-- A key of a kept object is deleted exactly when the object has it and it is not both a key of
`next` and retained: a moved key is deleted and set again. -/
theorem objectWrites_delete_iff (identity : Nat → Option Nat)
    (cFields nFields : List (String × Slot)) (k : String) :
    (k, "delete") ∈ (objectWrites identity cFields nFields).1 ↔
      k ∈ cFields.map Prod.fst ∧
        ¬(k ∈ nFields.map Prod.fst ∧
          k ∈ retainPrefix (cFields.map Prod.fst) (nFields.map Prod.fst)) := by
  simp only [objectWrites, List.mem_append, List.mem_filterMap]
  constructor
  · rintro (⟨⟨k', cs⟩, hmem, h⟩ | ⟨⟨k', ns⟩, _, h⟩)
    · split at h
      · simp at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        refine ⟨List.mem_map.mpr ⟨_, hmem, rfl⟩, ?_⟩
        simpa using hc
    · split at h
      · split at h
        · split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            exact absurd h.2 (by decide)
          · simp at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact absurd h.2 (by decide)
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact absurd h.2 (by decide)
  · rintro ⟨hk, hn⟩
    obtain ⟨⟨k', cs⟩, hmem, rfl⟩ := List.mem_map.mp hk
    refine Or.inl ⟨(k', cs), hmem, ?_⟩
    rw [if_neg (by simpa using hn)]

/-- No write reaches a key that already holds `next`'s value: a retained key whose value does not
differ under the identities is neither set nor deleted. -/
theorem objectWrites_unchanged (identity : Nat → Option Nat)
    (cFields nFields : List (String × Slot)) (k : String)
    (hr : k ∈ retainPrefix (cFields.map Prod.fst) (nFields.map Prod.fst))
    (hv : ∀ ns, (k, ns) ∈ nFields → ∀ cs, cFields.lookup k = some cs →
      differs identity cs.value ns.value = false) :
    (k, "set") ∉ (objectWrites identity cFields nFields).1 ∧
      (k, "delete") ∉ (objectWrites identity cFields nFields).1 := by
  constructor
  · intro h
    obtain ⟨ns, hmem, hw⟩ := (objectWrites_set_iff identity cFields nFields k).mp h
    obtain ⟨cs, hcs⟩ := exists_lookup_of_mem ((retainPrefix_sublist _ _).subset hr)
    simp only [written, hcs, List.contains_eq_mem, hv ns hmem cs hcs, Bool.or_false,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hw
    exact hw hr
  · intro h
    have := (objectWrites_delete_iff identity cFields nFields k).mp h
    exact this.2 ⟨(retainPrefix_prefix _ _).subset hr, hr⟩

/-- A kept object, neither of whose key lists repeats a key, takes no write exactly when it
already lists `next`'s keys in order, each with a value that does not differ. -/
theorem objectWrites_nil_iff (identity : Nat → Option Nat)
    (cFields nFields : List (String × Slot)) (hc : (cFields.map Prod.fst).Nodup)
    (hn : (nFields.map Prod.fst).Nodup) :
    (objectWrites identity cFields nFields).1 = [] ↔
      cFields.map Prod.fst = nFields.map Prod.fst ∧
        ∀ p ∈ nFields, ∀ cs, cFields.lookup p.1 = some cs →
          differs identity cs.value p.2.value = false := by
  simp only [objectWrites, List.append_eq_nil_iff, List.filterMap_eq_nil_iff]
  constructor
  · rintro ⟨hd, hs⟩
    have hsk : ∀ p ∈ nFields, ∃ cs, cFields.lookup p.1 = some cs ∧
        p.1 ∈ retainPrefix (cFields.map Prod.fst) (nFields.map Prod.fst) ∧
        differs identity cs.value p.2.value = false := by
      intro ⟨k, ns⟩ hp
      have := hs (k, ns) hp
      simp only at this
      split at this
      · rename_i cs hcs
        split at this
        · rename_i hr
          split at this
          · simp at this
          · rename_i hd'
            exact ⟨cs, hcs, by simpa using hr, by simpa using hd'⟩
        · simp at this
      · simp at this
    have hkeys : cFields.map Prod.fst = nFields.map Prod.fst := by
      apply retainPrefix_all hc hn
      · intro k hk
        obtain ⟨⟨k', cs⟩, hp, rfl⟩ := List.mem_map.mp hk
        have := hd (k', cs) hp
        simp only at this
        split at this
        · rename_i h
          simp only [Bool.and_eq_true, List.contains_iff_mem] at h
          exact h.2
        · simp at this
      · intro k hk
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
        obtain ⟨_, _, hr, _⟩ := hsk p hp
        exact hr
    refine ⟨hkeys, fun p hp cs hcs => ?_⟩
    obtain ⟨cs', hcs', _, hd'⟩ := hsk p hp
    rw [hcs] at hcs'
    cases hcs'
    exact hd'
  · rintro ⟨hkeys, hv⟩
    have hr : retainPrefix (cFields.map Prod.fst) (nFields.map Prod.fst) =
        nFields.map Prod.fst := by
      rw [hkeys, retainPrefix_self]
    constructor
    · intro ⟨k, cs⟩ hp
      have hk : k ∈ nFields.map Prod.fst := hkeys ▸ List.mem_map.mpr ⟨_, hp, rfl⟩
      simp only [hr, List.contains_iff_mem, hk, Bool.and_self, if_true]
    · intro ⟨k, ns⟩ hp
      have hk : k ∈ cFields.map Prod.fst := hkeys ▸ List.mem_map.mpr ⟨_, hp, rfl⟩
      obtain ⟨cs, hcs⟩ := exists_lookup_of_mem hk
      have hk' : k ∈ nFields.map Prod.fst := List.mem_map.mpr ⟨_, hp, rfl⟩
      simp only [hcs, hr, List.contains_iff_mem, hk', if_true]
      rw [if_neg (by simpa using hv (k, ns) hp cs hcs)]

/-- Whether a slot holding `c` already holds `next`'s `n` under the identities: both are empty,
or both hold values that do not differ. -/
def slotHolds (identity : Nat → Option Nat) : Option Val → Option Val → Bool
  | none, none => true
  | some cv, some nv => !differs identity cv nv
  | _, _ => false

/-- The writes a kept array's index takes: a set where `next` has an element that the array lacks
or holds differently under the identities, and a deletion where `next` has a hole below its
length and the array an element. -/
theorem mem_arraySlotWrites_index (identity : Nat → Option Nat) (ce ne : List (Option Val))
    (i : Nat) (w : String) :
    (ArraySlot.index i, w) ∈ arraySlotWrites identity ce ne ↔
      (w = "set" ∧ ∃ nv, ne[i]?.bind id = some nv ∧
        (ce[i]?.bind id = none ∨ ∃ cv, ce[i]?.bind id = some cv ∧ differs identity cv nv = true)) ∨
      (w = "delete" ∧ i < ne.length ∧ ne[i]?.bind id = none ∧ (ce[i]?.bind id).isSome) := by
  simp only [arraySlotWrites, List.mem_append, List.mem_filterMap, List.mem_range]
  constructor
  · rintro (h | ⟨j, hj, hf⟩)
    · split at h <;> simp at h
    · split at hf
      · rename_i cv nv hc hn
        split at hf
        · rename_i hd
          simp only [Option.some.injEq, Prod.mk.injEq, ArraySlot.index.injEq] at hf
          obtain ⟨rfl, rfl⟩ := hf
          exact Or.inl ⟨rfl, nv, hn, Or.inr ⟨cv, hc, hd⟩⟩
        · simp at hf
      · rename_i nv hc hn
        simp only [Option.some.injEq, Prod.mk.injEq, ArraySlot.index.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        exact Or.inl ⟨rfl, nv, hn, Or.inl hc⟩
      · rename_i cv hc hn
        split at hf
        · rename_i hl
          simp only [Option.some.injEq, Prod.mk.injEq, ArraySlot.index.injEq] at hf
          obtain ⟨rfl, rfl⟩ := hf
          exact Or.inr ⟨rfl, hl, hn, by simp [hc]⟩
        · simp at hf
      · simp at hf
  · rintro (⟨rfl, nv, hn, hc⟩ | ⟨rfl, hl, hn, hc⟩)
    · refine Or.inr ⟨i, ?_, ?_⟩
      · have : i < ne.length := by
          cases h : ne[i]? with
          | none => simp [h] at hn
          | some _ => exact (List.getElem?_eq_some_iff.mp h).1
        omega
      · rcases hc with hc | ⟨cv, hc, hd⟩
        · simp [hc, hn]
        · simp [hc, hn, hd]
    · refine Or.inr ⟨i, by omega, ?_⟩
      obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.mp hc
      rw [hcv, hn]
      simp [hl]

/-- An index of a kept array is set exactly when `next` has an element there and the array lacks
one or holds a different one under the identities. -/
theorem arraySlotWrites_set_iff (identity : Nat → Option Nat) (ce ne : List (Option Val))
    (i : Nat) :
    (ArraySlot.index i, "set") ∈ arraySlotWrites identity ce ne ↔
      ∃ nv, ne[i]?.bind id = some nv ∧
        (ce[i]?.bind id = none ∨ ∃ cv, ce[i]?.bind id = some cv ∧ differs identity cv nv = true) := by
  rw [mem_arraySlotWrites_index]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact h
    · exact absurd h (by decide)
  · intro h
    exact Or.inl ⟨rfl, h⟩

/-- An index of a kept array is deleted exactly when `next` has a hole there below its length and
the array an element. -/
theorem arraySlotWrites_delete_iff (identity : Nat → Option Nat) (ce ne : List (Option Val))
    (i : Nat) :
    (ArraySlot.index i, "delete") ∈ arraySlotWrites identity ce ne ↔
      i < ne.length ∧ ne[i]?.bind id = none ∧ (ce[i]?.bind id).isSome := by
  rw [mem_arraySlotWrites_index]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · exact absurd h (by decide)
    · exact h
  · intro h
    exact Or.inr ⟨rfl, h⟩

/-- A kept array's length is set exactly when the lengths differ. -/
theorem arraySlotWrites_length_iff (identity : Nat → Option Nat) (ce ne : List (Option Val)) :
    (ArraySlot.length, "set") ∈ arraySlotWrites identity ce ne ↔ ce.length ≠ ne.length := by
  simp only [arraySlotWrites, List.mem_append, List.mem_filterMap]
  constructor
  · rintro (h | ⟨j, _, hf⟩)
    · split at h <;> simp_all
    · exfalso
      split at hf <;> (try split at hf) <;> simp at hf
  · intro h
    left
    simp [h]

/-- No write reaches an index that already holds `next`'s element, or `next`'s hole. -/
theorem arraySlotWrites_unchanged (identity : Nat → Option Nat) (ce ne : List (Option Val))
    (i : Nat) (h : slotHolds identity (ce[i]?.bind id) (ne[i]?.bind id) = true) :
    (ArraySlot.index i, "set") ∉ arraySlotWrites identity ce ne ∧
      (ArraySlot.index i, "delete") ∉ arraySlotWrites identity ce ne := by
  rw [arraySlotWrites_set_iff, arraySlotWrites_delete_iff]
  constructor
  · rintro ⟨nv, hn, hc | ⟨cv, hc, hd⟩⟩ <;> simp_all [slotHolds]
  · rintro ⟨_, hn, hc⟩
    obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.mp hc
    simp [hn, hcv, slotHolds] at h

/-- A kept array takes no write exactly when it already has `next`'s length and, at every index,
`next`'s element or hole. -/
theorem arraySlotWrites_nil_iff (identity : Nat → Option Nat) (ce ne : List (Option Val)) :
    arraySlotWrites identity ce ne = [] ↔
      ce.length = ne.length ∧
        ∀ i : Nat, slotHolds identity (ce[i]?.bind id) (ne[i]?.bind id) = true := by
  simp only [arraySlotWrites, List.append_eq_nil_iff, List.filterMap_eq_nil_iff, List.mem_range]
  constructor
  · rintro ⟨hl, hi⟩
    have hlen : ce.length = ne.length := by
      split at hl
      · assumption
      · simp at hl
    refine ⟨hlen, fun i => ?_⟩
    by_cases hlt : i < ne.length
    · have := hi i (by omega)
      revert this
      cases hc : ce[i]?.bind id <;> cases hn : ne[i]?.bind id <;> simp [slotHolds, hlt]
    · have h1 : ce[i]? = none := List.getElem?_eq_none (by omega)
      have h2 : ne[i]? = none := List.getElem?_eq_none (by omega)
      simp [h1, h2, slotHolds]
  · rintro ⟨hlen, hs⟩
    refine ⟨by simp [hlen], fun i hi => ?_⟩
    have := hs i
    have hlt : i < ne.length := by omega
    revert this
    cases hc : ce[i]?.bind id <;> cases hn : ne[i]?.bind id <;> simp [slotHolds, hlt]

/-- The writes a kept map or set takes: a current key is deleted when it is not both a key of
`next` and retained; it is set when a key of `next` stands for it and it is not retained or its
value differs; a key of `next` that is a fresh node is set. -/
theorem mem_entryWrites (identity : Nat → Option Nat) (cKeys nKeys : List Val)
    (cValue nValue : Val → Option Val) (key : EntryKey) (w : String) :
    (key, w) ∈ entryWrites identity cKeys nKeys cValue nValue ↔
      (∃ ck, key = .current ck ∧ w = "delete" ∧ ck ∈ cKeys ∧
        ¬(some ck ∈ nKeys.map (resolveKey identity) ∧
          some ck ∈ retainPrefix (cKeys.map some) (nKeys.map (resolveKey identity)))) ∨
      (∃ ck, key = .current ck ∧ w = "set" ∧ ∃ k ∈ nKeys, resolveKey identity k = some ck ∧
        (some ck ∉ retainPrefix (cKeys.map some) (nKeys.map (resolveKey identity)) ∨
          ∃ cv nv, cValue ck = some cv ∧ nValue k = some nv ∧ differs identity cv nv = true)) ∨
      (∃ k, key = .fresh k ∧ w = "set" ∧ k ∈ nKeys ∧ resolveKey identity k = none) := by
  simp only [entryWrites, List.mem_append, List.mem_filterMap]
  constructor
  · rintro (⟨ck, hmem, h⟩ | ⟨k, hmem, h⟩)
    · split at h
      · simp at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine Or.inl ⟨ck, rfl, rfl, hmem, ?_⟩
        simpa using hc
    · split at h
      · rename_i ck hres
        split at h
        · rename_i hr
          split at h
          · rename_i cv nv hcv hnv
            split at h
            · rename_i hd
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact Or.inr (Or.inl ⟨ck, rfl, rfl, k, hmem, hres, Or.inr ⟨cv, nv, hcv, hnv, hd⟩⟩)
            · simp at h
          · simp at h
        · rename_i hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Or.inr (Or.inl ⟨ck, rfl, rfl, k, hmem, hres, Or.inl (by simpa using hr)⟩)
      · rename_i hres
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inr (Or.inr ⟨k, rfl, rfl, hmem, hres⟩)
  · rintro (⟨ck, rfl, rfl, hmem, hn⟩ | ⟨ck, rfl, rfl, k, hmem, hres, hw⟩ |
      ⟨k, rfl, rfl, hmem, hres⟩)
    · refine Or.inl ⟨ck, hmem, ?_⟩
      rw [if_neg (by simpa using hn)]
    · refine Or.inr ⟨k, hmem, ?_⟩
      simp only [hres]
      rcases hw with hr | ⟨cv, nv, hcv, hnv, hd⟩
      · rw [if_neg (by simpa using hr)]
      · split
        · simp [hcv, hnv, hd]
        · rfl
    · refine Or.inr ⟨k, hmem, ?_⟩
      simp only [hres]

/-- A current key of a kept map or set is set exactly when a key of `next` stands for it and it
is not in the retained prefix or its value differs. -/
theorem entryWrites_set_iff (identity : Nat → Option Nat) (cKeys nKeys : List Val)
    (cValue nValue : Val → Option Val) (ck : Val) :
    (EntryKey.current ck, "set") ∈ entryWrites identity cKeys nKeys cValue nValue ↔
      ∃ k ∈ nKeys, resolveKey identity k = some ck ∧
        (some ck ∉ retainPrefix (cKeys.map some) (nKeys.map (resolveKey identity)) ∨
          ∃ cv nv, cValue ck = some cv ∧ nValue k = some nv ∧ differs identity cv nv = true) := by
  rw [mem_entryWrites]
  constructor
  · rintro (⟨_, _, h, _⟩ | ⟨_, h1, _, h⟩ | ⟨_, h, _⟩)
    · exact absurd h (by decide)
    · cases h1
      exact h
    · cases h
  · intro h
    exact Or.inr (Or.inl ⟨ck, rfl, rfl, h⟩)

/-- A key of a kept map or set is deleted exactly when the collection has it and it is not both a
key of `next` and retained. -/
theorem entryWrites_delete_iff (identity : Nat → Option Nat) (cKeys nKeys : List Val)
    (cValue nValue : Val → Option Val) (ck : Val) :
    (EntryKey.current ck, "delete") ∈ entryWrites identity cKeys nKeys cValue nValue ↔
      ck ∈ cKeys ∧ ¬(some ck ∈ nKeys.map (resolveKey identity) ∧
        some ck ∈ retainPrefix (cKeys.map some) (nKeys.map (resolveKey identity))) := by
  rw [mem_entryWrites]
  constructor
  · rintro (⟨_, h1, _, h⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩)
    · cases h1
      exact h
    · exact absurd h (by decide)
    · cases h
  · intro h
    exact Or.inl ⟨ck, rfl, rfl, h⟩

/-- A key of `next` that is a fresh node is always set: its object is no current key. -/
theorem entryWrites_fresh_iff (identity : Nat → Option Nat) (cKeys nKeys : List Val)
    (cValue nValue : Val → Option Val) (k : Val) :
    (EntryKey.fresh k, "set") ∈ entryWrites identity cKeys nKeys cValue nValue ↔
      k ∈ nKeys ∧ resolveKey identity k = none := by
  rw [mem_entryWrites]
  constructor
  · rintro (⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h1, _, h⟩)
    · cases h
    · cases h
    · cases h1
      exact h
  · intro h
    exact Or.inr (Or.inr ⟨k, rfl, rfl, h⟩)

/-- No write reaches an entry that already holds `next`'s: a retained key whose value does not
differ is neither set nor deleted. -/
theorem entryWrites_unchanged (identity : Nat → Option Nat) (cKeys nKeys : List Val)
    (cValue nValue : Val → Option Val) (ck : Val)
    (hr : some ck ∈ retainPrefix (cKeys.map some) (nKeys.map (resolveKey identity)))
    (hv : ∀ k ∈ nKeys, resolveKey identity k = some ck → ∀ cv nv, cValue ck = some cv →
      nValue k = some nv → differs identity cv nv = false) :
    (EntryKey.current ck, "set") ∉ entryWrites identity cKeys nKeys cValue nValue ∧
      (EntryKey.current ck, "delete") ∉ entryWrites identity cKeys nKeys cValue nValue := by
  rw [entryWrites_set_iff, entryWrites_delete_iff]
  constructor
  · rintro ⟨k, hk, hres, hw | ⟨cv, nv, hcv, hnv, hd⟩⟩
    · exact hw hr
    · rw [hv k hk hres cv nv hcv hnv] at hd
      exact absurd hd (by decide)
  · rintro ⟨_, hn⟩
    exact hn ⟨(retainPrefix_prefix _ _).subset hr, hr⟩

theorem resolveKey_inj {identity : Nat → Option Nat}
    (hinj : ∀ a b x, identity a = some x → identity b = some x → a = b) {k k' ck : Val}
    (h : resolveKey identity k = some ck) (h' : resolveKey identity k' = some ck) : k = k' := by
  cases k with
  | prim p =>
    cases k' with
    | prim q =>
      simp only [resolveKey, Option.some.injEq] at h h'
      rw [← h'] at h
      cases h
      rfl
    | ref c =>
      simp only [resolveKey, Option.some.injEq, Option.map_eq_some_iff] at h h'
      obtain ⟨x, _, rfl⟩ := h'
      cases h
  | ref c =>
    cases k' with
    | prim q =>
      simp only [resolveKey, Option.some.injEq, Option.map_eq_some_iff] at h h'
      obtain ⟨x, _, rfl⟩ := h
      cases h'
    | ref d =>
      simp only [resolveKey, Option.map_eq_some_iff] at h h'
      obtain ⟨x, hx, rfl⟩ := h
      obtain ⟨y, hy, hxy⟩ := h'
      cases hxy
      rw [hinj c d x hx hy]

/-- Whether a map or set with keys `cKeys` already holds `next`'s: `next`'s keys, resolved under
the identities, are the current keys in order, and no value differs. -/
def collectionHolds (identity : Nat → Option Nat) (cKeys nKeys : List Val)
    (cValue nValue : Val → Option Val) : Prop :=
  nKeys.map (resolveKey identity) = cKeys.map some ∧
    ∀ k ∈ nKeys, ∀ ck cv nv, resolveKey identity k = some ck → cValue ck = some cv →
      nValue k = some nv → differs identity cv nv = false

/-- A kept map or set takes no write exactly when it already holds `next`'s entries, given
distinct keys on both sides and identities that keep each object at one node at most. -/
theorem entryWrites_nil_iff (identity : Nat → Option Nat) (cKeys nKeys : List Val)
    (cValue nValue : Val → Option Val) (hc : cKeys.Nodup) (hn : nKeys.Nodup)
    (hinj : ∀ a b x, identity a = some x → identity b = some x → a = b) :
    entryWrites identity cKeys nKeys cValue nValue = [] ↔
      collectionHolds identity cKeys nKeys cValue nValue := by
  simp only [entryWrites, List.append_eq_nil_iff, List.filterMap_eq_nil_iff]
  constructor
  · rintro ⟨hd, hs⟩
    have hsk : ∀ k ∈ nKeys, ∃ ck, resolveKey identity k = some ck ∧
        some ck ∈ retainPrefix (cKeys.map some) (nKeys.map (resolveKey identity)) ∧
        ∀ cv nv, cValue ck = some cv → nValue k = some nv → differs identity cv nv = false := by
      intro k hk
      have := hs k hk
      split at this
      · rename_i ck hres
        split at this
        · rename_i hr
          refine ⟨ck, hres, by simpa using hr, fun cv nv hcv hnv => ?_⟩
          rw [hcv, hnv] at this
          simpa using this
        · simp at this
      · simp at this
    have hkeys : cKeys.map some = nKeys.map (resolveKey identity) := by
      apply retainPrefix_all
      · exact List.Pairwise.map _ (fun a b h e => h (Option.some.inj e)) hc
      · rw [List.Nodup, List.pairwise_map]
        refine List.Pairwise.imp_of_mem (fun ha _ hne heq => ?_) hn
        obtain ⟨ca, hra, -, -⟩ := hsk _ ha
        exact hne (resolveKey_inj hinj hra (heq ▸ hra))
      · intro x hx
        obtain ⟨ck, hck, rfl⟩ := List.mem_map.mp hx
        have := hd ck hck
        split at this
        · rename_i h
          simp only [Bool.and_eq_true, List.contains_iff_mem] at h
          exact h.2
        · simp at this
      · intro x hx
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
        obtain ⟨ck, hres, hr, -⟩ := hsk k hk
        rw [hres]
        exact hr
    refine ⟨hkeys.symm, fun k hk ck cv nv hres hcv hnv => ?_⟩
    obtain ⟨ck', hres', -, hv⟩ := hsk k hk
    rw [hres] at hres'
    cases hres'
    exact hv cv nv hcv hnv
  · rintro ⟨hkeys, hv⟩
    have hr : retainPrefix (cKeys.map some) (nKeys.map (resolveKey identity)) =
        nKeys.map (resolveKey identity) := by
      rw [hkeys, retainPrefix_self]
    constructor
    · intro ck hck
      have hm : some ck ∈ nKeys.map (resolveKey identity) :=
        hkeys ▸ List.mem_map.mpr ⟨ck, hck, rfl⟩
      simp only [hr, List.contains_iff_mem, hm, Bool.and_self, if_true]
    · intro k hk
      have hmem : resolveKey identity k ∈ cKeys.map some :=
        hkeys ▸ List.mem_map.mpr ⟨k, hk, rfl⟩
      obtain ⟨ck, _, hres⟩ := List.mem_map.mp hmem
      have hm : some ck ∈ nKeys.map (resolveKey identity) := List.mem_map.mpr ⟨k, hk, hres.symm⟩
      simp only [← hres, hr, List.contains_iff_mem, hm, if_true]
      split
      · rename_i cv nv hcv hnv
        rw [if_neg (by simpa using hv k hk ck cv nv hres.symm hcv hnv)]
      · rfl

/-- A kept date sets its time exactly when the times differ. -/
theorem writesOf_date (identity : Nat → Option Nat) (cms nms : Int) :
    ("time", "set") ∈ (writesOf identity (.date cms) (.date nms)).1 ↔ cms ≠ nms := by
  simp only [writesOf]
  split <;> simp_all

/-- A kept buffer sets its bytes exactly when the bytes differ. -/
theorem writesOf_buffer (identity : Nat → Option Nat) (cb nb : List Nat) (cm nm : Option Nat) :
    ("bytes", "set") ∈ (writesOf identity (.buffer cb cm) (.buffer nb nm)).1 ↔ cb ≠ nb := by
  simp only [writesOf]
  split <;> simp_all

/-- A kept view takes no write: the decision keeps it only with `next`'s constructor, offset and
length, and its buffer is a fixed slot. -/
theorem writesOf_view (identity : Nat → Option Nat) (cc nc : String) (cb nb : Val)
    (co cl no nl : Nat) :
    (writesOf identity (.view cc cb co cl) (.view nc nb no nl)).1 = [] := rfl

/-- Whether current object `c` already holds `next`'s contents `n` under the identities: an object
`next`'s keys in order, with no value differing; an array `next`'s length and, at every index,
`next`'s element or hole; a map or set `collectionHolds`; a date `next`'s time; a buffer `next`'s
bytes; a view `next`'s constructor, offset and length. -/
def holds (identity : Nat → Option Nat) : Obj → Obj → Prop
  | .object _ cf _, .object _ nf _ =>
    cf.map Prod.fst = nf.map Prod.fst ∧
      ∀ p ∈ nf, ∀ cs, cf.lookup p.1 = some cs → differs identity cs.value p.2.value = false
  | .array ce _, .array ne _ =>
    ce.length = ne.length ∧
      ∀ i : Nat, slotHolds identity (ce[i]?.bind id) (ne[i]?.bind id) = true
  | .map ce, .map ne =>
    collectionHolds identity (ce.map Prod.fst) (ne.map Prod.fst) (ce.lookup ·) (ne.lookup ·)
  | .set cm, .set nm => collectionHolds identity cm nm (fun _ => none) (fun _ => none)
  | .date cms, .date nms => cms = nms
  | .buffer cb _, .buffer nb _ => cb = nb
  | .view cc _ co cl, .view nc _ no nl => cc = nc ∧ co = no ∧ cl = nl
  | _, _ => False

/-- Whether neither node repeats a key: an object's keys, a map's keys, a set's members. -/
def distinctKeys : Obj → Obj → Prop
  | .object _ cf _, .object _ nf _ => (cf.map Prod.fst).Nodup ∧ (nf.map Prod.fst).Nodup
  | .map ce, .map ne => (ce.map Prod.fst).Nodup ∧ (ne.map Prod.fst).Nodup
  | .set cm, .set nm => cm.Nodup ∧ nm.Nodup
  | _, _ => True

/-- A kept node's write list is empty exactly when its object already holds `next`'s contents
under the identities, for every kind. The node passes the static checks, as every kept node does;
neither side repeats a key; and the identities keep each object at one node at most, as a
decision does. -/
theorem writesOf_nil_iff (classes : Array (List (String × Slot))) (identity : Nat → Option Nat)
    (c n : Obj) (hadm : admitsStatic classes c n = true) (hkeys : distinctKeys c n)
    (hinj : ∀ a b x, identity a = some x → identity b = some x → a = b) :
    (writesOf identity c n).1 = [] ↔ holds identity c n := by
  cases c <;> cases n <;> simp only [admitsStatic, Bool.false_eq_true] at hadm
  case object.object => exact objectWrites_nil_iff identity _ _ hkeys.1 hkeys.2
  case array.array =>
    simp only [writesOf, holds, arrayWrites, List.map_eq_nil_iff]
    exact arraySlotWrites_nil_iff identity _ _
  case map.map =>
    simp only [writesOf, holds, collectionWrites, List.map_eq_nil_iff]
    exact entryWrites_nil_iff identity _ _ _ _ hkeys.1 hkeys.2 hinj
  case set.set =>
    simp only [writesOf, holds, collectionWrites, List.map_eq_nil_iff]
    exact entryWrites_nil_iff identity _ _ _ _ hkeys.1 hkeys.2 hinj
  case date.date =>
    simp only [writesOf, holds]
    split <;> simp_all
  case buffer.buffer =>
    simp only [writesOf, holds]
    split <;> simp_all
  case view.view =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hadm
    simp [writesOf, holds, hadm]

/-! ### Examples of writes by kind

Each example shows a kept node that takes no write and one that does. A map's or set's write
reports its key as text, which can repeat for distinct keys; `entryWrites` keeps them apart. -/

section WriteExamples

private def num (n : Int) : Val := .prim (.num n)
private def str (t : String) : Val := .prim (.str t)

example :
    (writesOf (fun _ => none) (.object .object [("a", .data (num 1) Attrs.plain)] true)
      (.object .object [("a", .data (num 1) Attrs.plain)] true)).1 = [] ∧
    (writesOf (fun _ => none) (.object .object [("a", .data (num 1) Attrs.plain)] true)
      (.object .object [("a", .data (num 2) Attrs.plain)] true)).1 = [("a", "set")] := by
  decide

example :
    arraySlotWrites (fun _ => none) [some (num 1), some (num 2)] [some (num 1), some (num 2)] =
      [] ∧
    arraySlotWrites (fun _ => none) [some (num 1), some (num 2)] [some (num 1), some (num 3)] =
      [(.index 1, "set")] ∧
    arraySlotWrites (fun _ => none) [some (num 1), some (num 2)] [some (num 1), none] =
      [(.index 1, "delete")] ∧
    arraySlotWrites (fun _ => none) [some (num 1), some (num 2)] [some (num 1)] =
      [(.length, "set")] ∧
    arrayWrites (fun _ => none) [some (num 1), some (num 2)] [some (num 1), none] =
      [("1", "delete")] := by
  decide

example :
    (writesOf (fun _ => none) (.map [(str "a", num 1), (str "b", num 2)])
      (.map [(str "a", num 1), (str "b", num 2)])).1 = [] ∧
    (writesOf (fun _ => none) (.map [(str "a", num 1), (str "b", num 2)])
      (.map [(str "a", num 1), (str "b", num 3)])).1 = [("b", "set")] ∧
    (writesOf (fun _ => none) (.map [(str "a", num 1), (str "b", num 2)])
      (.map [(str "b", num 2), (str "a", num 1)])).1 = [("a", "delete"), ("a", "set")] := by
  decide

example :
    (writesOf (fun _ => none) (.set [str "a"]) (.set [str "a"])).1 = [] ∧
    (writesOf (fun _ => none) (.set [str "a"]) (.set [str "b"])).1 =
      [("a", "delete"), ("b", "set")] := by
  decide

/-- A member of `next` that is a node stands for the object the node keeps, and a fresh node's
object is always added. -/
example :
    entryWrites (fun j => if j = 0 then some 3 else none) [.ref 3] [.ref 0] (fun _ => none)
      (fun _ => none) = [] ∧
    entryWrites (fun _ => none) [.ref 3] [.ref 0] (fun _ => none) (fun _ => none) =
      [(.current (.ref 3), "delete"), (.fresh (.ref 0), "set")] := by
  decide

/-- The string `"ref 3"` and a reference to object 3 are distinct keys with one text. -/
example :
    entryWrites (fun _ => none) [.ref 3] [str "ref 3"] (fun _ => none) (fun _ => none) =
      [(.current (.ref 3), "delete"), (.current (str "ref 3"), "set")] ∧
    collectionWrites (fun _ => none) [.ref 3] [str "ref 3"] (fun _ => none) (fun _ => none) =
      [("ref 3", "delete"), ("ref 3", "set")] := by
  decide

example :
    (writesOf (fun _ => none) (.date 1) (.date 1)).1 = [] ∧
    (writesOf (fun _ => none) (.date 1) (.date 2)).1 = [("time", "set")] := by
  decide

example :
    (writesOf (fun _ => none) (.buffer [1, 2] none) (.buffer [1, 2] none)).1 = [] ∧
    (writesOf (fun _ => none) (.buffer [1, 2] none) (.buffer [1, 3] none)).1 =
      [("bytes", "set")] := by
  decide

/-- A view never takes a write, whatever buffer reference `next` holds. -/
example :
    (writesOf (fun _ => none) (.view "Uint8Array" (.ref 0) 0 2)
      (.view "Uint8Array" (.ref 1) 0 2)).1 = [] := by
  decide

/-- `writesOf_nil_iff` needs distinct keys: a `next` that repeats a key the object holds unchanged
needs no write, yet its key list differs from the object's. -/
example :
    (objectWrites (fun _ => none) [("a", .data (num 1) Attrs.plain)]
      [("a", .data (num 1) Attrs.plain), ("a", .data (num 1) Attrs.plain)]).1 = [] ∧
    ["a"] ≠ ["a", "a"] := by
  decide

/-- `writesOf_nil_iff` needs identities that keep each object at one node at most: two members of
`next` that both stand for the set's one member need no write, yet the set holds one member. -/
example :
    entryWrites (fun j => if j < 2 then some 3 else none) [.ref 3] [.ref 0, .ref 1]
      (fun _ => none) (fun _ => none) = [] ∧
    [Val.ref 0, .ref 1].map (resolveKey (fun j => if j < 2 then some 3 else none)) ≠
      [Val.ref 3].map some := by
  decide

end WriteExamples


/-! ## Descriptors -/

theorem attrsOf_slotWith (cs : Slot) (v : Val) : attrsOf (slotWith cs v) = attrsOf cs := by
  cases cs <;> rfl

/-- A kept object holds `next`'s values under `next`'s keys. A retained key keeps its own slot
(`slotWith`): a data property its attributes, an accessor its kind, its setter, its enumerability
and its configurability. A moved key, deleted and added again, keeps its attributes (`attrsOf`). An
added key is a data property, writable and configurable with `next`'s enumerability. -/
theorem keptObject_attrs (proto : Proto) (cFields : List (String × Slot)) (extensible : Bool)
    (nFields : List (String × Slot)) :
    ∀ p ∈ fieldsOf (keptObject proto cFields extensible nFields),
      ∃ ns, (p.1, ns) ∈ nFields ∧ p.2.value = ns.value ∧
        match cFields.lookup p.1 with
        | some cs => attrsOf p.2 = attrsOf cs ∧
            (p.1 ∈ retainPrefix (cFields.map Prod.fst) (nFields.map Prod.fst) →
              p.2 = slotWith cs ns.value)
        | none => p.2 = .data ns.value (.copied ns.enumerable) := by
  intro p hp
  simp only [keptObject, fieldsOf, List.mem_map] at hp
  obtain ⟨⟨k, ns⟩, hmem, rfl⟩ := hp
  refine ⟨ns, hmem, ?_⟩
  dsimp only
  cases cFields.lookup k with
  | none => exact ⟨rfl, rfl⟩
  | some cs =>
    dsimp only
    by_cases hr : k ∈ retainPrefix (cFields.map Prod.fst) (nFields.map Prod.fst)
    · rw [if_pos (List.contains_iff_mem.mpr hr)]
      exact ⟨by cases cs <;> rfl, attrsOf_slotWith cs _, fun _ => rfl⟩
    · rw [if_neg (by simpa using hr)]
      exact ⟨rfl, rfl, fun h => absurd h hr⟩

/-- Under the static checks, a kept object keeps each own getter or setter that `next` keeps as
an accessor with its setter, enumerability and configurability, holding `next`'s value: an
accessor cannot move, so `objectAdmits` keeps it in the retained prefix. -/
theorem keptObject_accessor (proto : Proto) (cFields : List (String × Slot)) (extensible : Bool)
    (nFields inherited : List (String × Slot))
    (hadm : objectAdmits cFields extensible nFields inherited = true) :
    ∀ p ∈ fieldsOf (keptObject proto cFields extensible nFields), ∀ v setter e c,
      cFields.lookup p.1 = some (.accessor v setter e c) →
        ∃ ns, (p.1, ns) ∈ nFields ∧ p.2 = .accessor ns.value setter e c := by
  intro p hp v setter e c hc
  obtain ⟨ns, hmem, -, h⟩ := keptObject_attrs proto cFields extensible nFields p hp
  rw [hc] at h
  refine ⟨ns, hmem, h.2 ?_⟩
  obtain ⟨l₁, l₂, hl, -⟩ := List.lookup_eq_some_iff.mp hc
  have hcm : (p.1, OwnProperty.accessor v setter e c) ∈ cFields := by simp [hl]
  simp only [objectAdmits, Bool.and_eq_true, List.all_eq_true] at hadm
  have hk : (nFields.map Prod.fst).contains p.1 = true :=
    List.contains_iff_mem.mpr (List.mem_map.mpr ⟨_, hmem, rfl⟩)
  have := hadm.2 _ hcm
  simp only [hk, Bool.not_true, Bool.false_or, List.contains_iff_mem] at this
  exact this

/-! ## Blockers -/

/-- Demotion forbids only an object whose writes block: every object a pass finds blocked is kept
by that pass's decision at an unpinned node, and one of its writes reaches a setter that drops
its value or a fixed slot. -/
theorem mem_blockedObjects (input : Input) (pin : Array Bool) (kept : Array (Option Nat))
    (i : Nat) (h : i ∈ blockedObjects input pin kept) :
    ∃ j, j < input.next.nodes.size ∧ pin[j]?.getD false = false ∧
      kept[j]?.bind id = some i ∧
      (writesOf (identityOf kept) (input.cur.node i) (input.next.node j)).2 = true := by
  simp only [blockedObjects, List.mem_filterMap, List.mem_range] at h
  obtain ⟨j, hj, hf⟩ := h
  refine ⟨j, hj, ?_⟩
  split at hf
  · simp at hf
  · rename_i hpin
    split at hf
    · rename_i i' hi'
      split at hf
      · rename_i hw
        simp only [Option.some.injEq] at hf
        subst hf
        exact ⟨by simpa using hpin, hi', hw⟩
      · simp at hf
    · simp at hf

/-- An object a pass finds blocked is a current object: past `current`'s nodes lies the default
empty object, whose writes never block. -/
theorem blocked_lt (input : Input) (pin : Array Bool) (kept : Array (Option Nat)) (i : Nat)
    (h : i ∈ blockedObjects input pin kept) : i < input.cur.nodes.size := by
  obtain ⟨j, _, _, _, hw⟩ := mem_blockedObjects input pin kept i h
  refine Nat.lt_of_not_le fun hge => ?_
  have hd : input.cur.node i = .object .object [] false := by
    simp only [Graph.node, Array.getElem?_eq_none hge, Option.getD_none]
    rfl
  rw [hd] at hw
  cases hn : input.next.node j <;> rw [hn] at hw <;> simp [writesOf, objectWrites] at hw

/-! ## Decisions -/

theorem setIfInBounds_bind {xs : Array (Option Nat)} {i j x y : Nat}
    (h : (xs.setIfInBounds i (some x))[j]?.bind id = some y) :
    (i = j ∧ y = x) ∨ xs[j]?.bind id = some y := by
  rw [Array.getElem?_setIfInBounds] at h
  split at h
  · split at h
    · simp only [Option.bind_some, id, Option.some.injEq] at h
      exact Or.inl ⟨by assumption, h.symm⟩
    · simp at h
  · exact Or.inr h

/-- A node's candidates in a pass's order are `current` itself at the root, and otherwise its
candidates from discovery. -/
theorem mem_passCandidates (input : Input) (al : Discovery) (written : List Requirement)
    (j x : Nat) (h : x ∈ passCandidates input al written j) :
    (input.next.root.refId = some j ∧ input.cur.root.refId = some x) ∨
      x ∈ al.candidates[j]?.getD [] := by
  have hfound : ∀ y ∈ orderedCandidates input al j, y ∈ al.candidates[j]?.getD [] := by
    intro y hy
    simp only [orderedCandidates, List.mem_append, List.mem_filter] at hy
    rcases hy with ⟨hy, _⟩ | ⟨hy, _⟩ <;> exact hy
  unfold passCandidates at h
  split at h
  · rename_i hj
    refine Or.inl ⟨hj, ?_⟩
    cases hc : input.cur.root.refId <;> simp_all
  · right
    dsimp only at h
    split at h
    · split at h
      · rename_i y _ hy
        rcases List.mem_cons.mp h with rfl | h
        · exact hfound _ (by simpa using hy)
        · exact hfound _ (List.mem_filter.mp h).1
      · exact hfound _ h
    · exact hfound _ h

/-- What `establish` checks of each pair it reserves, apart from reservations: the object is a
candidate of the node in the pass's order, no earlier pass forbade it, and it passes the static
checks. -/
def checked (input : Input) (candidatesOf : Nat → List Nat) (forbidden : List Nat)
    (p : Requirement) : Prop :=
  p.2 ∈ candidatesOf p.1 ∧ forbidden.contains p.2 = false ∧
    admitsStatic input.classes (input.cur.node p.2) (input.next.node p.1) = true

/-- What `establish` checks of each pair it reserves: `checked`, and the object is not reserved
yet, or an earlier pass wrote it at that node. -/
def goodPair (input : Input) (candidatesOf : Nat → List Nat) (forbidden : List Nat)
    (written : List Requirement) (used : List Nat) (p : Requirement) : Prop :=
  checked input candidatesOf forbidden p ∧ (p.2 ∉ used ∨ p ∈ written)

/-- A chain of reserved pairs: each passed `establish`'s checks, and no two share a node or an
object. -/
def chainOK (input : Input) (candidatesOf : Nat → List Nat) (forbidden : List Nat)
    (written : List Requirement) (used : List Nat) (l : List Requirement) : Prop :=
  (∀ p ∈ l, goodPair input candidatesOf forbidden written used p) ∧
    ∀ p ∈ l, ∀ q ∈ l, (p.1 = q.1 ∨ p.2 = q.2) → p = q

/-- `establish` extends a chain only with pairs that pass its checks and share neither node nor
object with the chain. -/
theorem establish_chainOK (input : Input) (candidatesOf : Nat → List Nat) (forbidden : List Nat)
    (written : List Requirement) (kept : Array (Option Nat)) (decided : Array Bool)
    (required : Array (Option Nat)) (used : List Nat) :
    ∀ fuel chain c x r,
      establish input candidatesOf forbidden written kept decided required used fuel chain c x =
        some r →
      chainOK input candidatesOf forbidden written used chain →
        chainOK input candidatesOf forbidden written used r := by
  intro fuel
  induction fuel with
  | zero => intro chain c x r h; simp [establish] at h
  | succ fuel ih =>
    intro chain c x r h hchain
    simp only [establish] at h
    split at h
    · cases h; exact hchain
    split at h
    · simp at h
    rename_i hany
    split at h
    · split at h
      · cases h; exact hchain
      · simp at h
    split at h
    · split at h
      · cases h; exact hchain
      · simp at h
    split at h
    · simp at h
    rename_i hcond
    split at h
    · simp at h
    rename_i hadm
    have hstart : chainOK input candidatesOf forbidden written used ((c, x) :: chain) := by
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', not_or, not_and,
        Bool.not_eq_false] at hcond
      have hgood : goodPair input candidatesOf forbidden written used (c, x) := by
        refine ⟨⟨by simpa using hcond.2, by simpa using hcond.1.1, by simpa using hadm⟩, ?_⟩
        by_cases hu : x ∈ used
        · right
          have := hcond.1.2 (List.contains_iff_mem.mpr hu)
          simpa using this
        · exact Or.inl hu
      simp only [List.any_eq_true, not_exists, not_and, Bool.or_eq_true, decide_eq_true_eq,
        not_or] at hany
      refine ⟨?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hgood
        · exact hchain.1 p hp
      · intro p hp q hq hpq
        rcases List.mem_cons.mp hp with rfl | hp <;> rcases List.mem_cons.mp hq with rfl | hq
        · rfl
        · obtain ⟨a, b⟩ := q
          have := hany (a, b) hq
          simp only at this hpq
          rcases hpq with h1 | h1
          · exact absurd h1.symm this.1
          · exact absurd h1.symm this.2
        · obtain ⟨a, b⟩ := p
          have := hany (a, b) hp
          simp only at this hpq
          rcases hpq with h1 | h1
          · exact absurd h1 this.1
          · exact absurd h1 this.2
        · exact hchain.2 p hp q hq hpq
    revert r
    refine List.foldlRecOn (motive := fun (o : Option (List Requirement)) =>
      ∀ r, o = some r → chainOK input candidatesOf forbidden written used r) _ _ ?_ ?_
    · intro r hr
      cases hr
      exact hstart
    · intro acc hacc ⟨cv, nv⟩ _ r hr
      cases acc with
      | none => simp at hr
      | some ch =>
        simp only [Option.bind_some] at hr
        cases cv <;> cases nv <;> simp only at hr
        · split at hr
          · obtain rfl := Option.some.inj hr; exact hacc _ rfl
          · simp at hr
        · simp at hr
        · simp at hr
        · exact ih _ _ _ r hr (hacc ch rfl)

/-- Whether a decision state assigns object `x` to node `a`: keeps it there, or a decided parent
requires it there. -/
def assigned (d : Decision) (a x : Nat) : Prop :=
  d.kept[a]?.bind id = some x ∨ d.required[a]?.bind id = some x

/-- Whether object `x` is reserved for node `c` before a pass decides: pinned there, or written
there by an earlier pass. -/
def startReserved (input : Input) (pin : Array Bool) (written : List Requirement) (c x : Nat) :
    Prop :=
  (c, x) ∈ written ∨
    (c < input.next.nodes.size ∧ pin[c]?.getD false = true ∧ input.same[c]?.bind id = some x)

/-- Whether no object is reserved for two nodes before a pass. -/
def StartUnique (input : Input) (pin : Array Bool) (written : List Requirement) : Prop :=
  ∀ c c' x, startReserved input pin written c x → startReserved input pin written c' x → c = c'

/-- The invariant of a decision state: every assigned or start-reserved object is in `used`; an
object kept at an unpinned node, or required anywhere, passed `establish`'s checks there; and when
no object is reserved for two nodes before the pass, each object is assigned to one node at most
and only to the node it was reserved for. -/
structure DecisionInv (input : Input) (pin : Array Bool) (candidatesOf : Nat → List Nat)
    (forbidden : List Nat) (written : List Requirement) (d : Decision) : Prop where
  assigned_used : ∀ a x, assigned d a x → x ∈ d.used
  reserved_used : ∀ c x, startReserved input pin written c x → x ∈ d.used
  kept_checked : ∀ a x, d.kept[a]?.bind id = some x →
    pin[a]?.getD false = true ∨ checked input candidatesOf forbidden (a, x)
  required_checked : ∀ c x, d.required[c]?.bind id = some x →
    checked input candidatesOf forbidden (c, x)
  inj : StartUnique input pin written → ∀ a b x, assigned d a x → assigned d b x → a = b
  reserved_at : StartUnique input pin written →
    ∀ b c x, assigned d b x → startReserved input pin written c x → b = c

/-- A state with the same `used` that assigns only what another state assigned, keeping only what
it kept or required, keeps the invariant. -/
theorem DecisionInv.of_sub {input : Input} {pin : Array Bool} {candidatesOf : Nat → List Nat}
    {forbidden : List Nat} {written : List Requirement} {d d' : Decision}
    (hd : DecisionInv input pin candidatesOf forbidden written d) (hu : d'.used = d.used)
    (hk : ∀ a y : Nat, d'.kept[a]?.bind id = some y →
      d.kept[a]?.bind id = some y ∨ d.required[a]?.bind id = some y)
    (hr : ∀ c y : Nat, d'.required[c]?.bind id = some y → d.required[c]?.bind id = some y) :
    DecisionInv input pin candidatesOf forbidden written d' := by
  have ha : ∀ a y, assigned d' a y → assigned d a y := by
    intro a y h
    rcases h with h | h
    · exact hk a y h
    · exact Or.inr (hr a y h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a y h
    rw [hu]
    exact hd.assigned_used a y (ha a y h)
  · intro c y h
    rw [hu]
    exact hd.reserved_used c y h
  · intro a y h
    rcases hk a y h with h | h
    · exact hd.kept_checked a y h
    · exact Or.inr (hd.required_checked a y h)
  · intro c y h
    exact hd.required_checked c y (hr c y h)
  · intro hs a b y h1 h2
    exact hd.inj hs a b y (ha a y h1) (ha b y h2)
  · intro hs b c y h1 h2
    exact hd.reserved_at hs b c y (ha b y h1) h2

/-- Reserving one more pair of a chain `establish` returned for state `d` keeps the invariant. -/
theorem DecisionInv.add {input : Input} {pin : Array Bool} {candidatesOf : Nat → List Nat}
    {forbidden : List Nat} {written : List Requirement}
    {d d' d'' : Decision} {pairs : List Requirement} (c y : Nat)
    (hd : DecisionInv input pin candidatesOf forbidden written d)
    (hd' : DecisionInv input pin candidatesOf forbidden written d')
    (hsub : ∀ a z, assigned d' a z → assigned d a z ∨ (a, z) ∈ pairs)
    (hused : ∀ z ∈ d.used, z ∈ d'.used)
    (hpairs : chainOK input candidatesOf forbidden written d.used pairs) (hcy : (c, y) ∈ pairs)
    (hu : d''.used = y :: d'.used)
    (hk : ∀ a z, d''.kept[a]?.bind id = some z → d'.kept[a]?.bind id = some z ∨ (a = c ∧ z = y))
    (hr : ∀ a z, d''.required[a]?.bind id = some z →
      d'.required[a]?.bind id = some z ∨ (a = c ∧ z = y)) :
    DecisionInv input pin candidatesOf forbidden written d'' ∧
      (∀ a z, assigned d'' a z → assigned d a z ∨ (a, z) ∈ pairs) ∧
      (∀ z ∈ d.used, z ∈ d''.used) := by
  have ha : ∀ a z, assigned d'' a z → assigned d' a z ∨ (a = c ∧ z = y) := by
    intro a z h
    rcases h with h | h
    · rcases hk a z h with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases hr a z h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  have hgood := hpairs.1 (c, y) hcy
  have hnew : StartUnique input pin written → ∀ b, assigned d' b y → b = c := by
    intro hs b hb
    rcases hsub b y hb with hb | hb
    · rcases hgood.2 with hu' | hw
      · exact absurd (hd.assigned_used b y hb) hu'
      · exact hd.reserved_at hs b c y hb (Or.inl hw)
    · have := hpairs.2 (b, y) hb (c, y) hcy (Or.inr rfl)
      simp only [Prod.mk.injEq] at this
      exact this.1
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro a z h
    rw [hu]
    rcases ha a z h with h | ⟨-, rfl⟩
    · exact List.mem_cons_of_mem _ (hd'.assigned_used a z h)
    · exact List.mem_cons_self
  · intro c' z h
    rw [hu]
    exact List.mem_cons_of_mem _ (hd'.reserved_used c' z h)
  · intro a z h
    rcases hk a z h with h | ⟨rfl, rfl⟩
    · exact hd'.kept_checked a z h
    · exact Or.inr hgood.1
  · intro a z h
    rcases hr a z h with h | ⟨rfl, rfl⟩
    · exact hd'.required_checked a z h
    · exact hgood.1
  · intro hs a b z h1 h2
    rcases ha a z h1 with h1 | ⟨rfl, rfl⟩
    · rcases ha b z h2 with h2 | ⟨rfl, rfl⟩
      · exact hd'.inj hs a b z h1 h2
      · exact hnew hs a h1
    · rcases ha b z h2 with h2 | ⟨rfl, -⟩
      · exact (hnew hs b h2).symm
      · rfl
  · intro hs b c' z h1 h2
    rcases ha b z h1 with h1 | ⟨rfl, rfl⟩
    · exact hd'.reserved_at hs b c' z h1 h2
    · rcases hgood.2 with hu' | hw
      · exact absurd (hd.reserved_used c' z h2) hu'
      · exact hs b c' z (Or.inl hw) h2
  · intro a z h
    rcases ha a z h with h | ⟨rfl, rfl⟩
    · exact hsub a z h
    · exact Or.inr hcy
  · intro z hz
    rw [hu]
    exact List.mem_cons_of_mem _ (hused z hz)

/-- Every decision state of a pass keeps `DecisionInv`. -/
theorem decide_inv (input : Input) (al : Discovery) (pin : Array Bool) (forbidden : List Nat)
    (written : List Requirement) :
    ∃ d : Decision, decide input al pin forbidden written = d.kept ∧
      DecisionInv input pin (passCandidates input al written) forbidden written d := by
  unfold decide
  refine ⟨_, rfl, ?_⟩
  apply List.foldlRecOn
  · -- The start state: the pinned objects, each reserved at its own node.
    have hk : ∀ a x : Nat,
        ((Array.range input.next.nodes.size).map (pinnedObject input pin))[a]?.bind id =
          some x →
        a < input.next.nodes.size ∧ pin[a]?.getD false = true ∧
          input.same[a]?.bind id = some x := by
      intro a x h
      simp only [Array.getElem?_map, Array.getElem?_range] at h
      split at h
      · rename_i ha
        simp only [Option.map_some, Option.bind_some, id, pinnedObject] at h
        split at h
        · exact ⟨ha, by assumption, h⟩
        · simp at h
      · simp at h
    have hr : ∀ c x : Nat,
        (Array.replicate input.next.nodes.size (none : Option Nat))[c]?.bind id ≠ some x := by
      intro c x h
      simp only [Array.getElem?_replicate] at h
      split at h <;> simp at h
    have ha : ∀ a x : Nat,
        (((Array.range input.next.nodes.size).map (pinnedObject input pin))[a]?.bind id =
          some x ∨
        (Array.replicate input.next.nodes.size (none : Option Nat))[a]?.bind id = some x) →
        a < input.next.nodes.size ∧ pin[a]?.getD false = true ∧
          input.same[a]?.bind id = some x := by
      intro a x h
      rcases h with h | h
      · exact hk a x h
      · exact absurd h (hr a x)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a x h
      obtain ⟨ha, hp, hs⟩ := ha a x h
      simp only [List.mem_append, List.mem_filterMap, List.mem_range]
      exact Or.inl ⟨a, ha, by simp [pinnedObject, hp, hs]⟩
    · intro c x h
      simp only [List.mem_append, List.mem_filterMap, List.mem_range, List.mem_map]
      rcases h with h | ⟨hc, hp, hs⟩
      · exact Or.inr ⟨(c, x), h, rfl⟩
      · exact Or.inl ⟨c, hc, by simp [pinnedObject, hp, hs]⟩
    · intro a x h
      exact Or.inl (hk a x h).2.1
    · intro c x h
      exact absurd h (hr c x)
    · intro hs a b x h1 h2
      exact hs a b x (Or.inr (ha a x h1)) (Or.inr (ha b x h2))
    · intro hs b c x h1 h2
      exact hs b c x (Or.inr (ha b x h1)) h2
  · intro d hd j _
    dsimp only
    split
    · exact hd
    split
    · rename_i x hreq
      refine DecisionInv.of_sub hd rfl ?_ (fun c y h => h)
      intro a y h
      rcases setIfInBounds_bind h with ⟨rfl, rfl⟩ | h
      · exact Or.inr hreq
      · exact Or.inl h
    split
    · exact DecisionInv.of_sub hd rfl (fun a y h => Or.inl h) (fun c y h => h)
    rename_i pairs hfind
    obtain ⟨x0, _, hest⟩ := List.exists_of_findSome?_eq_some hfind
    have hpairs := establish_chainOK _ _ _ _ _ _ _ _ _ _ _ _ _ hest
      ⟨by simp, by simp⟩
    refine (List.foldlRecOn (motive := fun d' : Decision =>
        DecisionInv input pin (passCandidates input al written) forbidden written d' ∧
        (∀ a z, assigned d' a z → assigned d a z ∨ (a, z) ∈ pairs) ∧
        (∀ z ∈ d.used, z ∈ d'.used)) pairs _ ?_ ?_).1
    · exact ⟨DecisionInv.of_sub hd rfl (fun a y h => Or.inl h) (fun c y h => h),
        fun a z h => Or.inl h, fun z hz => hz⟩
    intro d' ⟨hinv, hsub, hused⟩ ⟨c, y⟩ hcy
    dsimp only
    split
    · rename_i hc
      subst hc
      refine DecisionInv.add c y hd hinv hsub hused hpairs hcy rfl ?_
        (fun a z h => Or.inl h)
      intro a z h
      rcases setIfInBounds_bind h with ⟨rfl, rfl⟩ | h
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl h
    · refine DecisionInv.add c y hd hinv hsub hused hpairs hcy rfl
        (fun a z h => Or.inl h) ?_
      intro a z h
      rcases setIfInBounds_bind h with ⟨rfl, rfl⟩ | h
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl h

/-- An object a decision keeps at an unpinned node passed `establish`'s checks there: it is a
candidate of the node, no earlier pass forbade it, and it passes the static checks. -/
theorem decide_checked (input : Input) (al : Discovery) (pin : Array Bool)
    (forbidden : List Nat) (written : List Requirement) (j x : Nat)
    (hpin : pin[j]?.getD false = false)
    (h : (decide input al pin forbidden written)[j]?.bind id = some x) :
    checked input (passCandidates input al written) forbidden (j, x) := by
  obtain ⟨d, hd, hinv⟩ := decide_inv input al pin forbidden written
  rw [hd] at h
  rcases hinv.kept_checked j x h with hp | hc
  · rw [hpin] at hp
    cases hp
  · exact hc

/-- A decision keeps at an unpinned node only a candidate of it: `current` at the root, and
otherwise the object at the node's position inside a candidate of a parent. Values are matched by
position. -/
theorem decide_candidate (input : Input) (al : Discovery) (pin : Array Bool)
    (forbidden : List Nat) (written : List Requirement) (j x : Nat)
    (hpin : pin[j]?.getD false = false)
    (h : (decide input al pin forbidden written)[j]?.bind id = some x) :
    (input.next.root.refId = some j ∧ input.cur.root.refId = some x) ∨
      x ∈ al.candidates[j]?.getD [] :=
  mem_passCandidates input al written j x
    (decide_checked input al pin forbidden written j x hpin h).1

/-- A pass never finds blocked an object an earlier pass forbade: every blocked object is kept at
an unpinned node (`mem_blockedObjects`), and the decision keeps no forbidden object there
(`decide_checked`). So each pass that does not end the run forbids a current object no earlier
pass forbade, and the passes end within one more than the number of current objects, whatever
the budget (`demote_length_le`). -/
theorem blocked_fresh (input : Input) (al : Discovery) (pin : Array Bool) (forbidden : List Nat)
    (written : List Requirement) (i : Nat)
    (h : i ∈ blockedObjects input pin (decide input al pin forbidden written)) :
    forbidden.contains i = false := by
  obtain ⟨j, _, hpin, hkept, _⟩ := mem_blockedObjects input pin _ i h
  exact (decide_checked input al pin forbidden written j i hpin hkept).2.1

/-! ## Injective decisions -/

/-- No object is reserved for two nodes before a pass when `written` names each object at one
node, distinct pinned nodes are distinct objects, and no pinned object is written at another
node. -/
theorem startReserved_unique (input : Input) (pin : Array Bool) (written : List Requirement)
    (hw : ∀ c c' x, (c, x) ∈ written → (c', x) ∈ written → c = c')
    (hsame : ∀ a b x, a < input.next.nodes.size → b < input.next.nodes.size →
      pin[a]?.getD false = true → pin[b]?.getD false = true →
      input.same[a]?.bind id = some x → input.same[b]?.bind id = some x → a = b)
    (hpw : ∀ b c x, b < input.next.nodes.size → pin[b]?.getD false = true →
      input.same[b]?.bind id = some x → (c, x) ∈ written → b = c) :
    StartUnique input pin written := by
  intro c c' x h1 h2
  rcases h1 with h1 | ⟨hc, hp, hs⟩ <;> rcases h2 with h2 | ⟨hc', hp', hs'⟩
  · exact hw c c' x h1 h2
  · exact (hpw c' c x hc' hp' hs' h1).symm
  · exact hpw c c' x hc hp hs h2
  · exact hsame c c' x hc hc' hp hp' hs hs'

/-- A decision keeps each current object at one node at most, given the premises of
`startReserved_unique`. -/
theorem decide_injective (input : Input) (al : Discovery) (pin : Array Bool)
    (forbidden : List Nat) (written : List Requirement)
    (hw : ∀ c c' x, (c, x) ∈ written → (c', x) ∈ written → c = c')
    (hsame : ∀ a b x, a < input.next.nodes.size → b < input.next.nodes.size →
      pin[a]?.getD false = true → pin[b]?.getD false = true →
      input.same[a]?.bind id = some x → input.same[b]?.bind id = some x → a = b)
    (hpw : ∀ b c x, b < input.next.nodes.size → pin[b]?.getD false = true →
      input.same[b]?.bind id = some x → (c, x) ∈ written → b = c)
    (a b x : Nat) (ha : (decide input al pin forbidden written)[a]?.bind id = some x)
    (hb : (decide input al pin forbidden written)[b]?.bind id = some x) : a = b := by
  obtain ⟨d, hd, hinv⟩ := decide_inv input al pin forbidden written
  rw [hd] at ha hb
  exact hinv.inj (startReserved_unique input pin written hw hsame hpw) a b x (Or.inl ha)
    (Or.inl hb)

/-- A decision keeps an object reserved before the pass only at the node it was reserved for. -/
theorem decide_reserved (input : Input) (al : Discovery) (pin : Array Bool)
    (forbidden : List Nat) (written : List Requirement)
    (hstart : ∀ c c' x, startReserved input pin written c x →
      startReserved input pin written c' x → c = c')
    (b c x : Nat) (hb : (decide input al pin forbidden written)[b]?.bind id = some x)
    (hc : startReserved input pin written c x) : b = c := by
  obtain ⟨d, hd, hinv⟩ := decide_inv input al pin forbidden written
  rw [hd] at hb
  exact hinv.reserved_at hstart b c x (Or.inl hb) hc

theorem mem_writtenPairs (input : Input) (pin : Array Bool) (kept : Array (Option Nat))
    (j i : Nat) :
    (j, i) ∈ writtenPairs input pin kept ↔
      j < input.next.nodes.size ∧ pin[j]?.getD false = false ∧ kept[j]?.bind id = some i := by
  simp only [writtenPairs, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨j', hj', h⟩
    split at h
    · simp at h
    · rename_i hp
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨i', hi', rfl, rfl⟩ := h
      exact ⟨hj', by simpa using hp, hi'⟩
  · rintro ⟨hj, hp, hi⟩
    refine ⟨j, hj, ?_⟩
    simp [hp, hi]

/-- Every decision of the passes is a decision whose written pairs name each object at one node
and no pinned object: each pass writes objects its decision kept at one node at most
(`decide_injective`) and never a pinned object elsewhere (`decide_reserved`). -/
theorem demote_inv (input : Input) (al : Discovery) (pin : Array Bool) (r : Nat)
    (hsame : ∀ a b x, a < input.next.nodes.size → b < input.next.nodes.size →
      pin[a]?.getD false = true → pin[b]?.getD false = true →
      input.same[a]?.bind id = some x → input.same[b]?.bind id = some x → a = b) :
    ∀ (fuel : Nat) (forbidden : List Nat) (written : List Requirement),
      (∀ c c' x, (c, x) ∈ written → (c', x) ∈ written → c = c') →
      (∀ b c x, b < input.next.nodes.size → pin[b]?.getD false = true →
        input.same[b]?.bind id = some x → (c, x) ∈ written → b = c) →
      ∀ kept ∈ demote input al pin r fuel forbidden written,
        ∃ forbidden' written', kept = decide input al pin forbidden' written' ∧
          (∀ c c' x, (c, x) ∈ written' → (c', x) ∈ written' → c = c') ∧
          (∀ b c x, b < input.next.nodes.size → pin[b]?.getD false = true →
            input.same[b]?.bind id = some x → (c, x) ∈ written' → b = c) := by
  intro fuel
  induction fuel with
  | zero =>
    intro forbidden written hw hpw kept hk
    simp only [demote, List.mem_singleton] at hk
    exact ⟨forbidden, written, hk, hw, hpw⟩
  | succ fuel ih =>
    intro forbidden written hw hpw kept hk
    have hstart := startReserved_unique input pin written hw hsame hpw
    simp only [demote] at hk
    split at hk
    · simp only [List.mem_singleton] at hk
      exact ⟨forbidden, written, hk, hw, hpw⟩
    · rcases List.mem_cons.mp hk with rfl | hk
      · exact ⟨forbidden, written, rfl, hw, hpw⟩
      · refine ih _ _ ?_ ?_ kept hk
        · intro c c' x h1 h2
          simp only [List.mem_append] at h1 h2
          rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
          · exact hw c c' x h1 h2
          · have := (mem_writtenPairs input pin _ c' x).mp h2
            exact (decide_reserved input al pin forbidden written hstart c' c x this.2.2
              (Or.inl h1)).symm
          · have := (mem_writtenPairs input pin _ c x).mp h1
            exact decide_reserved input al pin forbidden written hstart c c' x this.2.2
              (Or.inl h2)
          · exact decide_injective input al pin forbidden written hw hsame hpw c c' x
              ((mem_writtenPairs input pin _ c x).mp h1).2.2
              ((mem_writtenPairs input pin _ c' x).mp h2).2.2
        · intro b c x hb hp hs h
          simp only [List.mem_append] at h
          rcases h with h | h
          · exact hpw b c x hb hp hs h
          · have := (mem_writtenPairs input pin _ c x).mp h
            exact (decide_reserved input al pin forbidden written hstart c b x this.2.2
              (Or.inr ⟨hb, hp, hs⟩)).symm

/-- Every decision of a call's passes keeps each current object at one node at most, given that
distinct pinned nodes are distinct objects, as distinct next nodes are. -/
theorem demote_injective (input : Input) (al : Discovery) (pin : Array Bool) (r : Nat)
    (hsame : ∀ a b x, a < input.next.nodes.size → b < input.next.nodes.size →
      pin[a]?.getD false = true → pin[b]?.getD false = true →
      input.same[a]?.bind id = some x → input.same[b]?.bind id = some x → a = b)
    (fuel : Nat) (kept : Array (Option Nat)) (hk : kept ∈ demote input al pin r fuel [] [])
    (a b x : Nat) (ha : kept[a]?.bind id = some x) (hb : kept[b]?.bind id = some x) : a = b := by
  obtain ⟨forbidden, written, rfl, hw, hpw⟩ :=
    demote_inv input al pin r hsame fuel [] [] (by simp) (by simp) kept hk
  exact decide_injective input al pin forbidden written hw hsame hpw a b x ha hb

/-- In every decision of a call's passes, a pinned node's object is kept at no other node: an
object already in place stays at its own position, given that distinct pinned nodes are distinct
objects. -/
theorem demote_pinned (input : Input) (al : Discovery) (pin : Array Bool) (r : Nat)
    (hsame : ∀ a b x, a < input.next.nodes.size → b < input.next.nodes.size →
      pin[a]?.getD false = true → pin[b]?.getD false = true →
      input.same[a]?.bind id = some x → input.same[b]?.bind id = some x → a = b)
    (fuel : Nat) (kept : Array (Option Nat)) (hk : kept ∈ demote input al pin r fuel [] [])
    (b c x : Nat) (hc : c < input.next.nodes.size) (hpin : pin[c]?.getD false = true)
    (hs : input.same[c]?.bind id = some x) (hb : kept[b]?.bind id = some x) : b = c := by
  obtain ⟨forbidden, written, rfl, hw, hpw⟩ :=
    demote_inv input al pin r hsame fuel [] [] (by simp) (by simp) kept hk
  exact decide_reserved input al pin forbidden written
    (startReserved_unique input pin written hw hsame hpw) b c x hb (Or.inr ⟨hc, hpin, hs⟩)

/-- Every decision of the passes is a decision of some forbidden objects and written pairs. -/
theorem mem_demote (input : Input) (al : Discovery) (pin : Array Bool) (r : Nat) :
    ∀ (fuel : Nat) (forbidden : List Nat) (written : List Requirement),
      ∀ kept ∈ demote input al pin r fuel forbidden written,
        ∃ forbidden' written', kept = decide input al pin forbidden' written' := by
  intro fuel
  induction fuel with
  | zero =>
    intro forbidden written kept hk
    simp only [demote, List.mem_singleton] at hk
    exact ⟨forbidden, written, hk⟩
  | succ fuel ih =>
    intro forbidden written kept hk
    simp only [demote] at hk
    split at hk
    · simp only [List.mem_singleton] at hk
      exact ⟨forbidden, written, hk⟩
    · rcases List.mem_cons.mp hk with rfl | hk
      · exact ⟨forbidden, written, rfl⟩
      · exact ih _ _ kept hk

/-- Every decision of the passes keeps at an unpinned node only a candidate of it
(`decide_candidate`): values are matched by position. -/
theorem demote_candidate (input : Input) (al : Discovery) (pin : Array Bool) (r fuel : Nat)
    (kept : Array (Option Nat)) (hk : kept ∈ demote input al pin r fuel [] []) (j x : Nat)
    (hpin : pin[j]?.getD false = false) (h : kept[j]?.bind id = some x) :
    (input.next.root.refId = some j ∧ input.cur.root.refId = some x) ∨
      x ∈ al.candidates[j]?.getD [] := by
  obtain ⟨forbidden, written, rfl⟩ := mem_demote input al pin r fuel [] [] kept hk
  exact decide_candidate input al pin forbidden written j x hpin h

/-- Write minimality by the object each node keeps: in every decision of the passes, an unpinned
node takes no write exactly when the object it keeps already holds `next`'s contents, given
distinct keys. -/
theorem demote_writesOf_nil_iff (input : Input) (al : Discovery) (pin : Array Bool) (r : Nat)
    (hsame : ∀ a b x, a < input.next.nodes.size → b < input.next.nodes.size →
      pin[a]?.getD false = true → pin[b]?.getD false = true →
      input.same[a]?.bind id = some x → input.same[b]?.bind id = some x → a = b)
    (fuel : Nat) (kept : Array (Option Nat)) (hk : kept ∈ demote input al pin r fuel [] [])
    (j i : Nat) (hpin : pin[j]?.getD false = false) (hj : kept[j]?.bind id = some i)
    (hkeys : distinctKeys (input.cur.node i) (input.next.node j)) :
    (writesOf (identityOf kept) (input.cur.node i) (input.next.node j)).1 = [] ↔
      holds (identityOf kept) (input.cur.node i) (input.next.node j) := by
  obtain ⟨forbidden, written, rfl, hw, hpw⟩ :=
    demote_inv input al pin r hsame fuel [] [] (by simp) (by simp) kept hk
  exact writesOf_nil_iff input.classes _ _ _
    (decide_checked input al pin forbidden written j i hpin hj).2.2 hkeys
    (decide_injective input al pin forbidden written hw hsame hpw)

private def emptyObject : Obj := .object .object [] true

private def twoPinned : Input where
  cur := ⟨#[emptyObject], .ref 0⟩
  next := ⟨#[emptyObject, emptyObject], .ref 0⟩
  same := #[some 0, some 0]

/-- `decide_injective` needs distinct pinned objects: two pinned nodes that `same` maps to one
object both keep it. -/
example :
    decide twoPinned ⟨[0, 1], #[none, none], #[true, true], #[[], []]⟩ #[true, true] [] [] =
      #[some 0, some 0] := by
  decide +kernel

/-- Two next nodes under a primitive root, each with current object 0 as its candidate. -/
private def twoNodes (same : Array (Option Nat)) : Input where
  cur := ⟨#[emptyObject], .ref 0⟩
  next := ⟨#[emptyObject, emptyObject], .prim .null⟩
  same := same

/-- `decide_injective` needs `written` to name each object at one node: an object written at two
nodes is kept at both. `demote` never writes one so (`demote_inv`). -/
example :
    decide (twoNodes #[none, none]) ⟨[0, 1], #[none, none], #[false, false], #[[0], [0]]⟩
      #[false, false] [] [(0, 0), (1, 0)] = #[some 0, some 0] := by
  decide +kernel

/-- `decide_injective` needs no pinned object to be written at another node: such an object is
kept at both. `demote` never writes one so (`demote_inv`). -/
example :
    decide (twoNodes #[some 0, none]) ⟨[0, 1], #[none, none], #[true, false], #[[], [0]]⟩
      #[true, false] [] [(1, 0)] = #[some 0, some 0] := by
  decide +kernel

/-! ## Passes -/

/-- The current objects no pass has forbidden. -/
def unforbidden (input : Input) (forbidden : List Nat) : List Nat :=
  (List.range input.cur.nodes.size).filter fun i => !forbidden.contains i

/-- A pass that finds an object blocked leaves fewer current objects unforbidden: the object is a
current object (`blocked_lt`) no earlier pass forbade (`blocked_fresh`). -/
theorem unforbidden_lt (input : Input) (al : Discovery) (pin : Array Bool)
    (forbidden : List Nat) (written : List Requirement)
    (h : blockedObjects input pin (decide input al pin forbidden written) ≠ []) :
    (unforbidden input
        (forbidden ++ blockedObjects input pin (decide input al pin forbidden written))).length <
      (unforbidden input forbidden).length := by
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ h
  have heq : unforbidden input
      (forbidden ++ blockedObjects input pin (decide input al pin forbidden written)) =
      (unforbidden input forbidden).filter fun i =>
        !(blockedObjects input pin (decide input al pin forbidden written)).contains i := by
    simp only [unforbidden, List.filter_filter, List.contains_append, Bool.not_or]
    congr 1
    funext i
    exact Bool.and_comm _ _
  rw [heq, List.length_filter_lt_length_iff_exists]
  refine ⟨b, ?_, by simpa using hb⟩
  simp only [unforbidden, List.mem_filter, List.mem_range]
  exact ⟨blocked_lt input pin _ b hb,
    by simpa using blocked_fresh input al pin forbidden written b hb⟩

/-- The passes number at most one more than the current objects no earlier pass forbade,
whatever the budget: each pass that continues forbids one of them (`unforbidden_lt`). -/
theorem demote_length_le (input : Input) (al : Discovery) (pin : Array Bool) (r : Nat) :
    ∀ fuel forbidden written,
      (demote input al pin r fuel forbidden written).length ≤
        (unforbidden input forbidden).length + 1
  | 0, _, _ => by simp [demote]
  | fuel + 1, forbidden, written => by
    simp only [demote]
    split
    · simp
    · rename_i h
      simp only [Bool.or_eq_true, not_or, List.isEmpty_iff] at h
      have := unforbidden_lt input al pin forbidden written h.2
      have := demote_length_le input al pin r fuel
        (forbidden ++ blockedObjects input pin (decide input al pin forbidden written))
        (written ++ writtenPairs input pin (decide input al pin forbidden written))
      simp only [List.length_cons]
      omega

/-- Once the budget covers the current objects no earlier pass forbade, the passes end on their
own: the last decision keeps no root, which rejects the call, or keeps no object whose writes
block. -/
theorem demote_last_unblocked (input : Input) (al : Discovery) (pin : Array Bool) (r : Nat) :
    ∀ fuel forbidden written d, (unforbidden input forbidden).length ≤ fuel →
      ((demote input al pin r fuel forbidden written).getLastD d)[r]?.bind id = none ∨
        blockedObjects input pin ((demote input al pin r fuel forbidden written).getLastD d) = []
  | 0, forbidden, written, _, hm => by
    simp only [demote, List.getLastD_cons, List.getLastD_nil]
    refine Or.inr (List.eq_nil_iff_forall_not_mem.mpr fun i hi => ?_)
    have : i ∈ unforbidden input forbidden := by
      simp only [unforbidden, List.mem_filter, List.mem_range]
      exact ⟨blocked_lt input pin _ i hi,
        by simpa using blocked_fresh input al pin forbidden written i hi⟩
    have := List.length_pos_of_mem this
    omega
  | fuel + 1, forbidden, written, _, hm => by
    simp only [demote]
    split
    · rename_i h
      simp only [List.getLastD_cons, List.getLastD_nil]
      simp only [Bool.or_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] at h
      exact h
    · rename_i h
      simp only [Bool.or_eq_true, not_or, List.isEmpty_iff] at h
      have := unforbidden_lt input al pin forbidden written h.2
      rw [List.getLastD_cons]
      exact demote_last_unblocked input al pin r fuel _ _ _ (by omega)

/-- The passes of a run: none when it has nothing to do or its first decision keeps no root, else
the decisions of its passes. -/
theorem run_passes (input : Input) : (run input).passes = 0 ∨
    ∃ r, (run input).passes =
      (rounds (normalized input) (discover (normalized input)) r).length := by
  simp only [run]
  split
  · split
    · split
      · exact Or.inl rfl
      · exact Or.inr ⟨_, rfl⟩
    · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

/-- A call makes at most one decision pass per current object, plus one, whatever the budget: no
plan is searched. -/
theorem passes_le_cur (input : Input) : (run input).passes ≤ input.cur.nodes.size + 1 := by
  rcases run_passes input with h | ⟨r, h⟩ <;> rw [h]
  · exact Nat.zero_le _
  · have := demote_length_le (normalized input) (discover (normalized input))
      (discover (normalized input)).pinned r (normalized input).cur.nodes.size [] []
    have hu : (unforbidden (normalized input) []).length ≤ input.cur.nodes.size := by
      simp [unforbidden, normalized, Graph.normalize]
    simp only [rounds]
    omega

/-- The passes number at most one per pair of a next node and a current object, plus two: with a
node in `next`, `passes_le_cur`; with none, nothing blocks and a call makes one pass at most. -/
theorem passes_le (input : Input) :
    (run input).passes ≤ input.next.nodes.size * (input.cur.nodes.size + 1) + 2 := by
  have hcur := passes_le_cur input
  rcases Nat.eq_zero_or_pos input.next.nodes.size with hn | hn
  · rcases run_passes input with h | ⟨r, h⟩ <;> rw [h]
    · exact Nat.zero_le _
    · have : (rounds (normalized input) (discover (normalized input)) r).length = 1 := by
        simp only [rounds]
        cases (normalized input).cur.nodes.size <;>
          simp [demote, blockedObjects, normalized, Graph.normalize, hn]
      omega
  · have := Nat.le_mul_of_pos_left (input.cur.nodes.size + 1) hn
    omega

/-- A call that succeeds keeps no object whose writes block: its final decision, the result's
origins, is the one its passes end on, which the budget never cuts short
(`demote_last_unblocked`). So an object that blocks a change is replaced by a copy. -/
theorem run_last_unblocked (input : Input) (c r : Nat) (hc : input.cur.root = .ref c)
    (hr : input.next.root = .ref r) (hok : (run input).ok = true) :
    blockedObjects (normalized input) (discover (normalized input)).pinned (run input).origins =
      [] := by
  have hc' : (normalized input).cur.root = .ref c := by simp [normalized, Graph.normalize, hc]
  have hr' : (normalized input).next.root = .ref r := by simp [normalized, Graph.normalize, hr]
  have hu : (unforbidden (normalized input) []).length ≤ (normalized input).cur.nodes.size := by
    simp [unforbidden]
  have hlast := demote_last_unblocked (normalized input) (discover (normalized input))
    (discover (normalized input)).pinned r _ [] [] #[] hu
  simp only [run, hc', hr'] at hok ⊢
  split at hok
  · simp at hok
  · rename_i hroot
    rw [if_neg hroot]
    exact hlast.resolve_left fun h => hroot (by unfold rounds; rw [h]; rfl)

/-! ## Reads of `next`

Capture reads `next` in one walk, beside the walks that keep subtrees in place (`captureReads`).
A getter of an object only `next` holds runs once at most (`freshGets_le_one`), and the walks that
keep subtrees in place run each getter once at most (`captureReads_once`). An object kept in place
is then neither written nor read back (`run_pinned`). An object `current` and `next` share can
still run a getter twice while `next` is read: two examples show it for an object kept in place
that is also inside an object referring to `current`, or also a `Map` value in `next`, the
exceptions the promise names. -/

/-- `eraseDups` keeps each element once, and only elements of its list. -/
theorem eraseDups_spec {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List α), (∀ x ∈ l.eraseDups, x ∈ l) ∧ l.eraseDups.Nodup
  | [] => by simp
  | a :: as => by
    have ih := eraseDups_spec (as.filter fun b => !b == a)
    rw [List.eraseDups_cons]
    refine ⟨?_, List.nodup_cons.2 ⟨fun ha => by simpa using ih.1 a ha, ih.2⟩⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_filter.1 (ih.1 x hx)).1
termination_by l => l.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- A read of an object runs each of its getters once. -/
theorem getters_nodup (o : Obj) : (getters o).Nodup :=
  ((eraseDups_spec (keysOf o)).2).filter _

/-- Pairing a list without duplicates with one tag gives each pair at most once, and none with
another tag. -/
theorem count_tagged {β γ : Type} [DecidableEq β] [DecidableEq γ] (t : β) {l : List γ}
    (hl : l.Nodup) (x : β × γ) :
    (l.map fun k => (t, k)).count x ≤ if x.1 = t then 1 else 0 := by
  split
  · exact List.nodup_iff_count_le_one.1 (hl.map fun a b h => (Prod.mk.inj h).2) x
  · rename_i hx
    rw [List.count_eq_zero_of_not_mem]
    intro hm
    obtain ⟨k, _, rfl⟩ := List.mem_map.1 hm
    exact hx rfl

/-- A keep walk runs current objects' getters only. One that meets no root reads none of
`closure`, and each getter of the objects it returns at most once and no other. -/
theorem keepWalk_spec (cur : Graph) (stop : Nat → Bool) (closure : List Nat) :
    ∀ fuel stack walked (reads : List (Owner × String)),
      (∀ s ∈ walked, closure.contains s = false) →
      (∀ e ∈ reads, ∃ s, e.1 = .cur s) →
      (∀ s k, reads.count (.cur s, k) ≤ if walked.contains s then 1 else 0) →
      (∀ e ∈ (keepWalk cur stop closure fuel stack walked reads).2, ∃ s, e.1 = .cur s) ∧
      ∀ walked', (keepWalk cur stop closure fuel stack walked reads).1 = some walked' →
        (∀ s ∈ walked', closure.contains s = false) ∧
        ∀ s k, (keepWalk cur stop closure fuel stack walked reads).2.count (.cur s, k) ≤
          if walked'.contains s then 1 else 0
  | 0, _, walked, reads, hc, ho, hn => by
    refine ⟨ho, fun w hw => ?_⟩
    simp only [keepWalk, Option.some.injEq] at hw
    subst hw
    exact ⟨hc, hn⟩
  | _ + 1, [], walked, reads, hc, ho, hn => by
    refine ⟨ho, fun w hw => ?_⟩
    simp only [keepWalk, Option.some.injEq] at hw
    subst hw
    exact ⟨hc, hn⟩
  | fuel + 1, s :: stack, walked, reads, hc, ho, hn => by
    simp only [keepWalk]
    split
    · exact keepWalk_spec cur stop closure fuel stack walked reads hc ho hn
    · rename_i hs
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hs
      split
      · exact ⟨ho, fun _ h => by simp at h⟩
      · apply keepWalk_spec
        · intro s' hs'
          rcases List.mem_cons.1 hs' with rfl | hs'
          · exact hs.1
          · exact hc s' hs'
        · intro e he
          rcases List.mem_append.1 he with he | he
          · exact ho e he
          · obtain ⟨k, _, rfl⟩ := List.mem_map.1 he
            exact ⟨s, rfl⟩
        · intro s' k
          rw [List.count_append]
          have h1 := hn s' k
          have h2 := count_tagged (Owner.cur s) (getters_nodup (cur.node s)) (Owner.cur s', k)
          by_cases hss : s' = s
          · subst hss
            simp only [hs.2, Bool.false_eq_true, ite_false, ite_true, List.contains_cons,
              beq_self_eq_true, Bool.true_or] at h1 h2 ⊢
            omega
          · have hne : (Owner.cur s' = Owner.cur s) = False := by simp [hss]
            simp only [hne, ite_false, List.contains_cons, Bool.or_eq_true, beq_iff_eq, hss,
              false_or] at h2 ⊢
            omega

/-- The keep walk capture makes at a pending child, if it makes one, as `keepWalk_spec` has it. -/
theorem keepAt_spec (input : Input) (stop : Nat → Bool) (closure : List Nat) (j : Nat)
    (occupant : Option Nat) (keeps : Bool) :
    (∀ e ∈ (keepAt input stop closure j occupant keeps).2, ∃ s, e.1 = .cur s) ∧
    ∀ walked, (keepAt input stop closure j occupant keeps).1 = some walked →
      (∀ s ∈ walked, closure.contains s = false) ∧
      ∀ s k, (keepAt input stop closure j occupant keeps).2.count (.cur s, k) ≤
        if walked.contains s then 1 else 0 := by
  unfold keepAt
  split
  · split
    · exact keepWalk_spec input.cur stop closure _ _ [] [] (by simp) (by simp) (by simp)
    · simp
  · simp

/-- The getter runs of the walks that keep subtrees in place. -/
def keepRuns (reads : List Read) : List (Owner × String) :=
  (reads.filter fun e => e.1 == .keep).map Prod.snd

/-- The keep walks' getter runs of reads made one after another. -/
theorem keepRuns_append (a b : List Read) : keepRuns (a ++ b) = keepRuns a ++ keepRuns b := by
  simp [keepRuns]

/-- Getter runs that one reading tags: the keep walks' runs exactly when it is `keep`. -/
theorem keepRuns_tagged (t : Reading) (l : List (Owner × String)) :
    keepRuns (l.map fun e => (t, e)) = if t = .keep then l else [] := by
  induction l with
  | nil => split <;> rfl
  | cons e l ih =>
    simp only [keepRuns, List.map_cons, List.filter_cons] at ih ⊢
    by_cases ht : t = .keep
    · subst ht
      simp only [if_true] at ih
      simp [ih]
    · simp only [ht, if_false] at ih
      have : (t == Reading.keep) = false := by simpa using ht
      simp [this, ih, ht]

/-- Marking node `j` as met leaves every other node as it was. -/
theorem getD_setIfInBounds (known : Array Bool) (j j' : Nat) :
    (known.setIfInBounds j true)[j']?.getD true = (j == j' || known[j']?.getD true) := by
  rw [Array.getElem?_setIfInBounds]
  by_cases h : j = j'
  · subst h
    by_cases hj : j < known.size <;> simp [hj]
  · simp [h]

/-- Only next node `j` runs the getters of next node `j`. -/
theorem ownerOf_next {input : Input} {j j' : Nat} (h : ownerOf input j = .next j') : j' = j := by
  unfold ownerOf at h
  split at h <;> simp_all

/-- Along capture's walk, a getter of an object only `next` holds runs once at most, when its node
is visited, and a getter the walks that keep subtrees in place run, once at most, when its object
joins the closure. -/
theorem captureStep_spec (input : Input) (stop : Nat → Bool) :
    ∀ fuel pending (known : Array Bool) closure (reads : List Read),
      (∀ j k, (reads.map Prod.snd).count (.next j, k) ≤
        if known[j]?.getD true then 1 else 0) →
      (∀ i k, (keepRuns reads).count (.cur i, k) ≤ if closure.contains i then 1 else 0) →
      (∀ j k, ((captureStep input stop fuel pending known closure reads).2.map Prod.snd).count
        (.next j, k) ≤ 1) ∧
      ∀ i k, (keepRuns (captureStep input stop fuel pending known closure reads).2).count
        (.cur i, k) ≤ 1
  | 0, _, known, closure, reads, hf, hk =>
    ⟨fun j k => (hf j k).trans (by split <;> simp),
      fun i k => (hk i k).trans (by split <;> simp)⟩
  | _ + 1, [], known, closure, reads, hf, hk =>
    ⟨fun j k => (hf j k).trans (by split <;> simp),
      fun i k => (hk i k).trans (by split <;> simp)⟩
  | fuel + 1, (j, occupant, keeps) :: rest, known, closure, reads, hf, hk => by
    simp only [captureStep]
    split
    · exact captureStep_spec input stop fuel rest known closure reads hf hk
    · rename_i hj
      obtain ⟨hcur, hok⟩ := keepAt_spec input stop closure j occupant keeps
      have hnext : ∀ j' k,
          (keepAt input stop closure j occupant keeps).2.count (.next j', k) = 0 :=
        fun j' k => List.count_eq_zero_of_not_mem fun hm => by
          obtain ⟨s, hs⟩ := hcur _ hm
          simp at hs
      split
      · rename_i walked wr heq
        rw [heq] at hok hnext
        obtain ⟨hdis, hcount⟩ := hok walked rfl
        apply captureStep_spec
        · intro j' k
          have h1 := hf j' k
          have h2 := hnext j' k
          simp only [List.map_append, List.map_map, List.count_append, getD_setIfInBounds]
          have : (Prod.snd ∘ fun e : Owner × String => (Reading.keep, e)) = id := rfl
          rw [this, List.map_id, h2]
          split at h1 <;> simp_all
        · intro i k
          have h1 := hk i k
          have h2 := hcount i k
          rw [keepRuns_append, keepRuns_tagged, if_pos rfl, List.count_append]
          simp only [List.contains_append, Bool.or_eq_true] at h1 h2 ⊢
          by_cases hw : walked.contains i = true
          · have hc : closure.contains i = false := hdis i (by simpa using hw)
            simp only [hw, hc, if_true, true_or] at h1 h2 ⊢
            simp at h1
            omega
          · have hw' : walked.contains i = false := by simpa using hw
            simp only [hw', Bool.false_eq_true, false_or, if_false] at h1 h2 ⊢
            omega
      · rename_i wr heq
        rw [heq] at hnext
        apply captureStep_spec
        · intro j' k
          have h1 := hf j' k
          have h2 : wr.count (.next j', k) = 0 := hnext j' k
          have h3 := count_tagged (ownerOf input j) (getters_nodup (input.next.node j))
            (Owner.next j', k)
          simp only [List.map_append, List.map_map, List.count_append, getD_setIfInBounds]
          have e1 : (Prod.snd ∘ fun e : Owner × String => (Reading.discard, e)) = id := rfl
          have e2 : (Prod.snd ∘ fun k : String => (Reading.observe, ownerOf input j, k)) =
              fun k => (ownerOf input j, k) := rfl
          rw [e1, e2, List.map_id, h2]
          by_cases ho : Owner.next j' = ownerOf input j
          · have hjj := ownerOf_next ho.symm
            subst hjj
            have hk0 : known[j']?.getD true = false := by simpa using hj
            dsimp only at h3
            rw [if_pos ho] at h3
            simp only [hk0, Bool.false_eq_true, if_false] at h1
            simp only [beq_self_eq_true, Bool.true_or, if_true]
            omega
          · dsimp only at h3
            rw [if_neg ho] at h3
            split at h1 <;> split <;> simp_all
        · intro i k
          have hobs : keepRuns ((getters (input.next.node j)).map
              fun k => (Reading.observe, ownerOf input j, k)) = [] := by
            simp [keepRuns]
          rw [keepRuns_append, keepRuns_append, keepRuns_tagged, hobs]
          simpa using hk i k


/-- Reading `next` runs each getter of an object only `next` holds at most once, and the walks
that keep subtrees in place run each getter at most once: a subtree kept in place is read once. -/
theorem captureReads_once (input : Input) (r : Nat) :
    (∀ j k, ((captureReads input r).map Prod.snd).count (.next j, k) ≤ 1) ∧
    ∀ i k, (keepRuns (captureReads input r)).count (.cur i, k) ≤ 1 :=
  captureStep_spec input _ _ _ _ [] [] (by simp) (by simp [keepRuns])

/-- A count of `freshCounts` is the number of reads of its next node and key. -/
theorem mem_freshCounts {reads : List Read} {e : Nat × String × Nat}
    (he : e ∈ freshCounts reads) :
    e.2.2 = (reads.map Prod.snd).count (.next e.1, e.2.1) := by
  simp only [freshCounts, readCounts, List.mem_filterMap, List.mem_map] at he
  obtain ⟨_, ⟨⟨o, k⟩, _, rfl⟩, h⟩ := he
  cases o with
  | cur i => simp at h
  | next j =>
    simp only [Option.some.injEq] at h
    subst h
    rfl

/-- A getter of an object that only `next` holds runs at most once in a call: only reading `next`
runs it (`Outcome.freshGets`). -/
theorem freshGets_le_one (input : Input) : ∀ e ∈ (run input).freshGets, e.2.2 ≤ 1 := by
  simp only [run]
  split
  · intro e he
    rw [mem_freshCounts he]
    exact (captureReads_once _ _).1 _ _
  · simp

/-- A pass writes only to objects its decision keeps at unpinned nodes. -/
theorem mem_writesOfDecision {input : Input} {pin : Array Bool} {kept : Array (Option Nat)}
    {e : Nat × String × String} (h : e ∈ writesOfDecision input pin kept) :
    ∃ j, j < input.next.nodes.size ∧ pin[j]?.getD false = false ∧
      kept[j]?.bind id = some e.1 := by
  simp only [writesOfDecision, List.mem_flatMap, List.mem_range] at h
  obtain ⟨j, hj, he⟩ := h
  split at he
  · rename_i i hi
    split at he
    · simp at he
    · rename_i hp
      obtain ⟨⟨k, w⟩, _, rfl⟩ := List.mem_map.1 he
      exact ⟨j, hj, by simpa using hp, hi⟩
  · simp at he

/-- A pass reads back only objects its decision keeps at unpinned nodes. -/
theorem mem_readbackKeys {input : Input} {pin : Array Bool} {kept : Array (Option Nat)}
    {i : Nat} {k : String} (h : (i, k) ∈ readbackKeys input pin kept) :
    ∃ j, j < input.next.nodes.size ∧ pin[j]?.getD false = false ∧
      kept[j]?.bind id = some i := by
  have h := (eraseDups_spec _).1 _ h
  simp only [List.mem_flatMap, List.mem_range] at h
  obtain ⟨j, hj, he⟩ := h
  split at he
  · simp at he
  · rename_i hp
    split at he
    · rename_i i' hi
      obtain ⟨k', _, hk'⟩ := List.mem_filterMap.1 he
      split at hk'
      · simp only [Option.some.injEq, Prod.mk.injEq] at hk'
        obtain ⟨rfl, rfl⟩ := hk'
        exact ⟨j, hj, by simpa using hp, hi⟩
      · simp at hk'
    · simp at he

/-- The comparison reads only objects that are candidates of some node. -/
theorem mem_capturedKeys {input : Input} {al : Discovery} {i : Nat} {k : String}
    (h : (i, k) ∈ capturedKeys input al) : ∃ c : Nat, i ∈ al.candidates[c]?.getD [] := by
  have h := (eraseDups_spec _).1 _ h
  simp only [List.mem_flatMap, List.mem_range] at h
  obtain ⟨c, _, i', hi', hk⟩ := h
  obtain ⟨k', _, hk'⟩ := List.mem_filterMap.1 hk
  split at hk'
  · simp only [Option.some.injEq, Prod.mk.injEq] at hk'
    obtain ⟨rfl, rfl⟩ := hk'
    exact ⟨c, hi'⟩
  · simp at hk'

/-- A pinned node has no candidate. -/
theorem discover_pinned_candidates (input : Input) (j : Nat)
    (h : (discover input).pinned[j]?.getD false = true) :
    (discover input).candidates[j]?.getD [] = [] := by
  cases hr : input.next.root with
  | prim p =>
    simp only [discover, hr]
    by_cases hj : j < input.next.nodes.size <;> simp [hj]
  | ref r =>
    simp only [discover, hr] at h ⊢
    generalize visitStep input.cur input.next input.next.budget [(r, input.cur.root.refId)]
      (Array.replicate input.next.nodes.size false)
      (Array.replicate input.next.nodes.size none) [] = vs at h ⊢
    obtain ⟨order, first⟩ := vs
    simp only at h ⊢
    rw [Array.getElem?_mapIdx]
    cases (candidateStep input.cur input.next (input.next.budget * (input.cur.nodes.size + 1))
      [(r, input.cur.root.refId)] (Array.replicate input.next.nodes.size []))[j]? with
    | none => simp
    | some cs => simp [h]

/-- An object kept in place is neither changed nor read back: given that each current object is at
most one next node, no pass writes to the object at a pinned node, and read as `current` its
getters run at most once, in the comparison of another node it is a candidate of, which only an
object `current` also holds at another position is. -/
theorem run_pinned (raw : Input)
    (hsame : ∀ (a b x : Nat), raw.same[a]?.bind id = some x → raw.same[b]?.bind id = some x →
      a = b)
    (j i : Nat) (hj : j < raw.next.nodes.size)
    (hpin : (discover (normalized raw)).pinned[j]?.getD false = true)
    (hs : raw.same[j]?.bind id = some i) :
    (∀ e ∈ (run raw).allWrites, e.1 ≠ i) ∧ ∀ e ∈ (run raw).gets, e.1 = i →
      e.2.2 ≤ 1 ∧
        ∃ c : Nat, c ≠ j ∧ i ∈ (discover (normalized raw)).candidates[c]?.getD [] := by
  have hj' : j < (normalized raw).next.nodes.size := by
    simpa [normalized, Graph.normalize] using hj
  have hkeep : ∀ (r : Nat) (kept : Array (Option Nat)),
      kept ∈ rounds (normalized raw) (discover (normalized raw)) r → ∀ b : Nat,
      (discover (normalized raw)).pinned[b]?.getD false = false →
      kept[b]?.bind id ≠ some i := by
    intro r kept hk b hb hbi
    have := demote_pinned (normalized raw) (discover (normalized raw))
      (discover (normalized raw)).pinned r (fun a b x _ _ _ _ ha hb => hsame a b x ha hb) _ kept hk
      b j i hj' hpin hs hbi
    subst this
    simp [hpin] at hb
  have hwrites : ∀ (r : Nat),
      ∀ e ∈ ((rounds (normalized raw) (discover (normalized raw)) r).map
      (writesOfDecision (normalized raw) (discover (normalized raw)).pinned)).flatten.eraseDups,
      e.1 ≠ i := by
    intro r e he hei
    obtain ⟨l, hl, he⟩ := List.mem_flatten.1 ((eraseDups_spec _).1 _ he)
    obtain ⟨kept, hk, rfl⟩ := List.mem_map.1 hl
    obtain ⟨b, _, hb, hbi⟩ := mem_writesOfDecision he
    exact hkeep r kept hk b hb (hei ▸ hbi)
  have hgets : ∀ (r : Nat) (captured : List (Nat × String))
      (readbacks : List (List (Nat × String))),
      (∀ l ∈ readbacks, ∃ kept ∈ rounds (normalized raw) (discover (normalized raw)) r,
        l = readbackKeys (normalized raw) (discover (normalized raw)).pinned kept) →
      ∀ e ∈ getCounts captured readbacks, e.1 = i →
        e.2.2 ≤ 1 ∧ (i, e.2.1) ∈ captured := by
    intro r captured readbacks hr e he hei
    simp only [getCounts, List.mem_map] at he
    obtain ⟨⟨i', k⟩, hmem, rfl⟩ := he
    dsimp only at hei ⊢
    subst hei
    have hnil : ∀ l ∈ readbacks, l.contains (i', k) = false := by
      intro l hl
      obtain ⟨kept, hk, rfl⟩ := hr l hl
      rw [Bool.eq_false_iff]
      intro hc
      obtain ⟨b, _, hb, hbi⟩ := mem_readbackKeys (List.contains_iff_mem.1 hc)
      exact hkeep r kept hk b hb hbi
    rw [List.filter_eq_nil_iff.2 fun l hl => by rw [hnil l hl]; decide]
    refine ⟨by split <;> simp, ?_⟩
    rcases List.mem_append.1 ((eraseDups_spec _).1 _ hmem) with h | h
    · exact h
    · obtain ⟨l, hl, hk⟩ := List.mem_flatten.1 h
      have := hnil l hl
      rw [List.contains_iff_mem.2 hk] at this
      exact absurd this (by decide)
  simp only [run]
  split
  · dsimp only
    split
    · simp
    · rename_i _ _ _ r _ _ _
      simp only [publish]
      refine ⟨hwrites r, fun e he hei => ?_⟩
      obtain ⟨hle, hcap⟩ := hgets r _ _ (fun l hl => by
        split at hl
        · simp at hl
        · obtain ⟨kept, hk, rfl⟩ := List.mem_map.1 hl
          exact ⟨kept, hk, rfl⟩) e he hei
      obtain ⟨c, hc⟩ := mem_capturedKeys hcap
      refine ⟨hle, c, fun hcj => ?_, hc⟩
      subst hcj
      rw [discover_pinned_candidates _ _ hpin] at hc
      simp at hc
  · simp


private def plainObject (fields : List (String × Val)) : Obj :=
  .object .object (fields.map fun (k, v) => (k, .data v Attrs.plain)) true

private def getterObject : Obj :=
  .object .object [("g", .accessor (.prim (.num 1)) (some true) true true)] true

/-- `current` holds `p`, which has a getter, at `b` and inside `c`, which refers to `current`;
`next` holds both at their positions. -/
private def insideRootRef : Input where
  cur := ⟨#[plainObject [("a", .ref 1), ("b", .ref 2)],
    plainObject [("up", .ref 0), ("p", .ref 2)], getterObject], .ref 0⟩
  next := ⟨#[plainObject [("a", .ref 1), ("b", .ref 2), ("n", .prim (.num 1))],
    plainObject [("up", .ref 3), ("p", .ref 2)], getterObject,
    plainObject [("a", .ref 1), ("b", .ref 2)]], .ref 0⟩
  same := #[none, some 1, some 2, some 0]

/-- `p`, kept in place, runs its getter twice while `next` is read: the walk from `c` reads it
before it meets `current`, and the walk that keeps it reads it again. -/
example : ((captureReads insideRootRef 0).filter (·.2 == (.cur 2, "g"))).map Prod.fst =
    [.discard, .keep] ∧ (discover insideRootRef).pinned[2]? = some true := by
  decide +kernel

/-- `current` holds `x`, which has a getter, inside `p`; `next` holds `p` in place and `x` as a
`Map` value. -/
private def mapValue : Input where
  cur := ⟨#[plainObject [("b", .ref 1), ("m", .ref 2)], plainObject [("x", .ref 3)],
    .map [(.prim (.num 1), .prim (.num 0))], getterObject], .ref 0⟩
  next := ⟨#[plainObject [("b", .ref 1), ("m", .ref 3)], plainObject [("x", .ref 2)],
    getterObject, .map [(.prim (.num 1), .ref 2)]], .ref 0⟩
  same := #[none, some 1, some 3, none]

/-- `x`, inside a subtree kept in place, runs its getter twice while `next` is read: the walk that
keeps `p` reads it, and capture visits it as the `Map` value. -/
example : ((captureReads mapValue 0).filter (·.2 == (.cur 3, "g"))).map Prod.fst =
    [.keep, .observe] ∧ (discover mapValue).pinned[2]? = some true := by
  decide +kernel

/-! ## Demands -/

/-- No demand asks a candidate's own node for another object: every demand comes from an admitted
candidate `x` of some node `c`, through a fixed slot, and names `c` only with `x` itself. -/
theorem demands_satisfiable (input : Input) (al : Discovery) (c' x' : Nat)
    (h : (c', x') ∈ demands input al) :
    ∃ c x, x ∈ al.candidates[c]?.getD [] ∧ admitted input al.pinned c x = true ∧
      (Val.ref x', Val.ref c') ∈ fixedPairs (input.cur.node x) (input.next.node c) ∧
      (c' = c → x' = x) := by
  simp only [demands, List.mem_flatMap, List.mem_range] at h
  obtain ⟨c, _, x, hx, hmem⟩ := h
  split at hmem
  · rename_i hadm
    simp only [List.mem_filter, fixedRequirements, List.mem_filterMap] at hmem
    obtain ⟨⟨⟨cv, nv⟩, hpair, hsome⟩, hcond⟩ := hmem
    cases cv with
    | prim p => cases nv <;> simp at hsome
    | ref y =>
      cases nv with
      | prim q => simp at hsome
      | ref d =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsome
        obtain ⟨rfl, rfl⟩ := hsome
        refine ⟨c, x, hx, hadm, hpair, fun hc => ?_⟩
        subst hc
        simpa using hcond
  · simp at hmem

/-- The fixed slots of an admitted candidate that hold objects require each node to keep one
object, and a pinned node the object it is. -/
theorem admitted_pins (input : Input) (pin : Array Bool) (c x x' c' : Nat)
    (h : admitted input pin c x = true)
    (hp : (Val.ref x', Val.ref c') ∈ fixedPairs (input.cur.node x) (input.next.node c)) :
    (pin[c']?.getD false = true → input.same[c']?.bind id = some x') ∧
      ∀ y, (Val.ref y, Val.ref c') ∈ fixedPairs (input.cur.node x) (input.next.node c) →
        y = x' := by
  simp only [admitted, Bool.and_eq_true, List.all_eq_true] at h
  have hx := h.2 _ hp
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq,
    List.all_eq_true] at hx
  refine ⟨fun hpin => ?_, fun y hy => ?_⟩
  · rcases hx.1 with h1 | h1
    · simp [hpin] at h1
    · exact h1
  · have h2 := hx.2 _ hy
    simp only [bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq] at h2
    rcases h2 with h2 | h2
    · exact absurd trivial h2
    · exact h2

/-- A demand on a pinned node asks for the object it is: a candidate that would require another
object there is not admitted, so it reorders no node. -/
theorem demands_pinned (input : Input) (al : Discovery) (c' x' : Nat)
    (h : (c', x') ∈ demands input al) (hpin : al.pinned[c']?.getD false = true) :
    input.same[c']?.bind id = some x' := by
  obtain ⟨c, x, _, hadm, hpair, _⟩ := demands_satisfiable input al c' x' h
  exact (admitted_pins input al.pinned c x x' c' hadm hpair).1 hpin

/-! ## Fresh copies -/

/-- The origins of a published result are the final decision: a node's origin is the object it
keeps, and none when the node is a fresh copy. -/
theorem publish_origins (input : Input) (al : Discovery) (pin : Array Bool)
    (rounds : List (Array (Option Nat))) (kept : Array (Option Nat)) (r : Nat) :
    (publish input al pin rounds kept r).origins = kept := rfl

/-- A node the decision keeps nothing at holds a copy of `next`'s node, made as `snapshot` makes
it (`Obj.copy`). -/
theorem publish_fresh (input : Input) (al : Discovery) (pin : Array Bool)
    (rounds : List (Array (Option Nat))) (kept : Array (Option Nat)) (r j : Nat)
    (hj : j < input.next.nodes.size) (h : kept[j]?.bind id = none) :
    (publish input al pin rounds kept r).nodes[j]? = some (input.next.node j).copy := by
  simp [publish, hj, h]

/-! ## Counterexamples -/

section Counterexamples

/-- A rule that writes every key of `next`, equal or not. -/
def objectWritesAll (nFields : List (String × Slot)) : List (String × String) :=
  nFields.map fun (k, _) => (k, "set")

/-- A rule that re-adds a moved key as a plain data property. -/
def keptObjectNaive (proto : Proto) (cFields : List (String × Slot)) (extensible : Bool)
    (nFields : List (String × Slot)) : Obj :=
  .object proto (nFields.map fun (k, ns) =>
    (k, match cFields.lookup k with
      | some cs =>
        if (retainPrefix (cFields.map Prod.fst) (nFields.map Prod.fst)).contains k then
          slotWith cs ns.value
        else .data ns.value (.copied cs.enumerable)
      | none => .data ns.value (.copied ns.enumerable))) extensible

private def one : List (String × Slot) := [("a", .data (.prim .null) ⟨true, true, true⟩)]

/-- Writing every key breaks the promise: `a` is retained and unchanged, so the reference does
not write it. -/
example : ("a", "set") ∉ (objectWrites (fun _ => none) one one).1 ∧
    ("a", "set") ∈ objectWritesAll one := by
  decide

private def readOnlyFirst : List (String × Slot) :=
  [("a", .data (.prim .null) ⟨false, true, false⟩), ("b", .data (.prim .null) ⟨true, true, true⟩)]
private def swapped : List (String × Slot) :=
  [("b", .data (.prim .null) ⟨true, true, true⟩), ("a", .data (.prim .null) ⟨false, true, false⟩)]

/-- Re-adding a moved key as plain data breaks the promise: `a` moves and keeps its read-only,
non-configurable attributes in the reference. -/
example :
    (fieldsOf (keptObject .object readOnlyFirst true swapped)).lookup "a" =
      some (.data (.prim .null) ⟨false, true, false⟩) ∧
    (fieldsOf (keptObjectNaive .object readOnlyFirst true swapped)).lookup "a" =
      some (.data (.prim .null) ⟨true, true, true⟩) := by
  decide

end Counterexamples

end Reconcile.Spec.Reconcile

namespace Reconcile.Spec.Produce

open Reconcile.Spec

/-- The keep conditions on node `i` with respect to a set `set`: a current node equals its draft
and refers only to nodes of the set; a created object refers only to kept created objects and to
the changed copies of dates, buffers and views (`changedCopy`). -/
def Keeps (cur : Graph) (heap : Array Obj) (set : List Nat) (i : Nat) : Prop :=
  i < heap.size ∧ (i < cur.nodes.size → heap[i]? = some (cur.node i)) ∧
    ((heap[i]?.getD default).refs.all fun r =>
      if i < cur.nodes.size then set.contains r else createdKeeps cur heap set r) = true

theorem createdKeeps_mono (cur : Graph) (heap : Array Obj) {s t : List Nat}
    (h : ∀ x ∈ s, x ∈ t) (r : Nat) (hr : createdKeeps cur heap s r = true) :
    createdKeeps cur heap t r = true := by
  simp only [createdKeeps, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.contains_iff_mem] at hr ⊢
  rcases hr with ⟨hn, hs⟩ | hd
  · exact Or.inl ⟨hn, h _ hs⟩
  · exact Or.inr hd

theorem keeps_mono (cur : Graph) (heap : Array Obj) {s t : List Nat} (h : ∀ x ∈ s, x ∈ t)
    (i : Nat) (hi : Keeps cur heap s i) : Keeps cur heap t i := by
  obtain ⟨h1, h2, h3⟩ := hi
  refine ⟨h1, h2, ?_⟩
  simp only [List.all_eq_true] at h3 ⊢
  intro r hr
  have := h3 r hr
  split at this <;> split
  · simp only [List.contains_iff_mem] at this ⊢
    exact h _ this
  · contradiction
  · contradiction
  · exact createdKeeps_mono cur heap h r this

/-- The pruning step of `kept.go` keeps every node of a set closed under `Keeps`. -/
theorem kept_go_superset (cur : Graph) (heap : Array Obj) (S : List Nat)
    (hS : ∀ i ∈ S, Keeps cur heap S i) :
    ∀ fuel set, (∀ i ∈ S, i ∈ set) → ∀ i ∈ S, i ∈ kept.go cur heap fuel set := by
  intro fuel
  induction fuel with
  | zero => intro set h i hi; simpa [kept.go] using h i hi
  | succ fuel ih =>
    intro set h i hi
    simp only [kept.go]
    split
    · exact h i hi
    · refine ih _ ?_ i hi
      intro x hx
      simp only [List.mem_filter]
      exact ⟨h x hx, (keeps_mono cur heap h x (hS x hx)).2.2⟩

/-- Every node whose subtree the recipe left unchanged is kept: `kept` contains every set closed
under the keep conditions, so the result reuses the parts of `current` the recipe did not change
wherever it can. -/
theorem kept_greatest (cur : Graph) (heap : Array Obj) (S : List Nat)
    (hS : ∀ i ∈ S, Keeps cur heap S i) : ∀ i ∈ S, i ∈ kept cur heap := by
  intro i hi
  simp only [kept]
  refine kept_go_superset cur heap S hS _ _ ?_ i hi
  intro x hx
  obtain ⟨h1, h2, _⟩ := hS x hx
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨h1, h2⟩

theorem kept_go_closed (cur : Graph) (heap : Array Obj) :
    ∀ fuel set, set.length ≤ fuel →
      (∀ i ∈ set, i < heap.size ∧ (i < cur.nodes.size → heap[i]? = some (cur.node i))) →
      ∀ i ∈ kept.go cur heap fuel set, Keeps cur heap (kept.go cur heap fuel set) i := by
  intro fuel
  induction fuel with
  | zero =>
    intro set hlen _ i hi
    have : set = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst this
    simp [kept.go] at hi
  | succ fuel ih =>
    intro set hlen hloc i hi
    simp only [kept.go] at hi ⊢
    split at hi <;> split
    · rename_i heq _
      have hall := List.length_filter_eq_length_iff.mp heq
      have := hall i hi
      exact ⟨(hloc i hi).1, (hloc i hi).2, by simpa using this⟩
    · contradiction
    · contradiction
    · rename_i hne _
      apply ih
      · have hle := List.length_filter_le (fun i =>
          (heap[i]?.getD default).refs.all fun r =>
            if i < cur.nodes.size then set.contains r else createdKeeps cur heap set r) set
        omega
      · intro x hx
        exact hloc x (List.mem_filter.mp hx).1
      · exact hi

/-- Every kept node satisfies the keep conditions with respect to the kept set: a kept current
object is unchanged and refers only to kept objects, so the result keeps nothing the recipe
changed. -/
theorem kept_closed (cur : Graph) (heap : Array Obj) :
    ∀ i ∈ kept cur heap, Keeps cur heap (kept cur heap) i := by
  intro i hi
  simp only [kept] at hi ⊢
  refine kept_go_closed cur heap heap.size _ ?_ ?_ i hi
  · exact Nat.le_trans (List.length_filter_le _ _) (by simp [List.length_range])
  · intro x hx
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
    exact hx

/-! ## Snapshot -/

/-- `snapshot` makes one copy per source node. -/
theorem snapshot_size (cur : Graph) : (snapshot cur).nodes.size = cur.nodes.size := by
  simp [snapshot]

/-- Each copy is `Obj.copy` of its source node, the copy `reconcile` adds (`publish_fresh`). -/
theorem snapshot_copy (cur : Graph) (i : Nat) :
    (snapshot cur).nodes[i]? = cur.nodes[i]?.map Obj.copy := by
  simp [snapshot]

/-- Every origin is fresh: the copy shares no object with the source. -/
theorem snapshot_fresh (cur : Graph) : ∀ o ∈ (snapshot cur).origins, o = .fresh := by
  intro o ho
  simp only [snapshot, Array.mem_map] at ho
  obtain ⟨_, _, rfl⟩ := ho
  rfl

end Reconcile.Spec.Produce
