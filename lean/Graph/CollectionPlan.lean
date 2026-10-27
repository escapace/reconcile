import Mathlib.Data.List.Nodup
import Property.PropertyPlacement
import Spec.Promises
import Types.MapEntries

/-!
# Collection publication

`reconcile` publishes a kept `Map`'s or `Set`'s entries with the built-in methods (`publish` in
`src/types/shared/collection.ts`), which `publish` models. It reads the current entries once and
walks them with a position into the next entries. A current entry whose key is the next entry's
at the position stays in place and the position advances; a `Map` entry among them is put with its
next value unless it holds that value already, a put that would change nothing (`put_same`). Every
other current entry is deleted. The next entries from the position on are then put in order, which
appends them. The runtime's `unchanged` flag records that the walk wrote nothing.

With duplicate-free keys on both sides:

* the writes reach exactly the next entries, in order (`publish_result`);
* the current keys left in place are greedy matching's, `PropertyPlacement.matched` of the next
  keys over the current ones (`publish_retained`, `publish_position`). That is
  `Spec.Reconcile.retainPrefix`: the longest prefix of the next keys that occurs, in order, among
  the current keys, so the fewest entries move;
* the deletes are the other current keys, in current order (`publish_deletes`), and the puts are
  the retained entries whose value differs followed by the next entries past the retained prefix,
  in next order (`publish_puts`);
* with the next entries' keys and values resolved to the objects the decision keeps, these are
  the reference's writes, `Spec.Reconcile.entryWrites`, kind by kind and in order
  (`publish_entryWrites`, `publish_perm_entryWrites`), and they leave the kept collection holding
  the next entries (`publish_reaches_next`).

Whatever the keys, `unchanged` holds exactly when the walk wrote nothing (`unchanged_iff_writes`),
which is exactly when the current entries are the next ones (`writes_eq_nil_iff`,
`unchanged_iff`).

A `Map` is `Types.MapEntries`; a `Set` is the case `β = Unit`, where no value is put. The runtime
compares keys with SameValueZero, over the canonical keys a `Map` holds, and values with
`Object.is`; the model compares both by equality, a premise.
-/

namespace Reconcile.CollectionPlan

open Reconcile.Types.MapEntries Reconcile.PropertyPlacement

variable {α β : Type}

/-- A write through a built-in method: `set` of a key and value, or `delete` of a key. -/
inductive Write (α β : Type) where
  | put (key : α) (value : β)
  | delete (key : α)
  deriving DecidableEq, Repr

/-- The keys writes delete, in order. -/
def deletes (writes : List (Write α β)) : List α :=
  writes.filterMap fun | .delete key => some key | .put .. => none

/-- The entries writes put, in order. -/
def puts (writes : List (Write α β)) : List (α × β) :=
  writes.filterMap fun | .put key value => some (key, value) | .delete _ => none

@[simp] theorem deletes_append (a b : List (Write α β)) :
    deletes (a ++ b) = deletes a ++ deletes b :=
  List.filterMap_append

@[simp] theorem puts_append (a b : List (Write α β)) : puts (a ++ b) = puts a ++ puts b :=
  List.filterMap_append

@[simp] theorem deletes_map_put (l : List (α × β)) :
    deletes (l.map fun e => (.put e.1 e.2 : Write α β)) = [] := by
  induction l <;> simp_all [deletes]

@[simp] theorem puts_map_put (l : List (α × β)) :
    puts (l.map fun e => (.put e.1 e.2 : Write α β)) = l := by
  induction l <;> simp_all [puts]

variable [DecidableEq α]

/-- A write's effect on the entries. -/
def Write.apply (m : List (α × β)) : Write α β → List (α × β)
  | .put key value => Types.MapEntries.put key value m
  | .delete key => remove key m

/-- The entries after writes, applied in order. -/
def applyAll (m : List (α × β)) (writes : List (Write α β)) : List (α × β) :=
  writes.foldl Write.apply m

theorem applyAll_append (m : List (α × β)) (ws ws' : List (Write α β)) :
    applyAll m (ws ++ ws') = applyAll (applyAll m ws) ws' :=
  List.foldl_append

/-- Putting entries whose keys are new and distinct appends them. -/
theorem applyAll_puts (m entries : List (α × β)) (hn : (keys (m ++ entries)).Nodup) :
    applyAll m (entries.map fun e => .put e.1 e.2) = m ++ entries := by
  induction entries generalizing m with
  | nil => simp [applyAll]
  | cons e rest ih =>
    have hm : e.1 ∉ keys m := by
      intro h
      rw [keys_append, List.nodup_append] at hn
      exact hn.2.2 _ h _ (by simp [keys]) rfl
    have := ih (m ++ [e]) (by simpa using hn)
    simp only [applyAll, List.map_cons, List.foldl_cons, Write.apply] at this ⊢
    rw [put_new m e.1 e.2 hm]
    simpa using this

variable [DecidableEq β]

/-- The walk's state: the position into the next entries, the writes so far, and whether none was
made. -/
structure Walk (α β : Type) where
  position : Nat
  writes : List (Write α β)
  unchanged : Bool

/-- One current entry: kept in place when its key is the next entry's at the position, its value
put when it differs, and the position advances; otherwise deleted. -/
def step (next : List (α × β)) (s : Walk α β) (entry : α × β) : Walk α β :=
  match next[s.position]? with
  | some wanted =>
    if entry.1 = wanted.1 then
      if entry.2 = wanted.2 then ⟨s.position + 1, s.writes, s.unchanged⟩
      else ⟨s.position + 1, s.writes ++ [.put entry.1 wanted.2], false⟩
    else ⟨s.position, s.writes ++ [.delete entry.1], false⟩
  | none => ⟨s.position, s.writes ++ [.delete entry.1], false⟩

/-- `publish`: the walk over the current entries `cur`, then the next entries from its position
on, put in order. `position` is where the walk stopped: the number of entries kept in place. -/
def publish (cur next : List (α × β)) : Walk α β :=
  let s := cur.foldl (step next) ⟨0, [], true⟩
  let added := next.drop s.position
  ⟨s.position, s.writes ++ added.map (fun e => .put e.1 e.2), s.unchanged && added.isEmpty⟩

/-! ## The result -/

/-- One step keeps the live entries the next entries before the position followed by the current
entries not yet walked. -/
theorem step_result (next m : List (α × β)) (s : Walk α β) (c : α × β) (cs : List (α × β))
    (h : applyAll m s.writes = next.take s.position ++ c :: cs)
    (hn : (keys (next.take s.position ++ c :: cs)).Nodup) :
    applyAll m (step next s c).writes = next.take (step next s c).position ++ cs ∧
      (keys (next.take (step next s c).position ++ cs)).Nodup := by
  obtain ⟨k, v⟩ := c
  have hk : (keys (next.take s.position) ++ k :: keys cs).Nodup := by
    simpa [keys] using hn
  have hpre : k ∉ keys (next.take s.position) := fun hm =>
    (List.nodup_append.mp hk).2.2 _ hm _ List.mem_cons_self rfl
  have hpost : k ∉ keys cs := (List.nodup_cons.mp (List.nodup_append.mp hk).2.1).1
  have hdel : applyAll m (s.writes ++ [.delete k]) = next.take s.position ++ cs := by
    rw [applyAll_append, h]
    exact remove_middle _ _ k v hpre hpost
  have hdeln : (keys (next.take s.position ++ cs)).Nodup := by
    refine hn.sublist ?_
    simp only [keys, List.map_append, List.map_cons]
    exact List.Sublist.append_left (List.sublist_cons_self _ _) _
  unfold step
  cases hp : next[s.position]? with
  | none => exact ⟨hdel, hdeln⟩
  | some n =>
    obtain ⟨k', v'⟩ := n
    have htake : next.take (s.position + 1) = next.take s.position ++ [(k', v')] := by
      rw [List.take_add_one, hp]; rfl
    dsimp only
    by_cases hkey : k = k'
    · subst hkey
      have hn' : (keys (next.take (s.position + 1) ++ cs)).Nodup := by
        simpa [keys, htake] using hk
      by_cases hv : v = v'
      · subst hv
        rw [if_pos rfl, if_pos rfl]
        exact ⟨by rw [h, htake]; simp, hn'⟩
      · rw [if_pos rfl, if_neg hv]
        refine ⟨?_, hn'⟩
        rw [applyAll_append, h, htake]
        simpa [applyAll, Write.apply] using put_middle (next.take s.position) cs k v v' hpre
    · rw [if_neg hkey]
      exact ⟨hdel, hdeln⟩

theorem walk_result (next m : List (α × β)) :
    ∀ (cs : List (α × β)) (s : Walk α β), applyAll m s.writes = next.take s.position ++ cs →
      (keys (next.take s.position ++ cs)).Nodup →
      applyAll m (cs.foldl (step next) s).writes = next.take (cs.foldl (step next) s).position
  | [], s, h, _ => by simpa using h
  | c :: cs, s, h, hn => by
    obtain ⟨h', hn'⟩ := step_result next m s c cs h hn
    exact walk_result next m cs (step next s c) h' hn'

/-- With duplicate-free keys, publication's writes reach exactly the next entries, in order. -/
theorem publish_result (cur next : List (α × β)) (hc : (keys cur).Nodup)
    (hn : (keys next).Nodup) : applyAll cur (publish cur next).writes = next := by
  have hw := walk_result next cur cur ⟨0, [], true⟩ (by simp [applyAll]) (by simpa using hc)
  simp only [publish]
  rw [applyAll_append, hw, applyAll_puts _ _ (by rwa [List.take_append_drop]),
    List.take_append_drop]

/-! ## The retained entries and the writes -/

omit [DecidableEq β] in
theorem keys_take_matched (l : List (α × β)) (ks : List α) :
    keys (l.take (matched (keys l) ks).length) = matched (keys l) ks := by
  rw [keys, List.map_take]
  exact (List.prefix_iff_eq_take.mp (matched_prefix (keys l) ks)).symm

theorem matched_nil_right (ds : List α) : matched ds [] = [] := by
  cases ds <;> rfl

/-- Entries none of which is `c` filter alike against `cs` and `c :: cs`. -/
theorem filter_not_mem_cons (l cs : List (α × β)) (c : α × β) (h : ∀ e ∈ l, e ≠ c) :
    l.filter (fun e => decide (e ∉ c :: cs)) = l.filter (fun e => decide (e ∉ cs)) :=
  List.filter_congr fun e he => by simp [h e he]

omit [DecidableEq β] in
/-- An entry among the next ones the walk will keep is not a current entry it has passed. -/
theorem ne_of_matched (l cs : List (α × β)) (c : α × β) (hc : c.1 ∉ keys cs) :
    ∀ e ∈ l.take (matched (keys l) (keys cs)).length, e ≠ c := by
  intro e he hec
  have hk : e.1 ∈ keys (l.take (matched (keys l) (keys cs)).length) :=
    List.mem_map_of_mem he
  rw [keys_take_matched] at hk
  exact hc (hec ▸ (matched_sublist _ _).subset hk)

theorem walk_writes (next : List (α × β)) :
    ∀ (cs : List (α × β)) (s : Walk α β), (keys cs).Nodup →
      (cs.foldl (step next) s).position =
          s.position + (matched (keys (next.drop s.position)) (keys cs)).length ∧
        deletes (cs.foldl (step next) s).writes = deletes s.writes ++
          (keys cs).filter (· ∉ matched (keys (next.drop s.position)) (keys cs)) ∧
        puts (cs.foldl (step next) s).writes = puts s.writes ++
          ((next.drop s.position).take
            (matched (keys (next.drop s.position)) (keys cs)).length).filter (· ∉ cs)
  | [], s, _ => by simp [matched_nil_right, keys]
  | (k, v) :: cs, s, hn => by
    have hn' : (k :: keys cs).Nodup := by simpa [keys] using hn
    have hc : k ∉ keys cs := (List.nodup_cons.mp hn').1
    have hcs : (keys cs).Nodup := (List.nodup_cons.mp hn').2
    have hkeys : keys ((k, v) :: cs) = k :: keys cs := rfl
    rw [List.foldl_cons, hkeys]
    cases hd : next.drop s.position with
    | nil =>
      have hp : next[s.position]? = none := by rw [← List.head?_drop, hd]; rfl
      have hstep : step next s (k, v) = ⟨s.position, s.writes ++ [.delete k], false⟩ := by
        simp [step, hp]
      obtain ⟨h1, h2, h3⟩ := walk_writes next cs ⟨s.position, s.writes ++ [.delete k], false⟩ hcs
      dsimp only at h1 h2 h3
      rw [hd] at h1 h2 h3
      rw [hstep, h1, h2, h3]
      simp [keys, matched, deletes, puts]
    | cons n ns =>
      obtain ⟨k', v'⟩ := n
      have hp : next[s.position]? = some (k', v') := by rw [← List.head?_drop, hd]; rfl
      have hdrop : next.drop (s.position + 1) = ns := by rw [← List.tail_drop, hd]; rfl
      have hkn : keys ((k', v') :: ns) = k' :: keys ns := rfl
      rw [hkn]
      by_cases hkey : k = k'
      · subst hkey
        have hm : matched (k :: keys ns) (k :: keys cs) = k :: matched (keys ns) (keys cs) := by
          simp [matched]
        have hdel : (k :: keys cs).filter (· ∉ k :: matched (keys ns) (keys cs)) =
            (keys cs).filter (· ∉ matched (keys ns) (keys cs)) := by
          rw [List.filter_cons]
          simp only [List.mem_cons, true_or, not_true_eq_false, decide_false, Bool.false_eq_true,
            if_false]
          exact List.filter_congr fun x hx => by
            have : x ≠ k := fun e => hc (e ▸ hx)
            simp [this]
        have hne := ne_of_matched ns cs (k, v) hc
        have hncs : (k, v') ∉ cs := fun hm => hc (List.mem_map_of_mem (f := Prod.fst) hm)
        rw [hm, hdel, List.length_cons, List.take_succ_cons]
        by_cases hv : v = v'
        · subst hv
          have hstep : step next s (k, v) = ⟨s.position + 1, s.writes, s.unchanged⟩ := by
            simp [step, hp]
          obtain ⟨h1, h2, h3⟩ := walk_writes next cs ⟨s.position + 1, s.writes, s.unchanged⟩ hcs
          dsimp only at h1 h2 h3
          rw [hdrop] at h1 h2 h3
          rw [hstep, h1, h2, h3, List.filter_cons, filter_not_mem_cons _ _ _ hne]
          refine ⟨by omega, rfl, ?_⟩
          simp
        · have hstep : step next s (k, v) =
              ⟨s.position + 1, s.writes ++ [.put k v'], false⟩ := by
            simp [step, hp, hv]
          obtain ⟨h1, h2, h3⟩ :=
            walk_writes next cs ⟨s.position + 1, s.writes ++ [.put k v'], false⟩ hcs
          dsimp only at h1 h2 h3
          rw [hdrop] at h1 h2 h3
          rw [hstep, h1, h2, h3, List.filter_cons, filter_not_mem_cons _ _ _ hne]
          have hin : (k, v') ∉ (k, v) :: cs := by
            simp only [List.mem_cons, not_or]
            exact ⟨fun e => hv (Prod.ext_iff.mp e).2.symm, hncs⟩
          refine ⟨by omega, by simp [deletes], ?_⟩
          simp [puts, hin]
      · have hm : matched (k' :: keys ns) (k :: keys cs) = matched (k' :: keys ns) (keys cs) := by
          simp [matched, hkey]
        have hstep : step next s (k, v) = ⟨s.position, s.writes ++ [.delete k], false⟩ := by
          simp [step, hp, hkey]
        obtain ⟨h1, h2, h3⟩ := walk_writes next cs ⟨s.position, s.writes ++ [.delete k], false⟩ hcs
        dsimp only at h1 h2 h3
        rw [hd, hkn] at h1 h2 h3
        have hkm : k ∉ matched (k' :: keys ns) (keys cs) := fun h =>
          hc ((matched_sublist _ _).subset h)
        have hne : ∀ e ∈ ((k', v') :: ns).take (matched (k' :: keys ns) (keys cs)).length,
            e ≠ (k, v) := by
          simpa [hkn] using ne_of_matched ((k', v') :: ns) cs (k, v) hc
        rw [hm, hstep, h1, h2, h3, filter_not_mem_cons _ _ _ hne]
        refine ⟨rfl, ?_, by simp [puts]⟩
        simp [deletes, hkm]

/-- The walk keeps in place as many current entries as greedy matching keeps keys. -/
theorem publish_position (cur next : List (α × β)) (hc : (keys cur).Nodup) :
    (publish cur next).position = (matched (keys next) (keys cur)).length := by
  simpa [publish] using (walk_writes next cur ⟨0, [], true⟩ hc).1

/-- Publication deletes the current keys outside the retained prefix, in current order. -/
theorem publish_deletes (cur next : List (α × β)) (hc : (keys cur).Nodup) :
    deletes (publish cur next).writes = (keys cur).filter (· ∉ matched (keys next) (keys cur)) := by
  have h := (walk_writes next cur ⟨0, [], true⟩ hc).2.1
  simp only [List.drop_zero] at h
  simp only [publish, deletes_append, deletes_map_put, h, List.append_nil]
  simp only [deletes, List.filterMap_nil, List.nil_append]

/-- Publication puts the retained entries whose value differs and then the next entries past the
retained prefix, in next order. -/
theorem publish_puts (cur next : List (α × β)) (hc : (keys cur).Nodup) :
    puts (publish cur next).writes =
      (next.take (matched (keys next) (keys cur)).length).filter (· ∉ cur) ++
        next.drop (matched (keys next) (keys cur)).length := by
  have h := walk_writes next cur ⟨0, [], true⟩ hc
  simp only [List.drop_zero, Nat.zero_add] at h
  simp only [publish, puts_append, puts_map_put, h.1, h.2.2]
  simp only [puts, List.filterMap_nil, List.nil_append]

/-- The current keys publication keeps in place, in order, are greedy matching's: the longest
prefix of the next keys that occurs in order among the current keys,
`Spec.Reconcile.retainPrefix`. -/
theorem publish_retained (cur next : List (α × β)) (hc : (keys cur).Nodup) :
    (keys cur).filter (· ∉ deletes (publish cur next).writes) = matched (keys next) (keys cur) := by
  rw [publish_deletes cur next hc]
  calc (keys cur).filter (· ∉ (keys cur).filter (· ∉ matched (keys next) (keys cur)))
      = (keys cur).filter (· ∈ matched (keys next) (keys cur)) :=
        List.filter_congr fun k hk => by simp [hk]
    _ = matched (keys next) (keys cur) := filter_mem_sublist (matched_sublist _ _) hc

/-! ## The reference's writes

`Spec.Reconcile.entryWrites` lists the writes the reference makes to a kept `Map` or `Set`: the
current keys outside the retained prefix, deleted, in current order, then, in next order, the
retained keys whose value differs and every other next key, set. Publication reads the current
entries as they are and resolves each next entry's key and value to the object the decision keeps
there (`entryKey`, `resolveKey`); a fresh object is no current key. Its deletes and its puts are
the reference's, in order (`publish_entryWrites`), so it makes exactly the reference's writes, in
the runtime's interleaving (`publish_perm_entryWrites`). -/

section Reference

open Reconcile.Spec Reconcile.Spec.Reconcile

/-- The key publication writes for a next entry's key: the current key it resolves to, or a fresh
object. -/
def entryKey (identity : Nat → Option Nat) (k : Val) : EntryKey :=
  match resolveKey identity k with
  | some ck => .current ck
  | none => .fresh k

/-- A kept collection's current entries as publication reads them: each key with its value, which
a `Set` lacks. -/
def currentEntries (cKeys : List Val) (cValue : Val → Option Val) :
    List (EntryKey × Option (Option Val)) :=
  cKeys.map fun k => (.current k, (cValue k).map some)

/-- The next entries as publication resolves them. -/
def nextEntries (identity : Nat → Option Nat) (nKeys : List Val) (nValue : Val → Option Val) :
    List (EntryKey × Option (Option Val)) :=
  nKeys.map fun k => (entryKey identity k, (nValue k).map (resolveKey identity))

/-- A write as the reference reports it. -/
def label : Write EntryKey (Option (Option Val)) → EntryKey × String
  | .put k _ => (k, "set")
  | .delete k => (k, "delete")

/-- The current key a key names, if any. -/
def keyOf : EntryKey → Option Val
  | .current k => some k
  | .fresh _ => none

theorem keyOf_current (k : Val) : keyOf (.current k) = some k := rfl

theorem keyOf_entryKey (identity : Nat → Option Nat) (k : Val) :
    keyOf (entryKey identity k) = resolveKey identity k := by
  unfold entryKey
  split <;> simp_all [keyOf]

theorem keyOf_eq_some {x : EntryKey} {k : Val} : keyOf x = some k ↔ x = .current k := by
  cases x <;> simp [keyOf]

theorem entryKey_eq_current {identity : Nat → Option Nat} {k ck : Val} :
    entryKey identity k = .current ck ↔ resolveKey identity k = some ck := by
  unfold entryKey
  split <;> simp_all

theorem entryKey_inj {identity : Nat → Option Nat}
    (hinj : ∀ a b x, identity a = some x → identity b = some x → a = b) {a b : Val}
    (h : entryKey identity a = entryKey identity b) : a = b := by
  cases ha : resolveKey identity a <;> cases hb : resolveKey identity b <;>
    simp only [entryKey, ha, hb, EntryKey.current.injEq, EntryKey.fresh.injEq, reduceCtorEq] at h
  · exact h
  · subst h
    exact resolveKey_inj hinj ha hb

/-- `differs` asks whether the next value resolves to anything but the current one. -/
theorem differs_iff (identity : Nat → Option Nat) (cv nv : Val) :
    differs identity cv nv = true ↔ resolveKey identity nv ≠ some cv := by
  cases nv with
  | prim p => simpa [differs, resolveKey, bne_iff_ne] using ne_comm
  | ref c =>
    cases h : identity c
    · simp [differs, resolveKey, h]
    · simpa [differs, resolveKey, h, bne_iff_ne] using ne_comm

/-- Greedy matching commutes with a renaming that tells each current key from every desired one. -/
theorem matched_map {γ δ : Type} [DecidableEq γ] [DecidableEq δ] (g : γ → δ) :
    ∀ (ds cs : List γ), (∀ c ∈ cs, ∀ d ∈ ds, g c = g d → c = d) →
      matched (ds.map g) (cs.map g) = (matched ds cs).map g
  | [], _, _ => by simp [matched]
  | _ :: _, [], _ => by simp [matched_nil_right]
  | d :: ds, c :: cs, h => by
    have hcd : g c = g d ↔ c = d :=
      ⟨h c List.mem_cons_self d List.mem_cons_self, fun e => e ▸ rfl⟩
    simp only [List.map_cons, matched]
    by_cases e : c = d
    · rw [if_pos (hcd.mpr e), if_pos e, List.map_cons,
        matched_map g ds cs fun c' hc' d' hd' =>
          h c' (List.mem_cons_of_mem _ hc') d' (List.mem_cons_of_mem _ hd')]
    · rw [if_neg (fun h' => e (hcd.mp h')), if_neg e]
      exact matched_map g (d :: ds) cs fun c' hc' d' hd' => h c' (List.mem_cons_of_mem _ hc') d' hd'

/-- Filtering by a condition met where `P` fails is the `filterMap` that keeps those elements. -/
theorem filterMap_ite {γ δ : Type} (l : List γ) (P : γ → Bool) (Q : γ → Prop) [DecidablePred Q]
    (f : γ → δ) (h : ∀ x ∈ l, P x = decide (Q x)) :
    l.filterMap (fun x => if P x then none else some (f x)) =
      (l.filter fun x => decide ¬Q x).map f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx := h x List.mem_cons_self
    have ih := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    by_cases hq : Q x <;> simp [hx, hq, ih]

/-- With distinct keys on both sides, identities that keep each object at one node at most, and a
value at every key of a `Map` and none at a `Set`'s, publication deletes and puts exactly the
reference's writes, kind by kind and in order. -/
theorem publish_entryWrites (identity : Nat → Option Nat) (cKeys nKeys : List Val)
    (cValue nValue : Val → Option Val) (hc : cKeys.Nodup) (hn : nKeys.Nodup)
    (hinj : ∀ a b x, identity a = some x → identity b = some x → a = b)
    (hvalues : ∀ ck ∈ cKeys, ∀ k ∈ nKeys, (cValue ck).isSome = (nValue k).isSome) :
    entryWrites identity cKeys nKeys cValue nValue =
      (deletes (publish (currentEntries cKeys cValue)
          (nextEntries identity nKeys nValue)).writes).map (·, "delete") ++
        (puts (publish (currentEntries cKeys cValue)
          (nextEntries identity nKeys nValue)).writes).map (fun e => (e.1, "set")) := by
  have hkc : keys (currentEntries cKeys cValue) = cKeys.map .current := by
    simp [keys, currentEntries, Function.comp_def]
  have hkn : keys (nextEntries identity nKeys nValue) = nKeys.map (entryKey identity) := by
    simp [keys, nextEntries, Function.comp_def]
  have hcn : (keys (currentEntries cKeys cValue)).Nodup :=
    hkc ▸ hc.map fun _ _ e => EntryKey.current.inj e
  rw [publish_deletes _ _ hcn, publish_puts _ _ hcn, hkc, hkn]
  generalize hM : matched (nKeys.map (entryKey identity)) (cKeys.map EntryKey.current) = M
  have hret : retainPrefix (cKeys.map some) (nKeys.map (resolveKey identity)) = M.map keyOf := by
    rw [← hM, ← matched_map keyOf]
    · simp only [retainPrefix, List.map_map, Function.comp_def, keyOf_entryKey, keyOf_current]
    · intro c hc' d _ e
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc'
      exact (keyOf_eq_some.mp e.symm).symm
  have hmem : ∀ ck, (M.map keyOf).contains (some ck) = decide (EntryKey.current ck ∈ M) := by
    intro ck
    rw [Bool.eq_iff_iff, List.contains_iff_mem, decide_eq_true_iff, List.mem_map]
    exact ⟨fun ⟨x, hx, e⟩ => keyOf_eq_some.mp e ▸ hx, fun hx => ⟨_, hx, rfl⟩⟩
  have hsub : M.Sublist (cKeys.map EntryKey.current) := hM ▸ matched_sublist _ _
  have hpre : M.IsPrefix (nKeys.map (entryKey identity)) := hM ▸ matched_prefix _ _
  -- The kept next keys are the first `M.length` of them.
  have htake : (nKeys.take M.length).map (entryKey identity) = M := by
    rw [List.map_take]; exact (List.prefix_iff_eq_take.mp hpre).symm
  simp only [entryWrites, hret]
  congr 1
  · -- The deletes: the current keys outside the retained prefix.
    rw [List.filter_map, List.map_map]
    refine filterMap_ite cKeys _ (fun k => EntryKey.current k ∈ M)
      (fun k => (EntryKey.current k, "delete")) fun k _ => ?_
    rw [hmem]
    cases hk : decide (EntryKey.current k ∈ M)
    · simp
    · have : some k ∈ nKeys.map (resolveKey identity) := by
        have hr := (retainPrefix_prefix (cKeys.map some) (nKeys.map (resolveKey identity))).subset
        rw [hret] at hr
        exact hr (List.contains_iff_mem.mp ((hmem k).trans hk))
      rw [List.contains_iff_mem.mpr this]
      rfl
  · -- The puts: the retained entries whose value differs, then the rest of next, in order.
    unfold nextEntries
    rw [List.map_append, ← List.map_take, ← List.map_drop, List.filter_map, List.map_map,
      List.map_map]
    conv_lhs => rw [← List.take_append_drop M.length nKeys]
    rw [List.filterMap_append]
    have hdisj := List.disjoint_take_drop hn (Nat.le_refl M.length)
    congr 1
    · -- Retained next keys: set when the value resolves to anything but the current one.
      have hkept : ∀ k ∈ nKeys.take M.length, ∃ ck ∈ cKeys,
          resolveKey identity k = some ck ∧ EntryKey.current ck ∈ M := by
        intro k hk
        have hkM : entryKey identity k ∈ M := htake ▸ List.mem_map_of_mem hk
        obtain ⟨ck, hck, e⟩ := List.mem_map.mp (hsub.subset hkM)
        exact ⟨ck, hck, entryKey_eq_current.mp e.symm, e ▸ hkM⟩
      have hvk : ∀ k ∈ nKeys.take M.length, k ∈ nKeys := fun k hk =>
        (List.take_sublist _ _).subset hk
      generalize nKeys.take M.length = l at hkept hvk ⊢
      induction l with
      | nil => rfl
      | cons k l ih =>
        obtain ⟨ck, hck, hres, hckM⟩ := hkept k List.mem_cons_self
        have ih := ih (fun k' hk' => hkept k' (List.mem_cons_of_mem _ hk'))
          (fun k' hk' => hvk k' (List.mem_cons_of_mem _ hk'))
        have hentry : entryKey identity k = .current ck := entryKey_eq_current.mpr hres
        have hin : ((EntryKey.current ck, (nValue k).map (resolveKey identity)) ∈
            currentEntries cKeys cValue) ↔
            (cValue ck).map some = (nValue k).map (resolveKey identity) := by
          rw [currentEntries, List.mem_map]
          constructor
          · rintro ⟨c, _, e⟩
            simp only [Prod.mk.injEq, EntryKey.current.injEq] at e
            exact e.1 ▸ e.2
          · intro e
            exact ⟨ck, hck, by rw [e]⟩
        have hv := hvalues ck hck k (hvk k List.mem_cons_self)
        rw [List.filterMap_cons, ih, List.filter_cons]
        simp only [Function.comp_apply, hres, hmem, hckM, decide_true, if_true, hentry]
        cases hcv : cValue ck <;> cases hnv : nValue k <;> rw [hcv, hnv] at hin
        · simp only [Option.map_none, iff_true] at hin
          simp [hin]
        · simp [hcv, hnv] at hv
        · simp [hcv, hnv] at hv
        · rename_i cv nv
          simp only [Option.map_some, Option.some.injEq] at hin
          by_cases hd : resolveKey identity nv = some cv
          · have hdiff : differs identity cv nv = false :=
              Bool.eq_false_iff.mpr fun h => (differs_iff identity cv nv).mp h hd
            simp [hdiff, hin.mpr hd.symm]
          · have hdiff : differs identity cv nv = true := (differs_iff identity cv nv).mpr hd
            have hout : (EntryKey.current ck, some (resolveKey identity nv)) ∉
                currentEntries cKeys cValue := fun h => hd (hin.mp h).symm
            simp [hdiff, hout, hentry]
    · -- The other next keys: each is set.
      refine (List.filterMap_congr fun k hk => ?_).trans (congrFun List.filterMap_eq_map _)
      cases hres : resolveKey identity k with
      | none => simp [entryKey, hres]
      | some ck =>
        have hout : EntryKey.current ck ∉ M := by
          intro hm
          rw [← htake] at hm
          obtain ⟨k', hk', e⟩ := List.mem_map.mp hm
          have : k' = k := entryKey_inj hinj (e.trans (entryKey_eq_current.mpr hres).symm)
          exact hdisj (this ▸ hk') hk
        simp only [hmem, hout, decide_false, Bool.false_eq_true, if_false, Function.comp_apply]
        simp [entryKey, hres]

/-- Whatever the order, a write log holds its deletes and its puts. -/
theorem perm_label (w : List (Write EntryKey (Option (Option Val)))) :
    (w.map label).Perm
      ((deletes w).map (·, "delete") ++ (puts w).map (fun e => (e.1, "set"))) := by
  induction w with
  | nil => simp [deletes, puts]
  | cons x w ih =>
    cases x with
    | delete k => simpa [label, deletes, puts] using ih
    | put k v =>
      simp only [List.map_cons, label, deletes, puts, List.filterMap_cons] at ih ⊢
      exact (ih.cons _).trans List.perm_middle.symm

/-- Publication makes exactly the reference's writes to a kept `Map` or `Set`, in the runtime's
order. -/
theorem publish_perm_entryWrites (identity : Nat → Option Nat) (cKeys nKeys : List Val)
    (cValue nValue : Val → Option Val) (hc : cKeys.Nodup) (hn : nKeys.Nodup)
    (hinj : ∀ a b x, identity a = some x → identity b = some x → a = b)
    (hvalues : ∀ ck ∈ cKeys, ∀ k ∈ nKeys, (cValue ck).isSome = (nValue k).isSome) :
    ((publish (currentEntries cKeys cValue) (nextEntries identity nKeys nValue)).writes.map
      label).Perm (entryWrites identity cKeys nKeys cValue nValue) := by
  rw [publish_entryWrites identity cKeys nKeys cValue nValue hc hn hinj hvalues]
  exact perm_label _

/-- So the reference's writes, applied with the built-in methods, leave a kept `Map` or `Set`
holding the next entries, each key and value the object the decision keeps there. -/
theorem publish_reaches_next (identity : Nat → Option Nat) (cKeys nKeys : List Val)
    (cValue nValue : Val → Option Val) (hc : cKeys.Nodup) (hn : nKeys.Nodup)
    (hinj : ∀ a b x, identity a = some x → identity b = some x → a = b) :
    applyAll (currentEntries cKeys cValue)
        (publish (currentEntries cKeys cValue) (nextEntries identity nKeys nValue)).writes =
      nextEntries identity nKeys nValue := by
  refine publish_result _ _ ?_ ?_
  · simpa [keys, currentEntries, Function.comp_def] using
      hc.map fun _ _ e => EntryKey.current.inj e
  · have : (nKeys.map (entryKey identity)).Nodup :=
      hn.map_on fun _ _ _ _ e => entryKey_inj hinj e
    simpa [keys, nextEntries, Function.comp_def] using this

end Reference

/-! ## The `unchanged` flag -/

theorem step_writes (next : List (α × β)) (s : Walk α β) (c : α × β) :
    ((step next s c).writes = s.writes ∧ (step next s c).unchanged = s.unchanged) ∨
      ∃ w, (step next s c).writes = s.writes ++ [w] ∧ (step next s c).unchanged = false := by
  unfold step
  split
  · split
    · split
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr ⟨_, rfl, rfl⟩
    · exact .inr ⟨_, rfl, rfl⟩
  · exact .inr ⟨_, rfl, rfl⟩

/-- The walk's flag stays set exactly while it writes nothing. -/
theorem walk_unchanged (next : List (α × β)) :
    ∀ (cs : List (α × β)) (s : Walk α β), ∃ more,
      (cs.foldl (step next) s).writes = s.writes ++ more ∧
        (cs.foldl (step next) s).unchanged = (s.unchanged && more.isEmpty)
  | [], s => ⟨[], by simp⟩
  | c :: cs, s => by
    obtain ⟨more, hw, hu⟩ := walk_unchanged next cs (step next s c)
    simp only [List.foldl_cons]
    rcases step_writes next s c with ⟨sw, su⟩ | ⟨w, sw, su⟩
    · exact ⟨more, by rw [hw, sw], by rw [hu, su]⟩
    · exact ⟨w :: more, by rw [hw, sw]; simp, by rw [hu, su]; simp⟩

/-- A step that wrote nothing kept the next entry at the position, which is the current one. -/
theorem step_quiet (next : List (α × β)) (s : Walk α β) (c : α × β)
    (h : (step next s c).writes = s.writes) :
    next.drop s.position = c :: next.drop (step next s c).position := by
  obtain ⟨k, v⟩ := c
  unfold step at h ⊢
  cases hp : next[s.position]? with
  | none => simp [hp] at h
  | some n =>
    obtain ⟨k', v'⟩ := n
    simp only [hp] at h ⊢
    by_cases hkey : k = k'
    · by_cases hv : v = v'
      · subst hkey hv
        rw [if_pos rfl, if_pos rfl, ← List.tail_drop]
        have h1 : (next.drop s.position).head? = some (k, v) := by rw [List.head?_drop, hp]
        cases hd : next.drop s.position with
        | nil => simp [hd] at h1
        | cons x xs =>
          simp only [hd, List.head?_cons, Option.some.injEq] at h1
          simp [h1]
      · simp [hkey, hv] at h
    · simp [hkey] at h

/-- A walk that wrote nothing passed the next entries from its position on, in order. -/
theorem walk_quiet (next : List (α × β)) :
    ∀ (cs : List (α × β)) (s : Walk α β), (cs.foldl (step next) s).writes = s.writes →
      next.drop s.position = cs ++ next.drop (cs.foldl (step next) s).position
  | [], _, _ => rfl
  | c :: cs, s, h => by
    rw [List.foldl_cons] at h ⊢
    obtain ⟨more, hw, -⟩ := walk_unchanged next cs (step next s c)
    have hq : (step next s c).writes = s.writes := by
      rcases step_writes next s c with ⟨sw, -⟩ | ⟨w, sw, -⟩
      · exact sw
      · have := congrArg List.length (hw.symm.trans h)
        simp [sw] at this
    rw [step_quiet next s c hq, walk_quiet next cs (step next s c) (h.trans hq.symm)]
    rfl

/-- A walk over the next entries themselves writes nothing. -/
theorem walk_same (next : List (α × β)) :
    ∀ (cs : List (α × β)) (s : Walk α β) (r : List (α × β)), next.drop s.position = cs ++ r →
      cs.foldl (step next) s = ⟨s.position + cs.length, s.writes, s.unchanged⟩
  | [], s, _, _ => by simp
  | c :: cs, s, r, h => by
    have hp : next[s.position]? = some c := by rw [← List.head?_drop, h]; rfl
    have hstep : step next s c = ⟨s.position + 1, s.writes, s.unchanged⟩ := by
      simp [step, hp]
    have hdrop : next.drop (s.position + 1) = cs ++ r := by
      rw [← List.tail_drop, h]; rfl
    simp only [List.foldl_cons, hstep]
    rw [walk_same next cs ⟨s.position + 1, s.writes, s.unchanged⟩ r hdrop]
    simp only [List.length_cons, Walk.mk.injEq, and_true]
    omega

/-- The runtime's `unchanged` flag holds exactly when publication wrote nothing. -/
theorem unchanged_iff_writes (cur next : List (α × β)) :
    (publish cur next).unchanged = true ↔ (publish cur next).writes = [] := by
  obtain ⟨more, hw, hu⟩ := walk_unchanged next cur ⟨0, [], true⟩
  simp only [publish, hw, hu, List.nil_append, Bool.true_and, Bool.and_eq_true,
    List.isEmpty_iff, List.append_eq_nil_iff, List.map_eq_nil_iff]

/-- Publication writes nothing exactly when the current entries are the next ones, in order and
with their values. -/
theorem writes_eq_nil_iff (cur next : List (α × β)) :
    (publish cur next).writes = [] ↔ cur = next := by
  constructor
  · intro h
    simp only [publish, List.append_eq_nil_iff, List.map_eq_nil_iff] at h
    have hq := walk_quiet next cur ⟨0, [], true⟩ h.1
    simpa [h.2] using hq.symm
  · rintro rfl
    have := walk_same cur cur ⟨0, [], true⟩ [] (by simp)
    simp [publish, this]

/-- Publication reports `unchanged` exactly when the current entries are the next ones. -/
theorem unchanged_iff (cur next : List (α × β)) :
    (publish cur next).unchanged = true ↔ cur = next :=
  (unchanged_iff_writes cur next).trans (writes_eq_nil_iff cur next)

omit [DecidableEq β] in
/-- Putting an entry's own value changes nothing, so the runtime skips such puts. -/
theorem put_same (a b : List (α × β)) (k : α) (v : β) (ha : k ∉ keys a) :
    Types.MapEntries.put k v (a ++ (k, v) :: b) = a ++ (k, v) :: b :=
  put_middle a b k v v ha

/-- Counterexample for a plan that keeps only a common prefix in place: for current `[b, a]` and
next `[a]` the walk deletes only `b`, and `a` stays in place, though it follows a deleted entry. -/
example : (publish [("b", 1), ("a", 1)] [("a", 1)]).writes = [.delete "b"] := by decide

end Reconcile.CollectionPlan
