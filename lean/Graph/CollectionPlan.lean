import Mathlib.Data.List.Nodup

/-!
# Collection publication plan

`reconcile` matches `Map` and `Set` entries by position (`publish` in
`src/types/shared/collection.ts`). Up to the first position whose key differs, each entry stays in
place and takes its next value; from there on the current entries are deleted and the next ones
appended. A `Map` is modelled as its entries in insertion order, with the built-in `set`
(`put`: an existing key keeps its position) and `delete` (`remove`); a `Set` is the same with a
unit value. With duplicate-free keys and an equal key prefix, the plan reaches exactly the next
entries in order (`plan_eq`).
-/

namespace Reconcile.CollectionPlan

variable {α β : Type} [DecidableEq α]

/-- The keys of entries, in order. -/
def keys (m : List (α × β)) : List α := m.map Prod.fst

/-- `Map.prototype.set`: an existing key keeps its position, a new key is appended. -/
def put (m : List (α × β)) (k : α) (v : β) : List (α × β) :=
  if k ∈ keys m then m.map (fun e => if e.1 = k then (k, v) else e) else m ++ [(k, v)]

/-- `Map.prototype.delete`. -/
def remove (m : List (α × β)) (k : α) : List (α × β) := m.filter (fun e => e.1 ≠ k)

/-- Puts each entry in order. -/
def putAll (m : List (α × β)) (entries : List (α × β)) : List (α × β) :=
  entries.foldl (fun acc e => put acc e.1 e.2) m

/-- The plan for current entries `cur`, next entries `next` and shared key prefix length `p`. -/
def plan (cur next : List (α × β)) (p : Nat) : List (α × β) :=
  putAll ((keys (cur.drop p)).foldl remove (putAll cur (next.take p))) (next.drop p)

omit [DecidableEq α] in
theorem keys_append (a b : List (α × β)) : keys (a ++ b) = keys a ++ keys b := by
  simp [keys]

theorem map_keep (a : List (α × β)) (k : α) (v : β) (h : k ∉ keys a) :
    a.map (fun e => if e.1 = k then (k, v) else e) = a := by
  induction a with
  | nil => rfl
  | cons e rest ih =>
    simp only [keys, List.map_cons, List.mem_cons, not_or] at h
    simp only [List.map_cons]
    rw [if_neg (fun he => h.1 he.symm), ih h.2]

/-- Putting a key held once replaces its value in place. -/
theorem put_middle (a b : List (α × β)) (k : α) (v₀ v : β) (ha : k ∉ keys a) (hb : k ∉ keys b) :
    put (a ++ (k, v₀) :: b) k v = a ++ (k, v) :: b := by
  have hmem : k ∈ keys (a ++ (k, v₀) :: b) := by simp [keys]
  simp only [put, hmem, if_true, List.map_append, List.map_cons]
  rw [map_keep a k v ha, map_keep b k v hb]

/-- Putting a new key appends it. -/
theorem put_new (m : List (α × β)) (k : α) (v : β) (h : k ∉ keys m) :
    put m k v = m ++ [(k, v)] := by
  simp [put, h]

/-- Putting the entries of a prefix with the same keys replaces its values in place. -/
theorem putAll_prefix (pre next rest acc : List (α × β)) (hk : keys pre = keys next)
    (hn : (keys (acc ++ pre ++ rest)).Nodup) :
    putAll (acc ++ pre ++ rest) next = acc ++ next ++ rest := by
  induction pre generalizing next acc with
  | nil =>
    cases next with
    | nil => simp [putAll]
    | cons e t => simp [keys] at hk
  | cons e pre ih =>
    cases next with
    | nil => simp [keys] at hk
    | cons f next =>
      simp only [keys, List.map_cons, List.cons.injEq] at hk
      obtain ⟨hkey, hrest⟩ := hk
      have hnodup : (keys acc ++ e.1 :: (keys pre ++ keys rest)).Nodup := by
        simpa [keys, List.append_assoc] using hn
      rw [List.nodup_append] at hnodup
      obtain ⟨-, hmid, hdisj⟩ := hnodup
      have hka : e.1 ∉ keys acc := fun h => hdisj _ h _ (List.mem_cons_self) rfl
      have hkb : e.1 ∉ keys (pre ++ rest) := by
        rw [keys_append]; exact (List.nodup_cons.mp hmid).1
      change (f :: next).foldl (fun acc e => put acc e.1 e.2) (acc ++ e :: pre ++ rest) = _
      simp only [List.foldl_cons]
      have hstep : put (acc ++ e :: pre ++ rest) f.1 f.2 = (acc ++ [f]) ++ pre ++ rest := by
        rw [← hkey]
        have : acc ++ e :: pre ++ rest = acc ++ (e.1, e.2) :: (pre ++ rest) := by simp
        rw [this, put_middle acc (pre ++ rest) e.1 e.2 f.2 hka hkb]
        simp [hkey]
      rw [hstep]
      have := ih next (acc ++ [f]) hrest (by
        have hsame : keys (acc ++ [f] ++ pre ++ rest) = keys (acc ++ e :: pre ++ rest) := by
          simp [keys, hkey]
        rw [hsame]; exact hn)
      simpa [putAll] using this

/-- Deleting the keys of a suffix leaves the prefix. -/
theorem remove_suffix (pre tail : List (α × β)) (hn : (keys (pre ++ tail)).Nodup) :
    (keys tail).foldl remove (pre ++ tail) = pre := by
  induction tail generalizing pre with
  | nil => simp [keys]
  | cons e tail ih =>
    simp only [keys, List.map_cons, List.foldl_cons]
    rw [keys_append, List.nodup_append] at hn
    obtain ⟨hpre, htail, hdisj⟩ := hn
    have htail' : (e.1 :: keys tail).Nodup := by simpa [keys] using htail
    have hpe : e.1 ∉ keys pre := fun h => hdisj _ h _ (by simp [keys]) rfl
    have hte : e.1 ∉ keys tail := (List.nodup_cons.mp htail').1
    have hp : pre.filter (fun x => decide (x.1 ≠ e.1)) = pre :=
      List.filter_eq_self.mpr fun x hx => by
        simp only [ne_eq, decide_eq_true_eq]
        intro h; exact hpe (h ▸ List.mem_map_of_mem hx)
    have ht : tail.filter (fun x => decide (x.1 ≠ e.1)) = tail :=
      List.filter_eq_self.mpr fun x hx => by
        simp only [ne_eq, decide_eq_true_eq]
        intro h; exact hte (h ▸ List.mem_map_of_mem hx)
    have hstep : remove (pre ++ e :: tail) e.1 = pre ++ tail := by
      unfold remove
      rw [List.filter_append, List.filter_cons_of_neg (by simp), hp, ht]
    rw [hstep]
    apply ih
    rw [keys_append, List.nodup_append]
    refine ⟨hpre, (List.nodup_cons.mp htail').2, ?_⟩
    intro x hx y hy
    exact hdisj x hx y (List.mem_cons_of_mem _ hy)

/-- Putting entries whose keys are new and distinct appends them. -/
theorem putAll_append (m entries : List (α × β)) (hn : (keys (m ++ entries)).Nodup) :
    putAll m entries = m ++ entries := by
  induction entries generalizing m with
  | nil => simp [putAll]
  | cons e rest ih =>
    simp only [putAll, List.foldl_cons]
    have hm : e.1 ∉ keys m := by
      intro h
      rw [keys_append, List.nodup_append] at hn
      exact hn.2.2 _ h _ (by simp [keys]) rfl
    rw [put_new m e.1 e.2 hm]
    have := ih (m ++ [e]) (by simpa using hn)
    simpa [putAll] using this

/-- With duplicate-free keys and an equal key prefix of length `p`, the plan reaches the next
entries in order. -/
theorem plan_eq (cur next : List (α × β)) (p : Nat) (hc : (keys cur).Nodup)
    (hn : (keys next).Nodup) (hp : keys (cur.take p) = keys (next.take p)) :
    plan cur next p = next := by
  have h1 : putAll cur (next.take p) = next.take p ++ cur.drop p := by
    have := putAll_prefix (cur.take p) (next.take p) (cur.drop p) [] hp
      (by simpa using hc)
    simpa using this
  have hn2 : (keys (next.take p ++ cur.drop p)).Nodup := by
    have hsame : keys (next.take p ++ cur.drop p) = keys (cur.take p ++ cur.drop p) := by
      rw [keys_append, keys_append, hp]
    rw [hsame, List.take_append_drop]; exact hc
  unfold plan
  rw [h1, remove_suffix (next.take p) (cur.drop p) hn2, putAll_append]
  · exact List.take_append_drop p next
  · rw [List.take_append_drop]; exact hn

/-- Putting an entry's own value changes nothing, so the runtime skips such puts. -/
theorem put_same (a b : List (α × β)) (k : α) (v : β) (ha : k ∉ keys a) (hb : k ∉ keys b) :
    put (a ++ (k, v) :: b) k v = a ++ (k, v) :: b :=
  put_middle a b k v v ha hb

end Reconcile.CollectionPlan
