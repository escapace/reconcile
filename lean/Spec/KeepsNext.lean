import Spec.Promises

/-!
# `reconcile` never changes `next`

`reconcile(current, next)` must not change an object `next` holds, the objects its root reaches
(`heldObjects`). A pass writes only into the current objects its decision keeps and into new
objects, so `next` can change only through a kept current object that `next` also holds.
`Spec.Reconcile.keepsNext` is the rule each decision must pass before its pass writes; `run`
rejects a call whose decision fails it, with `Outcome.changesNext` set.

Node `j` is *untouched* when the decision keeps there the very object the node is
(`untouched`: `kept[j] = same[j]`). The rule (`keepsNext_iff`):

1. a node that keeps an object `next` holds is untouched: no node keeps an object of `next` that is
   another node's own; and
2. every node an untouched node refers to is untouched, a view's buffer included.

Why this rule, and no other:

- **Safety.** The first clause alone keeps every write of a pass that skips untouched nodes out of
  `next` (`writesOfDecision_not_next`, `writesOfDecision_keepsNext`). The second makes the skip
  exact: given that the arguments read each shared object alike (`Coherent`), an untouched node
  whose references are untouched already holds its contents (`untouched_holds`), so it takes no
  write and blocks nothing (`untouched_writesOf`). Skipping untouched nodes then changes no write
  (`writesOfDecision_eq_publishedWrites`), and even the publication of every unpinned node writes
  into no object of `next` (`publishedWrites_not_next`).
- **Exactness.** The second clause is exact: an untouched object, array, `Map` or `Set` node with a
  reference that is not untouched takes a write into `next`'s own object
  (`publishedWrites_child`); a view's buffer is a fixed slot, which the decision keeps as the
  view's own. The first clause is structural: it also rejects a node that keeps an object `next`
  holds elsewhere whose contents already equal the node's, which writes nothing (example
  `equalCopy`). It is kept because it is decided from the decision alone, before any write of the
  pass, without comparing contents; because a later pass, whose identities differ, can need writes
  into the same object; and because the result would otherwise hold an object of `next` at a
  position where `next` holds another, so a later change through `current` would change `next`.
- **Placement.** Every pass that writes passed the check: the passes before the last
  (`demote_dropLast`, `rounds_dropLast_writes_not_next`) and, in a call that succeeds, the last one
  (`run_allWrites_not_next`). A first decision that fails rejects the call before any write
  (`run_changesNext`). A later decision can fail after an earlier one passed (example `laterPass`):
  a node whose first candidate a pass found blocked moves to an object `next` holds. The earlier
  passes wrote only into objects `next` does not hold, so the rejection still comes before any
  write into `next`.
- **Objects in place.** In every decision a pinned node keeps the object it is (`decide_pinned`),
  and everything a pinned node refers to is pinned (`pinned_closed`), so pinned nodes satisfy both
  clauses (`keepsNextAt_pinned`). A call whose `next` holds current objects only where they are
  already in place is never rejected by the rule (`rounds_keepsNext_inPlace`).
- **Necessity.** Dropping either clause lets `next` change: a swap (`swap`) satisfies the second
  clause and writes into both swapped objects, and an object in place as a `Map` value whose
  reference another position takes first (`mapChild`) satisfies the first and writes into that
  object. When `next` holds `current` itself below a new root (`rootCycle`), the root breaks the
  first clause.
- **Algorithm.** `keepsNext` reads the decision, `same` and the references of `next`'s nodes, never
  `current` (`keepsNext_cur`). It is one pass over the nodes that reads the references of the
  untouched nodes only, which publication and readback then skip (`skipped` in `writesOfDecision`,
  `readbackKeys` and `blockedObjects`); later passes still find them at their nodes
  (`writtenPairs`).

`coherent` decides `Coherent` (`coherent_spec`); the examples are coherent inputs.

## Runtime obligations

- After each pass's decision keeps the root, and before that pass allocates or writes, the runtime
  runs the check and throws when it fails. It skips pinned nodes, which pass it
  (`keepsNextAt_pinned`).
- `nextHolds` is the per-call table from each object capture reached in `next` to its captured
  node, which capture already builds: a node is untouched when its target is its own source, and a
  target that is another node's source breaks the first clause. Objects inside a kept subtree are
  no node's target, since discovery offers them to no other node.
- The references of a node are its captured edges, including a view's buffer and a URL's
  `searchParams`. A write into a URL changes the `searchParams` object it owns, and a write into a
  buffer changes every view over it; discovery keeps a URL's `searchParams` node only with its
  URL's own object and a view's buffer node only with the view's own buffer, so the rule sees the
  linked object as a target. A URL node that discovery pins to its own source because its
  `searchParams` stay in place (URL adoption) is untouched.
- `Coherent` is the premise *Getters must not change values* states for `next`: an object `current`
  and `next` share reads the same through both, so its contents are `next`'s.
- An object `next` reaches only through a prototype, a function, another object kept by reference
  or a proxy's target is not one `next` holds; the rule does not see it.
-/

namespace Reconcile.Spec.Reconcile

open Reconcile.Spec

/-! ## The rule -/

theorem nextHolds_iff (input : Input) (x : Nat) :
    nextHolds input x = true ↔
      ∃ r j, input.next.root = .ref r ∧ j ∈ reach input.next r ∧
        input.same[j]?.bind id = some x := by
  unfold nextHolds heldObjects
  cases hr : input.next.root with
  | prim p => simp
  | ref r => simp [List.mem_filterMap]

theorem untouched_iff (input : Input) (kept : Array (Option Nat)) (j : Nat) :
    untouched input kept j = true ↔
      ∃ c, input.same[j]?.bind id = some c ∧ kept[j]?.bind id = some c := by
  unfold untouched
  split
  · rename_i c hc
    simp [hc]
  · rename_i hc
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro c h
    simp_all

/-- The check at one node holds exactly when the node keeps an object `next` holds only if it is
untouched, and when untouched, every node it refers to is untouched. -/
theorem keepsNextAt_iff (input : Input) (kept : Array (Option Nat)) (j : Nat) :
    keepsNextAt input kept j = true ↔
      (∀ x, kept[j]?.bind id = some x → nextHolds input x = true →
        untouched input kept j = true) ∧
      (untouched input kept j = true →
        ∀ d ∈ (input.next.node j).refs, untouched input kept d = true) := by
  unfold keepsNextAt
  split
  · rename_i hk
    simp only [true_iff]
    refine ⟨fun x hx => by simp [hk] at hx, fun hu => ?_⟩
    obtain ⟨c, _, hc⟩ := (untouched_iff input kept j).1 hu
    simp [hk] at hc
  · rename_i x hk
    by_cases hu : untouched input kept j = true
    · simp [hu, List.all_eq_true]
    · rw [if_neg hu]
      constructor
      · intro hn
        refine ⟨fun y hy hy' => ?_, fun h => absurd h hu⟩
        rw [hk] at hy
        cases hy
        simp [hy'] at hn
      · intro ⟨h, _⟩
        cases hx : nextHolds input x
        · rfl
        · exact absurd (h x hk hx) hu

/-- The rule, clause by clause: (1) a node that keeps an object `next` holds is untouched, and (2)
every node an untouched node refers to is untouched. -/
theorem keepsNext_iff (input : Input) (kept : Array (Option Nat)) :
    keepsNext input kept = true ↔
      (∀ j, j < input.next.nodes.size → ∀ x, kept[j]?.bind id = some x →
        nextHolds input x = true → untouched input kept j = true) ∧
      (∀ j, j < input.next.nodes.size → untouched input kept j = true →
        ∀ d ∈ (input.next.node j).refs, untouched input kept d = true) := by
  simp only [keepsNext, List.all_eq_true, List.mem_range, keepsNextAt_iff]
  constructor
  · intro h
    exact ⟨fun j hj => (h j hj).1, fun j hj => (h j hj).2⟩
  · intro h j hj
    exact ⟨h.1 j hj, h.2 j hj⟩

/-- The check reads no object of `current`: it depends on the decision, `same` and `next` alone. -/
theorem keepsNext_cur (input : Input) (g : Graph) (kept : Array (Option Nat)) :
    keepsNext { input with cur := g } kept = keepsNext input kept := rfl

/-! ## Safety -/

/-- A pass publishes, and so writes and reads back, only nodes that are neither pinned nor
untouched. -/
theorem mem_writesOfDecision_published {input : Input} {pin : Array Bool}
    {kept : Array (Option Nat)} {e : Nat × String × String}
    (h : e ∈ writesOfDecision input pin kept) :
    ∃ j, j < input.next.nodes.size ∧ skipped input pin kept j = false ∧
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

/-- **Safety.** A pass whose decision passes the rule's first clause writes into no object `next`
holds: it writes only into objects kept at nodes that are not untouched, and the first clause keeps
every object of `next` at its own node, untouched. -/
theorem writesOfDecision_not_next (input : Input) (pin : Array Bool) (kept : Array (Option Nat))
    (hk : ∀ j, j < input.next.nodes.size → ∀ x, kept[j]?.bind id = some x →
      nextHolds input x = true → untouched input kept j = true) :
    ∀ e ∈ writesOfDecision input pin kept, nextHolds input e.1 = false := by
  intro e he
  obtain ⟨j, hj, hs, hkept⟩ := mem_writesOfDecision_published he
  cases hn : nextHolds input e.1
  · rfl
  · have := hk j hj e.1 hkept hn
    simp [skipped, this] at hs

/-- A pass whose decision keeps `next` unchanged writes into no object `next` holds. -/
theorem writesOfDecision_keepsNext (input : Input) (pin : Array Bool) (kept : Array (Option Nat))
    (hk : keepsNext input kept = true) :
    ∀ e ∈ writesOfDecision input pin kept, nextHolds input e.1 = false :=
  writesOfDecision_not_next input pin kept ((keepsNext_iff input kept).1 hk).1

/-! ## Shared objects read alike

`Coherent` states what the runtime supplies about an object that `current` and `next` share: it is
the same object, so `current`'s node is `next`'s node with each reference renamed to the current
object that node is (`renameObj`, `sameOf`). -/

/-- A value with each reference renamed by `f`. -/
def renameVal (f : Nat → Nat) : Val → Val
  | .prim p => .prim p
  | .ref c => .ref (f c)

/-- A slot with its value renamed by `f`. -/
def renameSlot (f : Nat → Nat) : Slot → Slot
  | .data v a => .data (renameVal f v) a
  | .accessor v s e c => .accessor (renameVal f v) s e c

/-- A node with each reference renamed by `f`. -/
def renameObj (f : Nat → Nat) : Obj → Obj
  | .object p fields ext => .object p (fields.map (Prod.map id (renameSlot f))) ext
  | .array entries ext => .array (entries.map (Option.map (renameVal f))) ext
  | .map entries => .map (entries.map (Prod.map (renameVal f) (renameVal f)))
  | .set members => .set (members.map (renameVal f))
  | .date ms => .date ms
  | .buffer bytes max => .buffer bytes max
  | .view ctor b o l => .view ctor (renameVal f b) o l

/-- The current object next node `c` is, or `c` when it is none. -/
def sameOf (input : Input) (c : Nat) : Nat := (input.same[c]?.bind id).getD c

/-- The arguments read each shared object alike: distinct next nodes are distinct objects, `same`
names next nodes only, a shared object refers only to shared objects, and its current node is its
next node with each reference renamed to the current object that node is, with distinct keys. -/
structure Coherent (input : Input) : Prop where
  inj : ∀ a b x : Nat, input.same[a]?.bind id = some x → input.same[b]?.bind id = some x →
    a = b
  size : input.same.size ≤ input.next.nodes.size
  shared : ∀ j c, input.same[j]?.bind id = some c → ∀ d ∈ (input.next.node j).refs,
    (input.same[d]?.bind id).isSome = true
  node : ∀ j c, input.same[j]?.bind id = some c →
    input.cur.node c = renameObj (sameOf input) (input.next.node j)
  keys : ∀ j c, input.same[j]?.bind id = some c →
    distinctKeys (input.cur.node c) (input.next.node j)

theorem renameSlot_value (f : Nat → Nat) (s : Slot) :
    (renameSlot f s).value = renameVal f s.value := by
  cases s <;> rfl

theorem lookup_map_snd {β : Type} (g : β → β) (k : String) :
    ∀ l : List (String × β), (l.map (Prod.map id g)).lookup k = (l.lookup k).map g
  | [] => rfl
  | (k', b) :: rest => by
    simp only [List.map_cons, Prod.map, id, List.lookup]
    split <;> simp_all [lookup_map_snd g k rest]

theorem lookup_of_mem_nodup {α β : Type} [BEq α] [LawfulBEq α] {k : α} {v : β} :
    ∀ {l : List (α × β)}, (l.map Prod.fst).Nodup → (k, v) ∈ l → l.lookup k = some v
  | [], _, h => by simp at h
  | (k', v') :: rest, hn, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rcases List.mem_cons.1 h with h | h
    · cases h
      simp [List.lookup]
    · have hne : k ≠ k' := fun e => hn.1 ⟨(k, v), h, e⟩
      simp only [List.lookup, beq_false_of_ne hne]
      exact lookup_of_mem_nodup hn.2 h

theorem mem_of_lookup {α β : Type} [BEq α] [LawfulBEq α] {k : α} {v : β} :
    ∀ {l : List (α × β)}, l.lookup k = some v → (k, v) ∈ l
  | [], h => by simp [List.lookup] at h
  | (k', v') :: rest, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i he
      cases h
      rw [eq_of_beq he]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

theorem lookup_map_inj (g h : Val → Val) (k : Val) :
    ∀ l : List (Val × Val), (∀ a ∈ l.map Prod.fst, g a = g k → a = k) →
      (l.map (Prod.map g h)).lookup (g k) = (l.lookup k).map h
  | [], _ => rfl
  | (a, b) :: rest, hg => by
    simp only [List.map_cons, Prod.map, List.lookup]
    by_cases hak : a = k
    · subst hak
      simp
    · have hga : g a ≠ g k := fun e => hak (hg a (by simp) e)
      simp only [beq_false_of_ne (Ne.symm hga), beq_false_of_ne (Ne.symm hak)]
      exact lookup_map_inj g h k rest fun a' ha' e => hg a' (by simp [ha']) e

/-- A value whose references `identity` resolves as `f` renames them does not differ from its
renaming. -/
theorem differs_renameVal (identity : Nat → Option Nat) (f : Nat → Nat) (v : Val)
    (h : ∀ d, v = .ref d → identity d = some (f d)) :
    differs identity (renameVal f v) v = false := by
  cases v with
  | prim p => simp [differs, renameVal]
  | ref d => simp [differs, renameVal, h d rfl]

theorem resolveKey_renameVal (identity : Nat → Option Nat) (f : Nat → Nat) (v : Val)
    (h : ∀ d, v = .ref d → identity d = some (f d)) :
    resolveKey identity v = some (renameVal f v) := by
  cases v with
  | prim p => rfl
  | ref d => simp [resolveKey, renameVal, h d rfl]

theorem identity_of_differs {identity : Nat → Option Nat} {y d : Nat}
    (h : differs identity (.ref y) (.ref d) = false) : identity d = some y := by
  simp only [differs] at h
  split at h
  · rename_i x hx
    simp only [bne_eq_false_iff_eq, Val.ref.injEq] at h
    rw [hx, h]
  · simp at h

theorem renameVal_inj (f : Nat → Nat) {a b : Val}
    (hf : ∀ x y, a = .ref x → b = .ref y → f x = f y → x = y)
    (h : renameVal f a = renameVal f b) : a = b := by
  cases a <;> cases b <;> simp_all [renameVal]

theorem mem_refs_object {p : Proto} {nf : List (String × Slot)} {ext : Bool} {d : Nat} :
    d ∈ (Obj.object p nf ext).refs ↔ ∃ q ∈ nf, q.2.value = .ref d := by
  simp only [Obj.refs, List.mem_filterMap]
  constructor
  · rintro ⟨q, hq, h⟩
    refine ⟨q, hq, ?_⟩
    split at h
    · cases h; assumption
    · simp at h
  · rintro ⟨q, hq, h⟩
    exact ⟨q, hq, by simp [h]⟩

theorem mem_refs_array {ne : List (Option Val)} {ext : Ext} {d : Nat} :
    d ∈ (Obj.array ne ext).refs ↔ some (.ref d) ∈ ne := by
  simp only [Obj.refs, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, h⟩
    split at h
    · cases h; assumption
    · simp at h
  · intro h
    exact ⟨_, h, rfl⟩

theorem mem_refs_map {ne : List (Val × Val)} {d : Nat} :
    d ∈ (Obj.map ne).refs ↔ ∃ e ∈ ne, e.1 = .ref d ∨ e.2 = .ref d := by
  simp only [Obj.refs, List.mem_flatMap]
  constructor
  · rintro ⟨⟨k, v⟩, he, h⟩
    refine ⟨(k, v), he, ?_⟩
    rcases List.mem_append.1 h with h | h
    · left
      cases k <;> simp_all
    · right
      cases v <;> simp_all
  · rintro ⟨⟨k, v⟩, he, h | h⟩ <;> refine ⟨(k, v), he, ?_⟩ <;> simp_all

theorem mem_refs_set {nm : List Val} {d : Nat} :
    d ∈ (Obj.set nm).refs ↔ .ref d ∈ nm := by
  simp only [Obj.refs, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, h⟩
    split at h
    · cases h; assumption
    · simp at h
  · intro h
    exact ⟨_, h, rfl⟩

/-- A node renamed by `f`, whose references `identity` resolves as `f` renames them, holds the
node's contents under `identity`, given distinct keys and a renaming that keeps distinct references
apart. -/
theorem holds_renameObj (identity : Nat → Option Nat) (f : Nat → Nat) (n : Obj)
    (hid : ∀ d ∈ n.refs, identity d = some (f d))
    (hinj : ∀ a ∈ n.refs, ∀ b ∈ n.refs, f a = f b → a = b)
    (hkeys : distinctKeys (renameObj f n) n) :
    holds identity (renameObj f n) n := by
  cases n with
  | object p nf ext =>
    simp only [renameObj, holds]
    refine ⟨by simp [List.map_map, Function.comp_def], fun q hq cs hcs => ?_⟩
    rw [lookup_map_snd, lookup_of_mem_nodup hkeys.2 hq] at hcs
    cases hcs
    rw [renameSlot_value]
    exact differs_renameVal identity f _ fun d hd =>
      hid d (mem_refs_object.2 ⟨q, hq, hd⟩)
  | array ne ext =>
    simp only [renameObj, holds, List.length_map, true_and]
    intro i
    rw [List.getElem?_map]
    cases hi : ne[i]? with
    | none => simp [slotHolds]
    | some e =>
      cases e with
      | none => simp [slotHolds]
      | some v =>
        simp only [Option.map_some, Option.bind_some, id, slotHolds, Bool.not_eq_true']
        exact differs_renameVal identity f v fun d hd =>
          hid d (mem_refs_array.2 (hd ▸ List.mem_of_getElem? hi))
  | map ne =>
    simp only [renameObj, holds, collectionHolds]
    have hkey : ∀ k ∈ ne.map Prod.fst, resolveKey identity k = some (renameVal f k) := by
      intro k hk
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hk
      exact resolveKey_renameVal identity f _ fun d hd =>
        hid d (mem_refs_map.2 ⟨e, he, Or.inl hd⟩)
    refine ⟨?_, fun k hk ck cv nv hck hcv hnv => ?_⟩
    · simp only [List.map_map]
      rw [List.map_inj_left]
      intro e he
      simpa using hkey e.1 (List.mem_map.2 ⟨e, he, rfl⟩)
    · rw [hkey k hk] at hck
      cases hck
      rw [lookup_map_inj _ _ _ _ (fun a ha e => ?_), hnv] at hcv
      · cases hcv
        exact differs_renameVal identity f nv fun d hd =>
          hid d (mem_refs_map.2 ⟨(k, nv), mem_of_lookup hnv, Or.inr hd⟩)
      · obtain ⟨⟨a', b'⟩, ha', rfl⟩ := List.mem_map.1 ha
        obtain ⟨⟨k', v'⟩, hk', rfl⟩ := List.mem_map.1 hk
        exact renameVal_inj f (fun x y hx hy hxy =>
          hinj x (mem_refs_map.2 ⟨_, ha', Or.inl hx⟩) y (mem_refs_map.2 ⟨_, hk', Or.inl hy⟩)
            hxy) e
  | set nm =>
    simp only [renameObj, holds, collectionHolds]
    refine ⟨?_, fun k _ ck cv nv _ hcv _ => by simp at hcv⟩
    rw [List.map_map, List.map_inj_left]
    intro k hk
    exact resolveKey_renameVal identity f _ fun d hd => hid d (mem_refs_set.2 (hd ▸ hk))
  | date ms => simp [renameObj, holds]
  | buffer b m => simp [renameObj, holds]
  | view c b o l => simp [renameObj, holds]

/-- Conversely, a renamed node that holds the node's contents resolves every reference as the
renaming does, unless the node is a view, whose buffer `holds` leaves to its fixed slot. -/
theorem identity_of_holds_renameObj (identity : Nat → Option Nat) (f : Nat → Nat) (n : Obj)
    (h : holds identity (renameObj f n) n)
    (hinj : ∀ a ∈ n.refs, ∀ b ∈ n.refs, f a = f b → a = b)
    (hkeys : distinctKeys (renameObj f n) n)
    (hview : ∀ c b o l, n ≠ .view c b o l) :
    ∀ d ∈ n.refs, identity d = some (f d) := by
  intro d hd
  cases n with
  | object p nf ext =>
    simp only [renameObj, holds] at h
    obtain ⟨q, hq, hv⟩ := mem_refs_object.1 hd
    have := h.2 q hq (renameSlot f q.2) (by rw [lookup_map_snd, lookup_of_mem_nodup hkeys.2 hq]; rfl)
    rw [renameSlot_value, hv] at this
    exact identity_of_differs this
  | array ne ext =>
    simp only [renameObj, holds] at h
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 (mem_refs_array.1 hd)
    have := h.2 i
    rw [List.getElem?_map, hi] at this
    simp only [Option.map_some, Option.bind_some, id, slotHolds, Bool.not_eq_true'] at this
    exact identity_of_differs this
  | map ne =>
    simp only [renameObj, holds, collectionHolds] at h
    have hkey : ∀ k ∈ ne.map Prod.fst, resolveKey identity k = some (renameVal f k) := by
      have := h.1
      simp only [List.map_map] at this
      rw [List.map_inj_left] at this
      intro k hk
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hk
      simpa using this e he
    obtain ⟨⟨k, v⟩, he, hk | hv⟩ := mem_refs_map.1 hd
    · have := hkey k (List.mem_map.2 ⟨_, he, rfl⟩)
      simp only at hk
      subst hk
      simpa [resolveKey, renameVal] using this
    · simp only at hv
      subst hv
      have hkm : k ∈ ne.map Prod.fst := List.mem_map.2 ⟨_, he, rfl⟩
      have hl : ne.lookup k = some (.ref d) := lookup_of_mem_nodup hkeys.2 he
      have := h.2 k hkm (renameVal f k) (renameVal f (.ref d)) (.ref d) (hkey k hkm)
        (by
          rw [lookup_map_inj _ _ _ _ (fun a ha e => ?_), hl]
          · rfl
          · obtain ⟨⟨a', b'⟩, ha', rfl⟩ := List.mem_map.1 ha
            exact renameVal_inj f (fun x y hx hy hxy =>
              hinj x (mem_refs_map.2 ⟨_, ha', Or.inl hx⟩) y (mem_refs_map.2 ⟨_, he, Or.inl hy⟩)
                hxy) e) hl
      exact identity_of_differs this
  | set nm =>
    simp only [renameObj, holds, collectionHolds] at h
    have := h.1
    rw [List.map_map, List.map_inj_left] at this
    simpa [resolveKey, renameVal] using this _ (mem_refs_set.1 hd)
  | date ms => simp [Obj.refs] at hd
  | buffer b m => simp [Obj.refs] at hd
  | view c b o l => exact absurd rfl (hview c b o l)

/-- A kept object that already holds a node's contents takes no write and blocks nothing, for
every kind; unlike `writesOf_nil_iff`, this direction needs no premise. -/
theorem writesOf_of_holds (identity : Nat → Option Nat) (c n : Obj) (h : holds identity c n) :
    writesOf identity c n = ([], false) := by
  cases c <;> cases n <;> simp only [holds] at h
  case object.object p cf ext p' nf ext' =>
    obtain ⟨hkeys, hv⟩ := h
    have hr : retainPrefix (cf.map Prod.fst) (nf.map Prod.fst) = nf.map Prod.fst := by
      rw [hkeys, retainPrefix_self]
    simp only [writesOf, objectWrites, Prod.mk.injEq, List.append_eq_nil_iff,
      List.filterMap_eq_nil_iff, List.any_eq_false]
    refine ⟨⟨fun ⟨k, cs⟩ hp => ?_, fun ⟨k, ns⟩ hp => ?_⟩, fun ⟨k, ns⟩ hp => ?_⟩
    · have hk : k ∈ nf.map Prod.fst := hkeys ▸ List.mem_map.mpr ⟨_, hp, rfl⟩
      simp only [hr, List.contains_iff_mem, hk, Bool.and_self, if_true]
    · have hk : k ∈ cf.map Prod.fst := hkeys ▸ List.mem_map.mpr ⟨_, hp, rfl⟩
      obtain ⟨cs, hcs⟩ := exists_lookup_of_mem hk
      have hk' : k ∈ nf.map Prod.fst := List.mem_map.mpr ⟨_, hp, rfl⟩
      simp only [hcs, hr, List.contains_iff_mem, hk', if_true]
      rw [if_neg (by simpa using hv (k, ns) hp cs hcs)]
    · simp only
      split
      · rename_i v e c' hcs
        simp [show differs identity v ns.value = false from hv (k, ns) hp _ hcs]
      · rename_i cs _ hcs
        simp [show differs identity cs.value ns.value = false from hv (k, ns) hp _ hcs]
      · simp
  case array.array ce ext ne ext' =>
    have := (arraySlotWrites_nil_iff identity ce ne).2 h
    simp [writesOf, arrayWrites, this]
  case map.map ce ne =>
    obtain ⟨hkeys, hv⟩ := h
    have hr : retainPrefix ((ce.map Prod.fst).map some)
        ((ne.map Prod.fst).map (resolveKey identity)) =
        (ne.map Prod.fst).map (resolveKey identity) := by
      rw [hkeys, retainPrefix_self]
    simp only [writesOf, collectionWrites, entryWrites, Prod.mk.injEq, List.map_eq_nil_iff,
      List.append_eq_nil_iff, List.filterMap_eq_nil_iff, and_true]
    refine ⟨fun ck hck => ?_, fun k hk => ?_⟩
    · have hm : some ck ∈ (ne.map Prod.fst).map (resolveKey identity) :=
        hkeys ▸ List.mem_map.mpr ⟨ck, hck, rfl⟩
      simp only [hr, List.contains_iff_mem, hm, Bool.and_self, if_true]
    · have hmem : resolveKey identity k ∈ (ce.map Prod.fst).map some :=
        hkeys ▸ List.mem_map.mpr ⟨k, hk, rfl⟩
      obtain ⟨ck, _, hres⟩ := List.mem_map.mp hmem
      have hm : some ck ∈ (ne.map Prod.fst).map (resolveKey identity) :=
        List.mem_map.mpr ⟨k, hk, hres.symm⟩
      simp only [← hres, hr, List.contains_iff_mem, hm, if_true]
      split
      · rename_i cv nv hcv hnv
        rw [if_neg (by simpa using hv k hk ck cv nv hres.symm hcv hnv)]
      · rfl
  case set.set cm nm =>
    obtain ⟨hkeys, -⟩ := h
    have hr : retainPrefix (cm.map some) (nm.map (resolveKey identity)) =
        nm.map (resolveKey identity) := by
      rw [hkeys, retainPrefix_self]
    simp only [writesOf, collectionWrites, entryWrites, Prod.mk.injEq, List.map_eq_nil_iff,
      List.append_eq_nil_iff, List.filterMap_eq_nil_iff, and_true]
    refine ⟨fun ck hck => ?_, fun k hk => ?_⟩
    · have hm : some ck ∈ nm.map (resolveKey identity) := hkeys ▸ List.mem_map.mpr ⟨ck, hck, rfl⟩
      simp only [hr, List.contains_iff_mem, hm, Bool.and_self, if_true]
    · have hmem : resolveKey identity k ∈ cm.map some := hkeys ▸ List.mem_map.mpr ⟨k, hk, rfl⟩
      obtain ⟨ck, _, hres⟩ := List.mem_map.mp hmem
      have hm : some ck ∈ nm.map (resolveKey identity) := List.mem_map.mpr ⟨k, hk, hres.symm⟩
      simp only [← hres, hr, List.contains_iff_mem, hm, if_true]
  case date.date => simp [writesOf, h]
  case buffer.buffer => simp [writesOf, h]
  case view.view => rfl

/-! ## Untouched nodes already hold their contents -/

/-- An object that `next` holds at node `j` already holds the node's contents under a decision
that keeps every node `j` refers to untouched: the arguments read it alike, and each of its
references resolves to the object it already holds there. -/
theorem untouched_holds (input : Input) (kept : Array (Option Nat)) (hco : Coherent input)
    (j c : Nat) (hc : input.same[j]?.bind id = some c)
    (hd : ∀ d ∈ (input.next.node j).refs, untouched input kept d = true) :
    holds (identityOf kept) (input.cur.node c) (input.next.node j) := by
  rw [hco.node j c hc]
  refine holds_renameObj _ _ _ (fun d hdm => ?_) (fun a ha b hb hab => ?_) ?_
  · obtain ⟨c', hc', hk⟩ := (untouched_iff input kept d).1 (hd d hdm)
    simp [identityOf, hk, sameOf, hc']
  · obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.1 (hco.shared j c hc a ha)
    obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 (hco.shared j c hc b hb)
    simp only [sameOf, ha', hb', Option.getD_some] at hab
    subst hab
    exact hco.inj a b a' ha' hb'
  · rw [← hco.node j c hc]
    exact hco.keys j c hc

/-- **Untouched nodes need no publication and no readback.** Under a decision whose rule's second
clause holds at an untouched node, the node's object takes no write and blocks nothing: publishing
it changes nothing, and reading it back would accept it. -/
theorem untouched_writesOf (input : Input) (kept : Array (Option Nat)) (hco : Coherent input)
    (j c : Nat) (hc : input.same[j]?.bind id = some c)
    (hd : ∀ d ∈ (input.next.node j).refs, untouched input kept d = true) :
    writesOf (identityOf kept) (input.cur.node c) (input.next.node j) = ([], false) :=
  writesOf_of_holds _ _ _ (untouched_holds input kept hco j c hc hd)

/-! ## Publishing untouched nodes too

`publishedWrites` is the publication of every unpinned kept node, untouched ones included, as the
runtime publishes before the rule: the writes `writesOfDecision` makes when untouched nodes are
not skipped. -/

/-- The writes of a decision when every kept node that is not pinned is published. -/
def publishedWrites (input : Input) (pin : Array Bool) (kept : Array (Option Nat)) :
    List (Nat × String × String) :=
  (List.range input.next.nodes.size).flatMap fun j =>
    match kept[j]?.bind id with
    | some i =>
      if pin[j]?.getD false then []
      else (writesOf (identityOf kept) (input.cur.node i) (input.next.node j)).1.map
        fun (k, w) => (i, k, w)
    | none => []

/-- Skipping untouched nodes changes no write of a decision that keeps `next` unchanged: each
untouched node already holds its contents (`untouched_writesOf`). -/
theorem writesOfDecision_eq_publishedWrites (input : Input) (pin : Array Bool)
    (kept : Array (Option Nat)) (hco : Coherent input) (hk : keepsNext input kept = true) :
    writesOfDecision input pin kept = publishedWrites input pin kept := by
  unfold writesOfDecision publishedWrites
  refine List.flatMap_congr fun j hj => ?_
  cases hi : kept[j]?.bind id with
  | none => rfl
  | some i =>
    simp only
    by_cases hp : pin[j]?.getD false = true
    · simp [skipped, hp]
    · by_cases hu : untouched input kept j = true
      · obtain ⟨c, hc, hkc⟩ := (untouched_iff input kept j).1 hu
        rw [hi] at hkc
        cases hkc
        have hd := (keepsNext_iff input kept).1 hk |>.2 j (List.mem_range.1 hj) hu
        simp [skipped, hp, hu, untouched_writesOf input kept hco j i hc hd]
      · simp [skipped, hp, hu]

/-- **Safety of the full publication.** Even publishing every unpinned node, untouched ones
included, a decision that keeps `next` unchanged writes into no object `next` holds. -/
theorem publishedWrites_not_next (input : Input) (pin : Array Bool) (kept : Array (Option Nat))
    (hco : Coherent input) (hk : keepsNext input kept = true) :
    ∀ e ∈ publishedWrites input pin kept, nextHolds input e.1 = false := by
  rw [← writesOfDecision_eq_publishedWrites input pin kept hco hk]
  exact writesOfDecision_keepsNext input pin kept hk

/-- **The second clause is exact.** An untouched node with a reference that is not untouched
takes a write into `next`'s own object when it is published, unless it is a view, whose buffer the
decision keeps as a fixed slot: its object passed the static checks and the decision keeps each
object at one node. -/
theorem publishedWrites_child (input : Input) (kept : Array (Option Nat)) (hco : Coherent input)
    (j c : Nat) (hc : input.same[j]?.bind id = some c)
    (hadm : admitsStatic input.classes (input.cur.node c) (input.next.node j) = true)
    (hinj : ∀ a b x, identityOf kept a = some x → identityOf kept b = some x → a = b)
    (hview : ∀ ctor b o l, input.next.node j ≠ .view ctor b o l)
    (d : Nat) (hd : d ∈ (input.next.node j).refs) (hnu : untouched input kept d = false) :
    (writesOf (identityOf kept) (input.cur.node c) (input.next.node j)).1 ≠ [] := by
  intro hnil
  have hh := (writesOf_nil_iff input.classes _ _ _ hadm (hco.keys j c hc) hinj).1 hnil
  rw [hco.node j c hc] at hh
  have hkeys := hco.keys j c hc
  rw [hco.node j c hc] at hkeys
  have hid := identity_of_holds_renameObj _ _ _ hh (fun a ha b hb hab => ?_) hkeys hview d hd
  · obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.1 (hco.shared j c hc d hd)
    have : untouched input kept d = true := by
      rw [untouched_iff]
      refine ⟨d', hd', ?_⟩
      simpa [identityOf, sameOf, hd'] using hid
    rw [this] at hnu
    cases hnu
  · obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.1 (hco.shared j c hc a ha)
    obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 (hco.shared j c hc b hb)
    simp only [sameOf, ha', hb', Option.getD_some] at hab
    subst hab
    exact hco.inj a b a' ha' hb'

/-! ## Pinned nodes are untouched

The pinned nodes are the subtrees `reach` finds below the nodes pinned at their position. `reach`
walks with a budget; each step consumes one pending entry and adds the references of a node it has
not entered (`reachPot`), so the budget never runs out and the walk is closed under references
(`reach_closed`). -/

/-- The work left to `reach`'s walk: its pending entries and the references of the nodes it has not
entered. -/
def reachPot (g : Graph) (stack seen : List Nat) : Nat :=
  stack.length + ((List.range g.nodes.size).map fun x =>
    if seen.contains x then 0 else (g.node x).refs.length).sum

theorem node_refs_out (g : Graph) (x : Nat) (hx : g.nodes.size ≤ x) : (g.node x).refs = [] := by
  have hd : g.node x = .object .object [] false := by
    simp only [Graph.node, Array.getElem?_eq_none hx, Option.getD_none]
    rfl
  rw [hd]
  rfl

theorem sum_map_point (h h' : Nat → Nat) (a : Nat) (hpt : ∀ x, x ≠ a → h' x = h x)
    (h0 : h' a = 0) :
    ∀ L : List Nat, L.Nodup → (L.map h').sum + (if a ∈ L then h a else 0) = (L.map h).sum
  | [], _ => by simp
  | x :: L, hn => by
    rw [List.nodup_cons] at hn
    have ih := sum_map_point h h' a hpt h0 L hn.2
    by_cases hx : x = a
    · subst hx
      rw [if_neg hn.1] at ih
      simp only [List.map_cons, List.sum_cons, h0, List.mem_cons, true_or, if_true]
      omega
    · simp only [List.map_cons, List.sum_cons, hpt x hx, List.mem_cons, Ne.symm hx, false_or]
      omega

/-- Entering a node consumes one unit of work. -/
theorem reachPot_step (g : Graph) (id : Nat) (rest seen : List Nat) (hs : id ∉ seen) :
    reachPot g ((g.node id).refs ++ rest) (id :: seen) + 1 = reachPot g (id :: rest) seen := by
  unfold reachPot
  have := sum_map_point (fun x => if seen.contains x then 0 else (g.node x).refs.length)
    (fun x => if (id :: seen).contains x then 0 else (g.node x).refs.length) id
    (fun x hx => by simp [hx]) (by simp) (List.range g.nodes.size) List.nodup_range
  have hc : seen.contains id = false := by simpa using hs
  simp only [List.length_append, List.length_cons]
  by_cases hid : id < g.nodes.size
  · simp only [List.mem_range, hid, if_true, hc, Bool.false_eq_true, if_false] at this
    omega
  · simp only [List.mem_range, hid, if_false] at this
    rw [node_refs_out g id (by omega)]
    simp only [List.length_nil]
    omega

theorem reach_go_closed (g : Graph) :
    ∀ (fuel : Nat) (stack seen : List Nat), reachPot g stack seen ≤ fuel →
      (∀ x ∈ seen, ∀ d ∈ (g.node x).refs, d ∈ seen ∨ d ∈ stack) →
      ∀ x ∈ reach.go g fuel stack seen, ∀ d ∈ (g.node x).refs, d ∈ reach.go g fuel stack seen
  | 0, stack, seen, hp, hi => by
    have : stack = [] := List.eq_nil_of_length_eq_zero (by unfold reachPot at hp; omega)
    subst this
    simp only [reach.go]
    intro x hx d hd
    simpa using hi x hx d hd
  | fuel + 1, [], seen, _, hi => by
    simp only [reach.go]
    intro x hx d hd
    simpa using hi x hx d hd
  | fuel + 1, id :: rest, seen, hp, hi => by
    simp only [reach.go]
    split
    · rename_i hs
      apply reach_go_closed g fuel rest seen
      · unfold reachPot at hp ⊢
        simp only [List.length_cons] at hp
        omega
      · intro x hx d hd
        rcases hi x hx d hd with h | h
        · exact Or.inl h
        · rcases List.mem_cons.1 h with rfl | h
          · exact Or.inl (by simpa using hs)
          · exact Or.inr h
    · rename_i hs
      apply reach_go_closed g fuel _ _
      · have := reachPot_step g id rest seen (by simpa using hs)
        omega
      · intro x hx d hd
        rcases List.mem_cons.1 hx with rfl | hx
        · exact Or.inr (List.mem_append_left _ hd)
        · rcases hi x hx d hd with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · rcases List.mem_cons.1 h with rfl | h
            · exact Or.inl List.mem_cons_self
            · exact Or.inr (List.mem_append_right _ h)

theorem reach_go_pred (g : Graph) (P : Nat → Prop) (hP : ∀ x, P x → ∀ d ∈ (g.node x).refs, P d) :
    ∀ (fuel : Nat) (stack seen : List Nat), (∀ x ∈ stack, P x) → (∀ x ∈ seen, P x) →
      ∀ x ∈ reach.go g fuel stack seen, P x
  | 0, _, seen, _, hs => by simpa [reach.go] using hs
  | fuel + 1, [], seen, _, hs => by simpa [reach.go] using hs
  | fuel + 1, id :: rest, seen, ht, hs => by
    simp only [reach.go]
    split
    · exact reach_go_pred g P hP fuel rest seen (fun x hx => ht x (List.mem_cons_of_mem _ hx)) hs
    · refine reach_go_pred g P hP fuel _ _ (fun x hx => ?_) (fun x hx => ?_)
      · rcases List.mem_append.1 hx with hx | hx
        · exact hP id (ht id List.mem_cons_self) x hx
        · exact ht x (List.mem_cons_of_mem _ hx)
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact ht x List.mem_cons_self
        · exact hs x hx

theorem range_map_refs (g : Graph) :
    ((List.range g.nodes.size).map fun x => (g.node x).refs.length) =
      g.nodes.toList.map (·.refs.length) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    simp only [List.length_map, List.length_range] at h1
    simp [Graph.node, h1]

/-- `reach` is closed under references: its budget covers every step of the walk. -/
theorem reach_closed (g : Graph) (s x d : Nat) (hx : x ∈ reach g s) (hd : d ∈ (g.node x).refs) :
    d ∈ reach g s := by
  unfold reach at hx ⊢
  refine reach_go_closed g _ [s] [] ?_ (by simp) x hx d hd
  unfold reachPot Graph.budget
  simp only [List.length_singleton, List.contains_nil, Bool.false_eq_true, if_false]
  rw [range_map_refs]
  omega

/-- Every node `reach` finds satisfies a property of its start that references carry. -/
theorem reach_pred (g : Graph) (P : Nat → Prop) (hP : ∀ x, P x → ∀ d ∈ (g.node x).refs, P d)
    (s : Nat) (hs : P s) : ∀ x ∈ reach g s, P x :=
  reach_go_pred g P hP _ [s] [] (by simpa using hs) (by simp)

theorem pinnedAt_same {input : Input} {first : Array (Option Nat)} {r : Nat}
    (h : pinnedAt input first r = true) : (input.same[r]?.bind id).isSome = true := by
  unfold pinnedAt at h
  split at h
  · rename_i i _ hi _
    simp [hi]
  · simp at h

theorem same_lt {input : Input} (hco : Coherent input) {d : Nat}
    (h : (input.same[d]?.bind id).isSome = true) : d < input.next.nodes.size := by
  have : d < input.same.size := by
    by_contra hd
    simp [Array.getElem?_eq_none (Nat.le_of_not_lt hd)] at h
  exact Nat.lt_of_lt_of_le this hco.size

/-- **Pinned subtrees are closed.** A pinned node is a current object, and every node it refers to
is pinned. -/
theorem pinned_closed (input : Input) (hco : Coherent input) (order : List Nat)
    (first : Array (Option Nat)) (j : Nat)
    (hpin : (pinned input order first)[j]?.getD false = true) :
    (input.same[j]?.bind id).isSome = true ∧
      ∀ d ∈ (input.next.node j).refs, (pinned input order first)[d]?.getD false = true := by
  simp only [pinned, Array.getElem?_map, Array.getElem?_range] at hpin ⊢
  split at hpin
  · rename_i hj
    simp only [Option.map_some, Option.getD_some, Bool.or_eq_true, List.contains_iff_mem] at hpin
    -- Either case puts `j` inside a pinned subtree.
    have hin : j ∈ (order.filter (pinnedAt input first)).flatMap (reach input.next) := by
      rcases hpin with h | h
      · exact h
      · split at h
        · rename_i i hi
          simp only [List.contains_iff_mem, List.mem_filterMap] at h
          obtain ⟨j', hj', hs'⟩ := h
          rw [hco.inj j j' i hi hs'] 
          exact hj'
        · simp at h
    obtain ⟨r, hr, hjr⟩ := List.mem_flatMap.1 hin
    have hshared : ∀ x ∈ reach input.next r, (input.same[x]?.bind id).isSome = true :=
      reach_pred input.next _ (fun x hx d hd => by
        obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hx
        exact hco.shared x c hc d hd) r (pinnedAt_same (List.mem_filter.1 hr).2)
    refine ⟨hshared j hjr, fun d hd => ?_⟩
    have hdr := reach_closed input.next r j d hjr hd
    have hdn := same_lt hco (hshared d hdr)
    simp only [hdn, if_true, Option.map_some, Option.getD_some, Bool.or_eq_true,
      List.contains_iff_mem]
    exact Or.inl (List.mem_flatMap.2 ⟨r, hr, hdr⟩)
  · simp at hpin

/-- Discovery's pinned nodes are closed (`pinned_closed`). -/
theorem discover_pinned_closed (input : Input) (hco : Coherent input) (j : Nat)
    (hpin : (discover input).pinned[j]?.getD false = true) :
    (input.same[j]?.bind id).isSome = true ∧
      ∀ d ∈ (input.next.node j).refs, (discover input).pinned[d]?.getD false = true := by
  cases hr : input.next.root with
  | prim p =>
    simp only [discover, hr, Array.getElem?_replicate] at hpin
    split at hpin <;> simp at hpin
  | ref r =>
    simp only [discover, hr] at hpin ⊢
    generalize visitStep input.cur input.next input.next.budget [(r, input.cur.root.refId)]
      (Array.replicate input.next.nodes.size false)
      (Array.replicate input.next.nodes.size none) [] = vs at hpin ⊢
    obtain ⟨order, first⟩ := vs
    exact pinned_closed input hco order first j hpin

/-- In every decision a pinned node keeps the object it is. -/
theorem decide_pinned (input : Input) (al : Discovery) (pin : Array Bool) (forbidden : List Nat)
    (written : List Requirement) (j : Nat) (hj : j < input.next.nodes.size)
    (hpin : pin[j]?.getD false = true) :
    (decide input al pin forbidden written)[j]?.bind id = input.same[j]?.bind id := by
  unfold decide
  refine (List.foldlRecOn (motive := fun d : Decision =>
      d.decided[j]?.getD false = true ∧ d.kept[j]?.bind id = input.same[j]?.bind id)
    al.order _ ?_ ?_).2
  · refine ⟨hpin, ?_⟩
    simp [hj, pinnedObject, hpin]
  · intro d hd j' _
    dsimp only
    split
    · exact hd
    · rename_i hnd
      have hne : j' ≠ j := fun h => by subst h; simp [hd.1] at hnd
      have hdec : (d.decided.setIfInBounds j' true)[j]?.getD false = true := by
        rw [Array.getElem?_setIfInBounds_ne hne]
        exact hd.1
      split
      · exact ⟨hdec, by rw [Array.getElem?_setIfInBounds_ne hne]; exact hd.2⟩
      · split
        · exact ⟨hdec, hd.2⟩
        · rename_i pairs _
          refine List.foldlRecOn (motive := fun d' : Decision =>
              d'.decided[j]?.getD false = true ∧
                d'.kept[j]?.bind id = input.same[j]?.bind id) pairs _ ⟨hdec, hd.2⟩ ?_
          intro d' hd' ⟨c, x⟩ _
          dsimp only
          split
          · exact ⟨hd'.1, by rw [Array.getElem?_setIfInBounds_ne hne]; exact hd'.2⟩
          · exact hd'

/-- **Pinned nodes pass the rule.** In every decision of the passes, a pinned node is untouched, and
so is every node it refers to. -/
theorem keepsNextAt_pinned (input : Input) (hco : Coherent input) (r fuel : Nat)
    (forbidden : List Nat) (written : List Requirement) (kept : Array (Option Nat))
    (hk : kept ∈ demote input (discover input) (discover input).pinned r fuel forbidden written)
    (j : Nat) (hpin : (discover input).pinned[j]?.getD false = true) :
    untouched input kept j = true ∧ keepsNextAt input kept j = true := by
  obtain ⟨forbidden', written', rfl⟩ := mem_demote input _ _ r fuel forbidden written kept hk
  have hu : ∀ a, (discover input).pinned[a]?.getD false = true →
      untouched input (decide input (discover input) (discover input).pinned forbidden' written')
        a = true := by
    intro a ha
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (discover_pinned_closed input hco a ha).1
    rw [untouched_iff]
    refine ⟨c, hc, ?_⟩
    rw [decide_pinned input _ _ _ _ a (same_lt hco (by simp [hc])) ha, hc]
  refine ⟨hu j hpin, (keepsNextAt_iff _ _ _).2 ⟨fun _ _ _ => hu j hpin, fun _ d hd => ?_⟩⟩
  exact hu d ((discover_pinned_closed input hco j hpin).2 d hd)

/-- **Objects in place are never rejected.** When every next node that is a current object is
pinned, in place at its position, every decision of the passes keeps `next` unchanged. Capture
records only the nodes `next`'s root reaches, so for it the premise reads: every current object
`next` holds is in place. -/
theorem rounds_keepsNext_inPlace (input : Input) (hco : Coherent input) (r : Nat)
    (hall : ∀ j, j < input.next.nodes.size → (input.same[j]?.bind id).isSome = true →
      (discover input).pinned[j]?.getD false = true) :
    ∀ kept ∈ rounds input (discover input) r, keepsNext input kept = true := by
  intro kept hk
  refine (keepsNext_iff input kept).2 ⟨fun j hj x hx hn => ?_, fun j hj hu => ?_⟩
  · obtain ⟨_, j', _, _, hs'⟩ := (nextHolds_iff input x).1 hn
    have hj' := same_lt hco (d := j') (by simp [hs'])
    have hp' := hall j' hj' (by simp [hs'])
    have := demote_pinned input (discover input) (discover input).pinned r
      (fun a b x _ _ _ _ ha hb => hco.inj a b x ha hb) _ kept hk j j' x hj' hp' hs' hx
    subst this
    rw [untouched_iff]
    exact ⟨x, hs', hx⟩
  · obtain ⟨c, hc, _⟩ := (untouched_iff input kept j).1 hu
    have hp := hall j hj (by simp [hc])
    exact ((keepsNextAt_iff _ _ _).1 (keepsNextAt_pinned input hco r _ [] [] kept hk j hp).2).2 hu

/-! ## Placement: every pass that writes passed the check -/

theorem demote_ne_nil (input : Input) (al : Discovery) (pin : Array Bool) (r : Nat) :
    ∀ fuel forbidden written, demote input al pin r fuel forbidden written ≠ []
  | 0, _, _ => by simp [demote]
  | _ + 1, _, _ => by
    simp only [demote]
    split <;> simp

/-- Every decision the passes go past keeps the root and keeps `next` unchanged: the passes stop at
the first decision that does not. -/
theorem demote_dropLast (input : Input) (al : Discovery) (pin : Array Bool) (r : Nat) :
    ∀ fuel forbidden written, ∀ kept ∈ (demote input al pin r fuel forbidden written).dropLast,
      (kept[r]?.bind id).isSome = true ∧ keepsNext input kept = true
  | 0, _, _ => by simp [demote]
  | fuel + 1, forbidden, written => by
    simp only [demote]
    split
    · simp
    · rename_i h
      simp only [Bool.or_eq_true, not_or, Option.isNone_iff_eq_none, Bool.not_eq_true',
        Bool.not_eq_false] at h
      rw [List.dropLast_cons_of_ne_nil (demote_ne_nil input al pin r fuel _ _)]
      intro kept hk
      rcases List.mem_cons.1 hk with rfl | hk
      · exact ⟨by simpa [Option.isSome_iff_ne_none] using h.1.1, h.1.2⟩
      · exact demote_dropLast input al pin r fuel _ _ kept hk

/-- **No write into `next` before a rejection.** The passes before a call's last decision write
into no object `next` holds. -/
theorem rounds_dropLast_writes_not_next (input : Input) (al : Discovery) (r : Nat) :
    ∀ kept ∈ (rounds input al r).dropLast, ∀ e ∈ writesOfDecision input al.pinned kept,
      nextHolds input e.1 = false := fun kept hk =>
  writesOfDecision_keepsNext input al.pinned kept
    (demote_dropLast input al al.pinned r _ _ _ kept hk).2

theorem mem_dropLast_or_last {α : Type} (l : List α) (d x : α) (hx : x ∈ l) :
    x ∈ l.dropLast ∨ x = l.getLastD d := by
  have hne : l ≠ [] := List.ne_nil_of_mem hx
  rw [← List.dropLast_append_getLast hne] at hx
  rcases List.mem_append.1 hx with h | h
  · exact Or.inl h
  · right
    rw [List.mem_singleton.1 h, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
    rfl

/-- **Safety of a call.** A call that succeeds wrote into no object `next` holds in any pass: every
pass before the last passed the check, and so did the last, or the call would have been rejected. -/
theorem run_allWrites_not_next (raw : Input) (hok : (run raw).ok = true) :
    ∀ e ∈ (run raw).allWrites, nextHolds (normalized raw) e.1 = false := by
  simp only [run] at hok ⊢
  split at hok
  · rename_i _ r _ _
    split at hok
    · simp at hok
    · split at hok
      · simp at hok
      · rename_i hroot hkeeps
        simp only [Bool.not_eq_true', Bool.not_eq_false] at hkeeps
        rw [if_neg hroot, if_neg (by simpa using hkeeps)]
        intro e he
        simp only [publish] at he
        obtain ⟨l, hl, he⟩ := List.mem_flatten.1 ((eraseDups_spec _).1 _ he)
        obtain ⟨kept, hk, rfl⟩ := List.mem_map.1 hl
        rcases mem_dropLast_or_last _ #[] kept hk with hk | rfl
        · exact rounds_dropLast_writes_not_next _ _ r kept hk e he
        · exact writesOfDecision_keepsNext _ _ _ (by simpa using hkeeps) e he
  · simp

theorem isSome_of_not_isNone {α : Type} {o : Option α} (h : ¬o.isNone = true) :
    o.isSome = true := by
  cases o <;> simp_all

/-- A call rejected because it would change `next` keeps the root in its last decision, which fails
the rule, after passes that each passed it (`rounds_dropLast_writes_not_next`); it reports no pass,
a rejection before any write, exactly when that decision is its first. -/
theorem run_changesNext (raw : Input) (h : (run raw).changesNext = true) :
    (run raw).ok = false ∧ ∃ r,
      let passes := rounds (normalized raw) (discover (normalized raw)) r
      ((passes.getLastD #[])[r]?.bind id).isSome = true ∧
        keepsNext (normalized raw) (passes.getLastD #[]) = false ∧
        ((run raw).passes = 0 ↔ passes.length = 1) := by
  simp only [run] at h ⊢
  split at h
  · rename_i _ r _ _
    split at h
    · simp at h
    · split at h
      · rename_i hroot hkeeps
        rw [if_neg hroot, if_pos hkeeps]
        refine ⟨rfl, r, isSome_of_not_isNone hroot, by simpa using hkeeps, ?_⟩
        have := demote_ne_nil (normalized raw) (discover (normalized raw))
          (discover (normalized raw)).pinned r (normalized raw).cur.nodes.size [] []
        have hpos := List.length_pos_of_ne_nil this
        simp only [rounds]
        split <;> omega
      · simp [publish] at h
  · simp at h

/-! ## A checkable coherence

`coherent` decides `Coherent` (`coherent_spec`), so that the examples below are inputs the
theorems cover. -/

/-- Whether neither node repeats a key, as a Boolean. -/
def distinctKeysB : Obj → Obj → Bool
  | .object _ cf _, .object _ nf _ =>
    Decidable.decide (cf.map Prod.fst).Nodup && Decidable.decide (nf.map Prod.fst).Nodup
  | .map ce, .map ne =>
    Decidable.decide (ce.map Prod.fst).Nodup && Decidable.decide (ne.map Prod.fst).Nodup
  | .set cm, .set nm => Decidable.decide cm.Nodup && Decidable.decide nm.Nodup
  | _, _ => true

theorem distinctKeysB_spec (c n : Obj) (h : distinctKeysB c n = true) : distinctKeys c n := by
  cases c <;> cases n <;> simp_all [distinctKeysB, distinctKeys]

/-- `Coherent`, checked over `same`'s entries. -/
def coherent (input : Input) : Bool :=
  Decidable.decide (input.same.size ≤ input.next.nodes.size) &&
    (List.range input.same.size).all fun a =>
      match input.same[a]?.bind id with
      | none => true
      | some c =>
        (List.range input.same.size).all (fun b => b == a || input.same[b]?.bind id != some c) &&
          (input.next.node a).refs.all (fun d => (input.same[d]?.bind id).isSome) &&
          input.cur.node c == renameObj (sameOf input) (input.next.node a) &&
          distinctKeysB (input.cur.node c) (input.next.node a)

theorem same_size {input : Input} {a c : Nat} (h : input.same[a]?.bind id = some c) :
    a < input.same.size := by
  by_contra ha
  simp [Array.getElem?_eq_none (Nat.le_of_not_lt ha)] at h

theorem coherent_spec (input : Input) (h : coherent input = true) : Coherent input := by
  simp only [coherent, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨hsize, hall⟩ := h
  have hat : ∀ a c, input.same[a]?.bind id = some c →
      ((List.range input.same.size).all (fun b => b == a || input.same[b]?.bind id != some c) &&
        (input.next.node a).refs.all (fun d => (input.same[d]?.bind id).isSome) &&
        input.cur.node c == renameObj (sameOf input) (input.next.node a) &&
        distinctKeysB (input.cur.node c) (input.next.node a)) = true := by
    intro a c hc
    have := hall a (same_size hc)
    rw [hc] at this
    exact this
  refine ⟨fun a b x ha hb => ?_, hsize, fun j c hc d hd => ?_, fun j c hc => ?_,
    fun j c hc => ?_⟩
  · have := hat a x ha
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      beq_iff_eq, bne_iff_ne, ne_eq] at this
    rcases this.1.1.1 b (same_size hb) with h | h
    · exact h.symm
    · exact absurd hb h
  · have := hat j c hc
    simp only [Bool.and_eq_true, List.all_eq_true] at this
    exact this.1.1.2 d hd
  · have := hat j c hc
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.1.2
  · have := hat j c hc
    simp only [Bool.and_eq_true] at this
    exact distinctKeysB_spec _ _ this.2

/-! ## Examples and counterexamples -/

private def num (n : Int) : Val := .prim (.num n)

private def plain (fields : List (String × Val)) : Obj :=
  .object .object (fields.map fun (k, v) => (k, .data v Attrs.plain)) true

/-- A swap: `current` holds `x` at `a` and `y` at `b`, and `next` holds them the other way round. -/
private def swap : Input where
  cur := ⟨#[plain [("a", .ref 1), ("b", .ref 2)], plain [("v", num 1)], plain [("v", num 2)]],
    .ref 0⟩
  next := ⟨#[plain [("a", .ref 1), ("b", .ref 2)], plain [("v", num 2)], plain [("v", num 1)]],
    .ref 0⟩
  same := #[none, some 2, some 1]

/-- **Dropping the first clause lets `next` change.** The swap keeps `x` at `a` and `y` at `b`: no
node is untouched, so the second clause holds, but the first fails, and the pass writes into both
objects, which `next` holds. The rule rejects it before any write. -/
example :
    coherent swap = true ∧
    rounds swap (discover swap) 0 = [#[some 0, some 1, some 2]] ∧
    (List.range 3).all (fun j => !untouched swap #[some 0, some 1, some 2] j) = true ∧
    keepsNext swap #[some 0, some 1, some 2] = false ∧
    publishedWrites swap (discover swap).pinned #[some 0, some 1, some 2] =
      [(1, "v", "set"), (2, "v", "set")] ∧
    nextHolds swap 1 = true ∧ nextHolds swap 2 = true ∧
    (run swap).changesNext = true ∧ (run swap).passes = 0 := by
  decide +kernel

/-- `current` holds `q` at `p` and, as a `Map` value, `x`, which holds `c`; `next` holds `c` at `p`
and `x`, unchanged, as the `Map` value of a new `Map`. -/
private def mapChild : Input where
  cur := ⟨#[plain [("p", .ref 1), ("m", .ref 2)], plain [("v", num 1)], .map [(num 1, .ref 3)],
    plain [("c", .ref 4)], plain [("v", num 2)]], .ref 0⟩
  next := ⟨#[plain [("p", .ref 1), ("m", .ref 2)], plain [("v", num 2)], .map [(num 1, .ref 3)],
    plain [("c", .ref 1)]], .ref 0⟩
  same := #[none, some 4, none, some 3]

/-- **Dropping the second clause lets `next` change.** `x`, a `Map` value, is untouched but not
pinned, and node `c`, which `x` refers to, keeps `q`, its first candidate. Every node that keeps an
object `next` holds is untouched, so the first clause holds; the second fails at `x`. Publishing
`x` writes `q` into it, changing `next`; skipping it would leave `current` holding `c` there. -/
example :
    coherent mapChild = true ∧
    rounds mapChild (discover mapChild) 0 = [#[some 0, some 1, some 2, some 3]] ∧
    (List.range 4).all (fun j =>
      match (#[some 0, some 1, some 2, some 3] : Array (Option Nat))[j]?.bind id with
      | some x => !nextHolds mapChild x || untouched mapChild #[some 0, some 1, some 2, some 3] j
      | none => true) = true ∧
    untouched mapChild #[some 0, some 1, some 2, some 3] 3 = true ∧
    untouched mapChild #[some 0, some 1, some 2, some 3] 1 = false ∧
    keepsNext mapChild #[some 0, some 1, some 2, some 3] = false ∧
    (3, "c", "set") ∈ publishedWrites mapChild (discover mapChild).pinned
      #[some 0, some 1, some 2, some 3] ∧
    nextHolds mapChild 3 = true ∧ (run mapChild).changesNext = true := by
  decide +kernel

/-- `next` holds `current`'s `y` at `a`, where `current` holds `x`, and at `b` a new object equal to
`y`. -/
private def equalCopy : Input where
  cur := ⟨#[plain [("a", .ref 1), ("b", .ref 2)], plain [("v", num 1)], plain [("v", num 2)]],
    .ref 0⟩
  next := ⟨#[plain [("a", .ref 1), ("b", .ref 2)], plain [("v", num 2)], plain [("v", num 2)]],
    .ref 0⟩
  same := #[none, some 2, none]

/-- **The first clause is conservative.** Node `b` keeps `y`, which `next` holds at `a`, but `y`
already holds `b`'s contents, so no write reaches an object of `next`; the rule still rejects. -/
example :
    coherent equalCopy = true ∧
    rounds equalCopy (discover equalCopy) 0 = [#[some 0, some 1, some 2]] ∧
    keepsNext equalCopy #[some 0, some 1, some 2] = false ∧
    (publishedWrites equalCopy (discover equalCopy).pinned #[some 0, some 1, some 2]).all
      (fun e => !nextHolds equalCopy e.1) = true ∧
    (run equalCopy).changesNext = true := by
  decide +kernel

/-- `current` holds at `a` an object `i` whose setter drops its value, and `y` at `b`; `next` holds
one new object at `a` and `b`, and `y` at `c`, where `current` holds nothing. -/
private def laterPass : Input where
  cur := ⟨#[plain [("a", .ref 1), ("b", .ref 2)],
    .object .object [("s", .accessor (num 1) (some false) true true)] true,
    plain [("s", num 1)]], .ref 0⟩
  next := ⟨#[plain [("a", .ref 1), ("b", .ref 1), ("c", .ref 2)], plain [("s", num 2)],
    plain [("s", num 1)]], .ref 0⟩
  same := #[none, none, some 2]

/-- **A later pass can fail the rule.** The first decision keeps `i` at the new node, passes the
check and writes only into objects `next` does not hold; `i` blocks. The second keeps `y`, the
node's next candidate, which `next` holds at `c`, and would write into it: the rule rejects the
call after one pass, before any write into `next`. -/
example :
    coherent laterPass = true ∧
    rounds laterPass (discover laterPass) 0 =
      [#[some 0, some 1, none], #[some 0, some 2, none]] ∧
    keepsNext laterPass #[some 0, some 1, none] = true ∧
    (writesOfDecision laterPass (discover laterPass).pinned #[some 0, some 1, none]).all
      (fun e => !nextHolds laterPass e.1) = true ∧
    keepsNext laterPass #[some 0, some 2, none] = false ∧
    (2, "s", "set") ∈ writesOfDecision laterPass (discover laterPass).pinned
      #[some 0, some 2, none] ∧
    nextHolds laterPass 2 = true ∧
    (run laterPass).changesNext = true ∧ (run laterPass).passes = 2 := by
  decide +kernel

/-- `next` keeps `current`'s `x` in place and adds a key. -/
private def inPlace : Input where
  cur := ⟨#[plain [("a", .ref 1)], plain [("v", num 1)]], .ref 0⟩
  next := ⟨#[plain [("a", .ref 1), ("n", num 1)], plain [("v", num 1)]], .ref 0⟩
  same := #[none, some 1]

/-- An object in place passes the rule, and the call writes only the added key. -/
example :
    coherent inPlace = true ∧ (run inPlace).ok = true ∧
    (run inPlace).allWrites = [(0, "n", "set")] := by
  decide +kernel

/-- `x`, in place at `a`, refers back to `current`, so `next` holds `current` itself. -/
private def rootCycle : Input where
  cur := ⟨#[plain [("a", .ref 1)], plain [("up", .ref 0)]], .ref 0⟩
  next := ⟨#[plain [("a", .ref 1), ("n", num 1)], plain [("up", .ref 2)], plain [("a", .ref 1)]],
    .ref 0⟩
  same := #[none, some 1, some 0]

/-- When `next` holds `current` below a new root, the root keeps `current`, an object `next` holds
at another node, and the rule rejects the call: before the rule, publishing `x` wrote a copy of
`current` into it. -/
example :
    coherent rootCycle = true ∧ (run rootCycle).changesNext = true ∧
    (run rootCycle).passes = 0 ∧
    (1, "up", "set") ∈ publishedWrites rootCycle (discover rootCycle).pinned
      ((rounds rootCycle (discover rootCycle) 0).getLastD #[]) ∧
    nextHolds rootCycle 1 = true := by
  decide +kernel

end Reconcile.Spec.Reconcile
