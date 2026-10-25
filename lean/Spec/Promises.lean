import Spec.Reconcile
import Spec.Produce

/-!
# The promises: theorems about the reference models

Each theorem states a promise the documentation makes, about the executable reference the random
differential bridge compares with the runtime. The bridge carries the promise to the runtime; the
theorem shows the reference keeps it on every input, not only the generated ones.

- `retainPrefix`: the retained prefix is a prefix of `next`'s order, a subsequence of `cur`'s, and
  the longest such prefix (`retainPrefix_prefix`, `retainPrefix_sublist`, `retainPrefix_longest`).
  The keys or entries outside it are the moves.
- `reconcile`: a getter of `current` runs at most once per decision pass beyond its first read,
  and at most once when no pass writes (`get_bound`, `read_once_before_write`); the number of
  decision passes is bounded by the number of node pairs (`passes_le`): no plan search.
- `reconcile` writes: a retained key is written exactly when its value differs, a moved or added
  key always (`objectWrites_set_iff`); a kept object keeps the attributes of every property it had
  and adds the rest writable and configurable with `next`'s enumerability (`keptObject_attrs`);
  demotion forbids only an object whose writes block (`mem_blockedObjects`) and never one an
  earlier pass forbade, so every pass that continues forbids a new current object
  (`blocked_fresh`); no demand asks a candidate's own node for another object, so a candidate
  that can never be kept reorders nothing (`demands_satisfiable`); a node that keeps nothing holds
  a fresh copy and its origin is none (`publish_origins`, `publish_fresh`).
- `produce`: a current object is kept exactly when its subtree is unchanged, and the kept set is
  the greatest such set (`kept_closed`, `kept_greatest`).
- `snapshot`: one copy per source node, every origin fresh (`snapshot_size`, `snapshot_copy`,
  `snapshot_fresh`).

Four counterexamples each show, on one input, a wrong definition that a theorem rules out:
retaining only the common prefix, reading back after a write-free pass, writing every key and
re-adding a moved key as plain data.
-/

namespace Reconcile.Spec.Reconcile

open Reconcile.Spec

/-! ## Retention -/

section Retention

variable {K : Type} [DecidableEq K]

theorem isSubseq_iff (l m : List K) : isSubseq l m = true ↔ l.Sublist m := by
  induction m generalizing l with
  | nil =>
    cases l with
    | nil => simp [isSubseq]
    | cons a as => simp [isSubseq]
  | cons b bs ih =>
    cases l with
    | nil => simp [isSubseq]
    | cons a as =>
      by_cases h : a = b
      · subst h
        simp [isSubseq, ih]
      · simp only [isSubseq, h, if_false, ih]
        constructor
        · intro hs
          exact hs.cons b
        · intro hs
          rcases List.sublist_cons_iff.mp hs with hs | ⟨r, hr, _⟩
          · exact hs
          · cases hr
            exact absurd rfl h

theorem retainLength_le (cur next : List K) (k : Nat) : retainLength cur next k ≤ k := by
  induction k with
  | zero => simp [retainLength]
  | succ k ih =>
    simp only [retainLength]
    split
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le ih

theorem retainLength_subseq (cur next : List K) (k : Nat) :
    isSubseq (next.take (retainLength cur next k)) cur = true := by
  induction k with
  | zero => simp [retainLength, isSubseq]
  | succ k ih =>
    simp only [retainLength]
    split
    · assumption
    · exact ih

theorem retainLength_maximal (cur next : List K) (k j : Nat) (hj : j ≤ k)
    (h : isSubseq (next.take j) cur = true) : j ≤ retainLength cur next k := by
  induction k with
  | zero => exact hj
  | succ k ih =>
    simp only [retainLength]
    split
    · exact hj
    · rename_i hk
      apply ih
      rcases Nat.lt_or_eq_of_le hj with hlt | heq
      · exact Nat.le_of_lt_succ hlt
      · subst heq
        exact absurd h hk

/-- The retained prefix is a prefix of `next`'s order. -/
theorem retainPrefix_prefix (cur next : List K) : (retainPrefix cur next).IsPrefix next :=
  List.take_prefix _ _

/-- The retained prefix is a subsequence of `cur`'s order: nothing in it moves. -/
theorem retainPrefix_sublist (cur next : List K) : (retainPrefix cur next).Sublist cur :=
  (isSubseq_iff _ _).mp (retainLength_subseq cur next next.length)

/-- No longer prefix of `next` is a subsequence of `cur`: every key or entry outside the retained
prefix must move, so the retained prefix rule makes the fewest moves among prefix rules. -/
theorem retainPrefix_longest (cur next : List K) (p : List K) (hp : p.IsPrefix next)
    (hs : p.Sublist cur) : p.length ≤ (retainPrefix cur next).length := by
  have hp' : p = next.take p.length := by
    rw [List.prefix_iff_eq_take.mp hp]
    simp
  have hk : p.length ≤ next.length := hp.length_le
  have := retainLength_maximal cur next next.length p.length hk (by
    rw [← hp']
    exact (isSubseq_iff _ _).mpr hs)
  simp only [retainPrefix, List.length_take]
  exact Nat.le_min.mpr ⟨this, hk⟩

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

/-- When no pass writes, a getter of `current` runs at most once. -/
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

/-! ## Passes -/

theorem demote_length_le (input : Input) (al : Discovery) (pin : Array Bool) :
    ∀ fuel forbidden written, (demote input al pin fuel forbidden written).length ≤ fuel + 1 := by
  intro fuel
  induction fuel with
  | zero => intro forbidden written; simp [demote]
  | succ fuel ih =>
    intro forbidden written
    simp only [demote]
    split
    · simp
    · simp only [List.length_cons]
      exact Nat.succ_le_succ (ih _ _)

/-- The number of decision passes is at most one per pair of a next node and a current object,
plus two: a decision is final after as many demotions as there are pairs to forbid, and no plan is
searched. -/
theorem fuelOf_normalized (input : Input) :
    fuelOf (normalized input) = input.next.nodes.size * (input.cur.nodes.size + 1) + 1 := by
  simp [fuelOf, normalized, Graph.normalize]

/-- The passes of a run: none when the call is rejected statically or has nothing to do, else the
decision passes of the budget. -/
theorem run_passes (input : Input) : (run input).passes = 0 ∨
    (run input).passes = (demote (normalized input) (discover (normalized input))
      (discover (normalized input)).pinned (fuelOf (normalized input))
      [] []).length := by
  simp only [run]
  split
  · split
    · exact Or.inl rfl
    · split
      · exact Or.inr rfl
      · exact Or.inr rfl
  · exact Or.inl rfl

theorem passes_le (input : Input) :
    (run input).passes ≤ input.next.nodes.size * (input.cur.nodes.size + 1) + 2 := by
  rcases run_passes input with h | h <;> rw [h]
  · exact Nat.zero_le _
  · have := demote_length_le (normalized input) (discover (normalized input))
      (discover (normalized input)).pinned (fuelOf (normalized input)) [] []
    have hf := fuelOf_normalized input
    omega

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

/-! ## Descriptors -/

def fieldsOf : Obj → List (String × Slot)
  | .object _ fields _ => fields
  | _ => []

theorem attrsOf_slotWith (cs : Slot) (v : Val) : attrsOf (slotWith cs v) = attrsOf cs := by
  cases cs <;> rfl

/-- A kept object keeps the attributes of every property it had, retained or moved, and an added
property is writable and configurable with `next`'s enumerability. -/
theorem keptObject_attrs (proto : Proto) (cFields : List (String × Slot)) (extensible : Bool)
    (nFields : List (String × Slot)) :
    ∀ p ∈ fieldsOf (keptObject proto cFields extensible nFields),
      ∃ ns, (p.1, ns) ∈ nFields ∧ attrsOf p.2 =
        (match cFields.lookup p.1 with
          | some cs => attrsOf cs
          | none => ⟨true, ns.enumerable, true⟩) := by
  intro p hp
  simp only [keptObject, fieldsOf, List.mem_map] at hp
  obtain ⟨⟨k, ns⟩, hmem, rfl⟩ := hp
  refine ⟨ns, hmem, ?_⟩
  simp only
  split
  · rename_i cs heq
    rw [heq]
    split
    · exact attrsOf_slotWith cs _
    · rfl
  · rename_i heq
    rw [heq]
    simp [attrsOf]

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


/-- A left fold keeps a property that its start has and that every step keeps. -/
theorem foldl_inv {α γ : Type} (P : γ → Prop) (f : γ → α → γ) :
    ∀ (l : List α) (init : γ), P init → (∀ acc a, a ∈ l → P acc → P (f acc a)) →
      P (l.foldl f init)
  | [], _, h, _ => h
  | a :: l, init, h, hs =>
    foldl_inv P f l (f init a) (hs init a (List.mem_cons_self ..) h)
      (fun acc b hb => hs acc b (List.mem_cons_of_mem _ hb))

/-- Every pair `establish` reserves passed its checks, so none reserves a forbidden object. -/
theorem establish_fresh (input : Input) (candidatesOf : Nat → List Nat) (forbidden : List Nat)
    (written : List Requirement) (kept : Array (Option Nat)) (decided : Array Bool)
    (required : Array (Option Nat)) (used : List Nat) :
    ∀ fuel chain c x r,
      establish input candidatesOf forbidden written kept decided required used fuel chain c x =
        some r →
      (∀ p ∈ chain, forbidden.contains p.2 = false) → ∀ p ∈ r, forbidden.contains p.2 = false := by
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
    have hx : forbidden.contains x = false := by
      simp only [Bool.or_eq_true, not_or] at hcond
      exact Bool.eq_false_iff.mpr hcond.1.1
    revert r
    refine foldl_inv
      (fun (o : Option (List Requirement)) => ∀ r, o = some r →
        ∀ p ∈ r, forbidden.contains p.2 = false) _ _ _ ?_ ?_
    · intro r hr p hp
      cases hr
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hx
      · exact hchain p hp
    · intro acc ⟨cv, nv⟩ _ hacc r hr
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

/-- What a decision state never holds: a forbidden object kept at an unpinned node, or required
at any node. -/
abbrev freshDecision (pin : Array Bool) (forbidden : List Nat) (d : Decision) : Prop :=
  (∀ j x : Nat, pin[j]?.getD false = false → d.kept[j]?.bind id = some x →
    forbidden.contains x = false) ∧
  (∀ c x : Nat, d.required[c]?.bind id = some x → forbidden.contains x = false)

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

/-- A decision never keeps a forbidden object at a node that is not pinned. -/
theorem decide_fresh (input : Input) (al : Discovery) (pin : Array Bool) (forbidden : List Nat)
    (written : List Requirement) (j x : Nat) (hpin : pin[j]?.getD false = false)
    (h : (decide input al pin forbidden written)[j]?.bind id = some x) :
    forbidden.contains x = false := by
  unfold decide at h
  revert h
  apply (show ∀ d : Decision, freshDecision pin forbidden d →
      d.kept[j]?.bind id = some x → forbidden.contains x = false from
    fun d hd => hd.1 j x hpin)
  apply foldl_inv
  · constructor
    · intro k y hk hy
      simp only [Array.getElem?_map, Array.getElem?_range] at hy
      split at hy
      · simp only [Option.map_some, Option.bind_some, id] at hy
        rw [hk] at hy
        simp at hy
      · simp at hy
    · intro c y hy
      simp only [Array.getElem?_replicate] at hy
      split at hy <;> simp at hy
  · intro d k _ hd
    dsimp only
    split
    · exact hd
    split
    · rename_i x0 hreq
      refine ⟨fun k' y hk' hy => ?_, hd.2⟩
      rcases setIfInBounds_bind hy with ⟨rfl, rfl⟩ | hy
      · exact hd.2 _ _ hreq
      · exact hd.1 k' y hk' hy
    split
    · exact ⟨hd.1, hd.2⟩
    rename_i pairs hfind
    obtain ⟨x0, _, hest⟩ := List.exists_of_findSome?_eq_some hfind
    have hpairs := establish_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ hest (by simp)
    refine foldl_inv (freshDecision pin forbidden) _ pairs _ ⟨hd.1, hd.2⟩ ?_
    intro d' p hp hd'
    obtain ⟨c, y⟩ := p
    have hy : forbidden.contains y = false := hpairs (c, y) hp
    dsimp only
    split
    · refine ⟨fun k' z hk' hz => ?_, hd'.2⟩
      rcases setIfInBounds_bind hz with ⟨rfl, rfl⟩ | hz
      · exact hy
      · exact hd'.1 k' z hk' hz
    · refine ⟨hd'.1, fun c' z hz => ?_⟩
      rcases setIfInBounds_bind hz with ⟨rfl, rfl⟩ | hz
      · exact hy
      · exact hd'.2 c' z hz

/-- A pass never finds blocked an object an earlier pass forbade: every blocked object is kept at
an unpinned node (`mem_blockedObjects`), and the decision keeps no forbidden object there. So each
pass that does not end the run forbids a current object no earlier pass forbade, and the passes
end within one more than the number of current objects, whatever the budget. -/
theorem blocked_fresh (input : Input) (al : Discovery) (pin : Array Bool) (forbidden : List Nat)
    (written : List Requirement) (i : Nat)
    (h : i ∈ blockedObjects input pin (decide input al pin forbidden written)) :
    forbidden.contains i = false := by
  obtain ⟨j, _, hpin, hkept, _⟩ := mem_blockedObjects input pin _ i h
  exact decide_fresh input al pin forbidden written j i hpin hkept

/-! ## Demands -/

/-- No demand asks a candidate's own node for another object: every demand comes from an admitted
candidate `x` of some node `c`, through a fixed slot, and names `c` only with `x` itself. -/
theorem demands_satisfiable (input : Input) (al : Discovery) (c' x' : Nat)
    (h : (c', x') ∈ demands input al) :
    ∃ c x, x ∈ al.candidates[c]?.getD [] ∧ admitted input c x = true ∧
      (Val.ref x', Val.ref c') ∈ fixedPairs (input.cur.node x) (input.next.node c) ∧
      (c' = c → x' = x) := by
  simp only [demands, List.mem_flatMap, List.mem_range] at h
  obtain ⟨c, _, x, hx, hmem⟩ := h
  split at hmem
  · rename_i hadm
    simp only [List.mem_filterMap] at hmem
    obtain ⟨⟨cv, nv⟩, hpair, hsome⟩ := hmem
    cases cv with
    | prim p => cases nv <;> simp at hsome
    | ref y =>
      cases nv with
      | prim q => simp at hsome
      | ref d =>
        simp only at hsome
        split at hsome
        · simp at hsome
        · rename_i hcond
          simp only [Option.some.injEq, Prod.mk.injEq] at hsome
          obtain ⟨rfl, rfl⟩ := hsome
          refine ⟨c, x, hx, hadm, hpair, fun hc => ?_⟩
          subst hc
          simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_and,
            Decidable.not_not] at hcond
          exact hcond trivial
  · simp at hmem

/-! ## Fresh copies -/

/-- The origins of a published result are the final decision: a node's origin is the object it
keeps, and none when the node is a fresh copy. -/
theorem publish_origins (input : Input) (al : Discovery) (pin : Array Bool)
    (rounds : List (Array (Option Nat))) (kept : Array (Option Nat)) (r : Nat) :
    (publish input al pin rounds kept r).origins = kept := rfl

/-- A node the decision keeps nothing at holds a fresh copy of `next`'s node. -/
theorem publish_fresh (input : Input) (al : Discovery) (pin : Array Bool)
    (rounds : List (Array (Option Nat))) (kept : Array (Option Nat)) (r j : Nat)
    (hj : j < input.next.nodes.size) (h : kept[j]?.bind id = none) :
    (publish input al pin rounds kept r).nodes[j]? = some (freshCopy (input.next.node j)) := by
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
        else .data ns.value ⟨true, cs.enumerable, true⟩
      | none => .data ns.value ⟨true, ns.enumerable, true⟩)) extensible

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
and refers only to nodes of the set; a created object refers only to kept created objects and
changed `Date` copies. -/
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

/-- Each copy is `copy` of its source node. -/
theorem snapshot_copy (cur : Graph) (i : Nat) :
    (snapshot cur).nodes[i]? = cur.nodes[i]?.map copy := by
  simp [snapshot]

/-- Every origin is fresh: the copy shares no object with the source. -/
theorem snapshot_fresh (cur : Graph) : ∀ o ∈ (snapshot cur).origins, o = .fresh := by
  intro o ho
  simp only [snapshot, Array.mem_map] at ho
  obtain ⟨_, _, rfl⟩ := ho
  rfl

end Reconcile.Spec.Produce
