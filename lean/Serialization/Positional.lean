import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup

/-!
# Positional wire

Every value position is a slot. A slot is a literal or a reference, and which one is decided by
its container's layout, never by the value: the wire reserves no number or string. Slot kinds
are alternating run lengths, starting with literals, whose last run is open (implied by the
payload length). Layouts and shapes are interned tables in first-use order.

This file proves, over an abstract wire value type:

* run encoding is a bijection between kind lists and canonical run lists (`kinds_runs`,
  `runs_kinds`);
* slot decoding inverts slot encoding for bounded references, and accepts nothing else
  (`decode_encode_slots`, `encode_decode_slots`);
* interning in first-use order is inverted exactly by the decoder's first-use and distinctness
  checks (`intern_canonical`, `canonical_intern`);
* a document of nodes decodes to exactly the encoded nodes, and every accepted document is the
  encoding of the nodes it decodes to (`decode_encode_document`, `encode_decode_document`).

`Values` abstracts the wire value channel. Its laws say only that literals and naturals each
round-trip; they need not be disjoint, which is the point: a slot's kind, not its value,
selects the reading.
-/

namespace SerializationPositional

/-! ## Alternating runs with an open last run -/

/-- Kinds: `false` is a literal slot, `true` a reference slot. -/
def runsGo : List Bool → Bool → Nat → List Nat
  | [], _, _ => []
  | b :: bs, k, c => if b = k then runsGo bs k (c + 1) else c :: runsGo bs b 1

/-- Canonical runs: maximal runs starting with literals, the last (open) run omitted. -/
def runsOf (ks : List Bool) : List Nat := runsGo ks false 0

/-- Expand runs over `n` slots. Only the first run may be empty, and the open last run must be
nonempty unless no run is listed. -/
def kindsGo : List Nat → Bool → Bool → Nat → Option (List Bool)
  | [], first, k, n => if first = true ∨ 0 < n then some (List.replicate n k) else none
  | r :: rs, first, k, n =>
    if n < r then none
    else if r = 0 ∧ first = false then none
    else (kindsGo rs false (!k) (n - r)).map (List.replicate r k ++ ·)

def kindsOf (rs : List Nat) (n : Nat) : Option (List Bool) := kindsGo rs true false n

theorem kindsGo_runsGo (ks : List Bool) :
    ∀ (k : Bool) (c : Nat) (first : Bool), (first = true ∨ 0 < c) →
      kindsGo (runsGo ks k c) first k (c + ks.length) = some (List.replicate c k ++ ks) := by
  induction ks with
  | nil =>
    intro k c first h
    simp [runsGo, kindsGo, h]
  | cons b bs ih =>
    intro k c first h
    by_cases hb : b = k
    · subst hb
      have := ih b (c + 1) first (Or.inr (Nat.succ_pos c))
      simp only [runsGo, if_true]
      rw [show c + (b :: bs).length = c + 1 + bs.length by simp; omega, this]
      simp [List.replicate_succ', List.append_assoc]
    · have hk : (!k) = b := by cases b <;> cases k <;> simp_all
      have := ih b 1 false (Or.inr Nat.one_pos)
      have hc : ¬(c = 0 ∧ first = false) := by
        rintro ⟨rfl, rfl⟩; simp at h
      simp only [runsGo, hb, if_false, kindsGo, hc, if_false]
      rw [show c + (b :: bs).length - c = 1 + bs.length by simp; omega, hk, this]
      simp

/-- Expanding the canonical runs of a kind list recovers it. -/
theorem kinds_runs (ks : List Bool) : kindsOf (runsOf ks) ks.length = some ks := by
  simpa [kindsOf, runsOf] using kindsGo_runsGo ks false 0 true (Or.inl rfl)

theorem runsGo_replicate (r : Nat) (k : Bool) (xs : List Bool) (c : Nat) :
    runsGo (List.replicate r k ++ xs) k c = runsGo xs k (c + r) := by
  induction r generalizing c with
  | zero => rfl
  | succ r ih =>
    rw [List.replicate_succ, List.cons_append]
    simp only [runsGo, if_true]
    rw [ih]
    congr 1
    omega

theorem kindsGo_head {rs : List Nat} {k : Bool} {n : Nat} {ks : List Bool}
    (h : kindsGo rs false k n = some ks) : ∃ tail, ks = k :: tail := by
  cases rs with
  | nil =>
    simp only [kindsGo] at h
    split at h
    · rename_i hn
      simp at hn
      cases h
      exact ⟨List.replicate (n - 1) k, by
        rw [← List.replicate_succ]; congr 1; omega⟩
    · cases h
  | cons r rs =>
    simp only [kindsGo] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i _ hr
        obtain ⟨ks', _, rfl⟩ := Option.map_eq_some_iff.mp h
        have : r ≠ 0 := by simpa using hr
        obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero this
        exact ⟨List.replicate r' k ++ ks', by simp [List.replicate_succ]⟩

theorem runsGo_kindsGo (rs : List Nat) :
    ∀ (first k : Bool) (n : Nat) (ks : List Bool), kindsGo rs first k n = some ks →
      runsGo ks k 0 = rs := by
  induction rs with
  | nil =>
    intro first k n ks h
    simp only [kindsGo] at h
    split at h
    · cases h
      simpa using runsGo_replicate n k [] 0
    · cases h
  | cons r rs ih =>
    intro first k n ks h
    simp only [kindsGo] at h
    split at h
    · cases h
    · split at h
      · cases h
      · obtain ⟨ks', hks', rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨tail, rfl⟩ := kindsGo_head hks'
        have hrest := ih false (!k) (n - r) _ hks'
        rw [runsGo_replicate]
        cases k <;> simpa [runsGo] using hrest

/-- Canonical runs are unique: any accepted run list is the canonical one for its kinds. -/
theorem runs_kinds {rs : List Nat} {n : Nat} {ks : List Bool} (h : kindsOf rs n = some ks) :
    runsOf ks = rs :=
  runsGo_kindsGo rs true false n ks h

theorem kindsGo_length (rs : List Nat) :
    ∀ (first k : Bool) (n : Nat) (ks : List Bool), kindsGo rs first k n = some ks →
      ks.length = n := by
  induction rs with
  | nil =>
    intro first k n ks h
    simp only [kindsGo] at h
    split at h
    · cases h; simp
    · cases h
  | cons r rs ih =>
    intro first k n ks h
    simp only [kindsGo] at h
    split at h
    · cases h
    · rename_i hn
      split at h
      · cases h
      · obtain ⟨ks', hks', rfl⟩ := Option.map_eq_some_iff.mp h
        have := ih false (!k) (n - r) ks' hks'
        simp [this]; omega

/-! ## Slots -/

/-- The wire value channel: literals and naturals each round-trip. They may overlap. -/
structure Values (σ W : Type) where
  lit : σ → W
  nat : Nat → W
  ofLit : W → Option σ
  ofNat : W → Option Nat
  ofLit_lit : ∀ s, ofLit (lit s) = some s
  ofNat_nat : ∀ i, ofNat (nat i) = some i
  lit_ofLit : ∀ w s, ofLit w = some s → lit s = w
  nat_ofNat : ∀ w i, ofNat w = some i → nat i = w

inductive Slot (σ : Type) where
  | lit : σ → Slot σ
  | ref : Nat → Slot σ
  deriving DecidableEq, Repr

def Slot.isRef {σ : Type} : Slot σ → Bool
  | .lit _ => false
  | .ref _ => true

variable {σ W : Type}

def wireOf (V : Values σ W) : Slot σ → W
  | .lit s => V.lit s
  | .ref i => V.nat i

/-- Read one slot of the given kind; a reference must name an existing node. -/
def readSlot (V : Values σ W) (n : Nat) (k : Bool) (w : W) : Option (Slot σ) :=
  if k then
    match V.ofNat w with
    | some i => if i < n then some (.ref i) else none
    | none => none
  else (V.ofLit w).map .lit

def readAll (V : Values σ W) (n : Nat) : List Bool → List W → Option (List (Slot σ))
  | [], [] => some []
  | k :: ks, w :: ws => do
    let s ← readSlot V n k w
    let rest ← readAll V n ks ws
    pure (s :: rest)
  | _, _ => none

def encodeSlots (V : Values σ W) (ss : List (Slot σ)) : List Nat × List W :=
  (runsOf (ss.map Slot.isRef), ss.map (wireOf V))

def decodeSlots (V : Values σ W) (n : Nat) (rs : List Nat) (ws : List W) :
    Option (List (Slot σ)) := do
  let ks ← kindsOf rs ws.length
  readAll V n ks ws

/-- Every reference names one of `n` nodes. -/
def Bounded (n : Nat) (ss : List (Slot σ)) : Prop := ∀ i, Slot.ref i ∈ ss → i < n

theorem readAll_encode (V : Values σ W) (n : Nat) (ss : List (Slot σ)) (h : Bounded n ss) :
    readAll V n (ss.map Slot.isRef) (ss.map (wireOf V)) = some ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    have hs : Bounded n ss := fun i hi => h i (List.mem_cons_of_mem _ hi)
    cases s with
    | lit v => simp [readAll, readSlot, Slot.isRef, wireOf, V.ofLit_lit, ih hs]
    | ref i =>
      have hi : i < n := h i (by simp)
      simp [readAll, readSlot, Slot.isRef, wireOf, V.ofNat_nat, hi, ih hs]

theorem decode_encode_slots (V : Values σ W) (n : Nat) (ss : List (Slot σ)) (h : Bounded n ss) :
    decodeSlots V n (encodeSlots V ss).1 (encodeSlots V ss).2 = some ss := by
  have hk := kinds_runs (ss.map Slot.isRef)
  simp only [List.length_map] at hk
  simp [decodeSlots, encodeSlots, hk, readAll_encode V n ss h]

theorem readAll_sound (V : Values σ W) (n : Nat) :
    ∀ (ks : List Bool) (ws : List W) (ss : List (Slot σ)), readAll V n ks ws = some ss →
      ss.map Slot.isRef = ks ∧ ss.map (wireOf V) = ws ∧ Bounded n ss := by
  intro ks
  induction ks with
  | nil =>
    intro ws ss h
    cases ws with
    | nil => cases h; exact ⟨rfl, rfl, fun _ hi => by simp at hi⟩
    | cons => simp [readAll] at h
  | cons k ks ih =>
    intro ws ss h
    cases ws with
    | nil => simp [readAll] at h
    | cons w ws =>
      simp only [readAll] at h
      cases hs : readSlot V n k w with
      | none => simp [hs] at h
      | some s =>
        cases hr : readAll V n ks ws with
        | none => simp [hs, hr] at h
        | some rest =>
          simp only [hs, hr, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
          subst h
          obtain ⟨h1, h2, h3⟩ := ih ws rest hr
          unfold readSlot at hs
          split at hs
          · rename_i hk
            split at hs
            · rename_i i hi
              split at hs
              · rename_i hlt
                cases hs
                refine ⟨by simp [Slot.isRef, hk, h1], by simp [wireOf, V.nat_ofNat w i hi, h2], ?_⟩
                intro j hj
                rcases List.mem_cons.mp hj with e | e
                · cases e; exact hlt
                · exact h3 j e
              · cases hs
            · cases hs
          · rename_i hk
            obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hs
            refine ⟨by simp [Slot.isRef, h1]; cases k <;> simp_all,
              by simp [wireOf, V.lit_ofLit w v hv, h2], ?_⟩
            intro j hj
            rcases List.mem_cons.mp hj with e | e
            · cases e
            · exact h3 j e

/-- Every accepted payload is the encoding of the slots it decodes to. -/
theorem encode_decode_slots (V : Values σ W) {n : Nat} {rs : List Nat} {ws : List W}
    {ss : List (Slot σ)} (h : decodeSlots V n rs ws = some ss) :
    encodeSlots V ss = (rs, ws) ∧ Bounded n ss := by
  simp only [decodeSlots] at h
  cases hk : kindsOf rs ws.length with
  | none => simp [hk] at h
  | some ks =>
    simp only [hk] at h
    obtain ⟨h1, h2, h3⟩ := readAll_sound V n ks ws ss h
    refine ⟨?_, h3⟩
    simp [encodeSlots, h1, h2, runs_kinds hk]

/-! ## Interning in first-use order -/

/-- Encoder interning: reuse an existing entry's index or append a new entry. -/
def intern {α : Type} [DecidableEq α] (table : List α) (x : α) : Nat × List α :=
  if x ∈ table then (table.idxOf x, table) else (table.length, table ++ [x])

def internAll {α : Type} [DecidableEq α] : List α → List α → List Nat × List α
  | table, [] => ([], table)
  | table, x :: xs =>
    let (i, table') := intern table x
    let (ids, final) := internAll table' xs
    (i :: ids, final)

/-- Decoder check: each id is an existing one or the next new one; returns the count used. -/
def firstUse : Nat → List Nat → Option Nat
  | m, [] => some m
  | m, i :: is => if i < m then firstUse m is else if i = m then firstUse (m + 1) is else none

theorem idxOf_take_nodup {α : Type} [DecidableEq α] (t : List α) (hn : t.Nodup) :
    ∀ (m i : Nat), i < m → m ≤ t.length → (hi : i < t.length) →
      t[i] ∈ t.take m ∧ (t.take m).idxOf t[i] = i := by
  intro m i him hm hi
  have hmem : t[i] ∈ t.take m := by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp; omega, by simp [List.getElem_take]⟩
  refine ⟨hmem, ?_⟩
  have hnd : (t.take m).Nodup := hn.sublist (List.take_sublist _ _)
  have hlt : i < (t.take m).length := by simp; omega
  have := List.get_idxOf hnd ⟨i, hlt⟩
  simpa [List.getElem_take] using this

theorem not_mem_take_nodup {α : Type} (t : List α) (hn : t.Nodup) (m : Nat)
    (hm : m < t.length) : t[m] ∉ t.take m := by
  intro hmem
  rw [List.mem_iff_getElem] at hmem
  obtain ⟨j, hj, he⟩ := hmem
  simp only [List.length_take, List.getElem_take] at hj he
  have := (List.Nodup.getElem_inj_iff hn (hi := by omega) (hj := hm)).mp he
  omega

/-- Canonical tables: a first-use-ordered id list over a duplicate-free table using every entry
is exactly what interning its values produces. -/
theorem canonical_intern {α : Type} [DecidableEq α] (t : List α) (hn : t.Nodup) :
    ∀ (ids : List Nat) (vs : List α) (m : Nat), m ≤ t.length →
      firstUse m ids = some t.length → ids.map (fun i => t[i]?) = vs.map some →
      internAll (t.take m) vs = (ids, t) := by
  intro ids
  induction ids with
  | nil =>
    intro vs m hm hf hv
    simp only [firstUse, Option.some.injEq] at hf
    subst hf
    cases vs with
    | nil => simp [internAll]
    | cons => simp at hv
  | cons i is ih =>
    intro vs m hm hf hv
    cases vs with
    | nil => simp at hv
    | cons v vs =>
      simp only [List.map_cons, List.cons.injEq] at hv
      obtain ⟨hiv, hrest⟩ := hv
      have hi : i < t.length := by
        by_contra hge; rw [List.getElem?_eq_none (by omega)] at hiv; cases hiv
      have hval : t[i] = v := by
        rw [List.getElem?_eq_getElem hi] at hiv; exact Option.some.inj hiv
      subst hval
      simp only [firstUse] at hf
      split at hf
      · rename_i him
        obtain ⟨hmem, hidx⟩ := idxOf_take_nodup t hn m i him hm hi
        simp only [internAll, intern, hmem, if_true, hidx, ih vs m hm hf hrest]
      · split at hf
        · rename_i _ him
          subst him
          have hnot := not_mem_take_nodup t hn i hi
          have htake : t.take i ++ [t[i]] = t.take (i + 1) := by
            rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
          have hlen : (t.take i).length = i := by simp; omega
          simp only [internAll, intern, hnot, if_false, hlen, htake, ih vs (i + 1) (by omega) hf hrest]
        · cases hf

theorem intern_extends {α : Type} [DecidableEq α] (table : List α) (x : α) :
    ∃ suffix, (intern table x).2 = table ++ suffix := by
  unfold intern; split
  · exact ⟨[], by simp⟩
  · exact ⟨[x], rfl⟩

/-- Encoder output satisfies the decoder's checks and indexes back to the input values. -/
theorem intern_canonical {α : Type} [DecidableEq α] :
    ∀ (xs table : List α), table.Nodup →
      (internAll table xs).2.Nodup ∧
      firstUse table.length (internAll table xs).1 = some (internAll table xs).2.length ∧
      (internAll table xs).1.map (fun i => (internAll table xs).2[i]?) = xs.map some ∧
      table <+: (internAll table xs).2 := by
  intro xs
  induction xs with
  | nil =>
    intro table hn
    simp [internAll, firstUse, hn]
  | cons x xs ih =>
    intro table hn
    by_cases hx : x ∈ table
    · have hint : intern table x = (table.idxOf x, table) := by simp [intern, hx]
      obtain ⟨h1, h2, h3, h4⟩ := ih table hn
      simp only [internAll, hint]
      have hlt : table.idxOf x < table.length := List.idxOf_lt_length_iff.mpr hx
      refine ⟨h1, ?_, ?_, h4⟩
      · simp [firstUse, hlt, h2]
      · obtain ⟨suffix, hs⟩ := h4
        simp only [List.map_cons, h3]
        congr 1
        rw [← hs, List.getElem?_append_left hlt, List.getElem?_idxOf hx]
    · have hint : intern table x = (table.length, table ++ [x]) := by simp [intern, hx]
      have hn' : (table ++ [x]).Nodup := by
        simp only [List.nodup_append, hn, List.nodup_singleton, true_and]
        intro a ha b hb e
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        subst hb e
        exact hx ha
      obtain ⟨h1, h2, h3, h4⟩ := ih (table ++ [x]) hn'
      simp only [internAll, hint]
      refine ⟨h1, ?_, ?_, ?_⟩
      · simpa [firstUse] using h2
      · obtain ⟨suffix, hs⟩ := h4
        simp only [List.map_cons, h3]
        congr 1
        rw [← hs]
        simp
      · obtain ⟨suffix, hs⟩ := h4
        exact ⟨[x] ++ suffix, by rw [← hs]; simp⟩

/-! ## Documents -/

/-- A container node: its layout key (node kind, shape and the like, without slot kinds) and
its slots. Native fixed-schema payloads are outside this model. -/
structure Node (κ σ : Type) where
  key : κ
  slots : List (Slot σ)
  deriving DecidableEq

/-- The interned layout of a node: its key plus canonical slot-kind runs. -/
def layoutOf {κ : Type} (v : Node κ σ) : κ × List Nat := (v.key, runsOf (v.slots.map Slot.isRef))

structure Document (κ W : Type) where
  layouts : List (κ × List Nat)
  descriptors : List Nat
  payloads : List (List W)

def encodeDocument {κ : Type} [DecidableEq κ] (V : Values σ W) (nodes : List (Node κ σ)) :
    Document κ W :=
  let (ids, table) := internAll [] (nodes.map layoutOf)
  ⟨table, ids, nodes.map fun v => v.slots.map (wireOf V)⟩

def decodeNodes {κ : Type} (V : Values σ W) (n : Nat) (layouts : List (κ × List Nat)) :
    List Nat → List (List W) → Option (List (Node κ σ))
  | [], [] => some []
  | d :: ds, p :: ps => do
    let (key, rs) ← layouts[d]?
    let ss ← decodeSlots V n rs p
    let rest ← decodeNodes V n layouts ds ps
    pure (⟨key, ss⟩ :: rest)
  | _, _ => none

/-- Decoder: tables must be duplicate-free and used in first-use order; references must name
one of the document's nodes. -/
def decodeDocument {κ : Type} [DecidableEq κ] (V : Values σ W) (d : Document κ W) :
    Option (List (Node κ σ)) :=
  if d.layouts.Nodup ∧ firstUse 0 d.descriptors = some d.layouts.length then
    decodeNodes V d.payloads.length d.layouts d.descriptors d.payloads
  else none

theorem decodeNodes_encode {κ : Type} (V : Values σ W) (n : Nat) (layouts : List (κ × List Nat)) :
    ∀ (nodes : List (Node κ σ)) (ids : List Nat),
      (∀ v ∈ nodes, Bounded n v.slots) →
      ids.map (fun i => layouts[i]?) = (nodes.map layoutOf).map some →
      decodeNodes V n layouts ids (nodes.map fun v => v.slots.map (wireOf V)) = some nodes := by
  intro nodes
  induction nodes with
  | nil => intro ids _ h; cases ids <;> simp_all [decodeNodes]
  | cons v vs ih =>
    intro ids hb h
    cases ids with
    | nil => simp at h
    | cons i is =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨hi, his⟩ := h
      have hv := decode_encode_slots V n v.slots (hb v (by simp))
      simp only [encodeSlots] at hv
      simp [decodeNodes, hi, layoutOf, hv, ih is (fun w hw => hb w (by simp [hw])) his]

/-- Decoding inverts encoding when every reference names one of the nodes. -/
theorem decode_encode_document {κ : Type} [DecidableEq κ] (V : Values σ W)
    (nodes : List (Node κ σ)) (hb : ∀ v ∈ nodes, Bounded nodes.length v.slots) :
    decodeDocument V (encodeDocument V nodes) = some nodes := by
  obtain ⟨h1, h2, h3, _⟩ := intern_canonical (nodes.map layoutOf) [] List.nodup_nil
  simp only [encodeDocument, decodeDocument]
  simp only [List.length_nil] at h2
  simp only [h1, h2, true_and, if_true, List.length_map]
  exact decodeNodes_encode V nodes.length _ nodes _ hb h3

theorem decodeNodes_sound {κ : Type} (V : Values σ W) (n : Nat) (layouts : List (κ × List Nat)) :
    ∀ (ds : List Nat) (ps : List (List W)) (nodes : List (Node κ σ)),
      decodeNodes V n layouts ds ps = some nodes →
      ps = nodes.map (fun v => v.slots.map (wireOf V)) ∧
      ds.map (fun i => layouts[i]?) = (nodes.map layoutOf).map some ∧
      ∀ v ∈ nodes, Bounded n v.slots := by
  intro ds
  induction ds with
  | nil => intro ps nodes h; cases ps <;> simp_all [decodeNodes]
  | cons d ds ih =>
    intro ps nodes h
    cases ps with
    | nil => simp [decodeNodes] at h
    | cons p ps =>
      simp only [decodeNodes] at h
      cases hl : layouts[d]? with
      | none => simp [hl] at h
      | some e =>
        rcases e with ⟨key, rs⟩
        cases hs : decodeSlots V n rs p with
        | none => simp [hl, hs] at h
        | some ss =>
          cases hr : decodeNodes V n layouts ds ps with
          | none => simp [hl, hr] at h
          | some rest =>
            simp only [hl, Option.bind_eq_bind, Option.bind_some, hs, hr, Option.pure_def,
              Option.some.injEq] at h
            subst h
            obtain ⟨he, hbnd⟩ := encode_decode_slots V hs
            simp only [encodeSlots, Prod.mk.injEq] at he
            obtain ⟨p1, p2, p3⟩ := ih ps rest hr
            refine ⟨by simp [he.2, p1], by simp [hl, layoutOf, he.1, p2], ?_⟩
            intro v hv
            rcases List.mem_cons.mp hv with e | e
            · subst e; exact hbnd
            · exact p3 v e

/-- Canonicity: every accepted document is the encoding of the nodes it decodes to. -/
theorem encode_decode_document {κ : Type} [DecidableEq κ] (V : Values σ W)
    (d : Document κ W) (nodes : List (Node κ σ)) (h : decodeDocument V d = some nodes) :
    encodeDocument V nodes = d := by
  simp only [decodeDocument] at h
  split at h
  · rename_i hc
    obtain ⟨hn, hf⟩ := hc
    obtain ⟨p1, p2, _⟩ := decodeNodes_sound V _ _ _ _ _ h
    have hc := canonical_intern d.layouts hn d.descriptors (nodes.map layoutOf) 0
      (Nat.zero_le _) hf p2
    simp only [List.take_zero] at hc
    rcases d with ⟨layouts, descriptors, payloads⟩
    simp only at hc p1
    simp only [encodeDocument, hc, p1]
  · cases h

/-! ## Relaxed document decoding

The runtime decoder checks meaning, not canonical form: it does not require the tables to be
duplicate-free or in first-use order. `decodeNodes` alone is that decoder. It still inverts the
encoder, and `decodeNodes_sound` says every accepted document is the slot encoding of the
nodes it decodes to, with each layout id naming that node's layout and every reference in
range; the canonical theorems above remain the stronger model of the encoder's output. -/

def decodeRelaxed {κ : Type} (V : Values σ W) (d : Document κ W) : Option (List (Node κ σ)) :=
  decodeNodes V d.payloads.length d.layouts d.descriptors d.payloads

theorem decode_encode_relaxed {κ : Type} [DecidableEq κ] (V : Values σ W)
    (nodes : List (Node κ σ)) (hb : ∀ v ∈ nodes, Bounded nodes.length v.slots) :
    decodeRelaxed V (encodeDocument V nodes) = some nodes := by
  obtain ⟨_, _, h3, _⟩ := intern_canonical (nodes.map layoutOf) [] List.nodup_nil
  simp only [encodeDocument, decodeRelaxed, List.length_map]
  exact decodeNodes_encode V nodes.length _ nodes _ hb h3

/-! ## Control table framing

Shapes, layouts and layout ids travel in one control array: the layout id of each node (their
count is the number of payloads), the number of shapes, each shape framed by its length, then
each layout framed by its length up to the end. Lengths use the natural-number channel. -/

def frame (V : Values σ W) : List (List W) → List W
  | [] => []
  | e :: es => V.nat e.length :: (e ++ frame V es)

/-- Reads framed entries until the input ends. -/
def unframe (V : Values σ W) : List W → Option (List (List W))
  | [] => some []
  | w :: ws =>
    match V.ofNat w with
    | some k => if k ≤ ws.length then (unframe V (ws.drop k)).map (ws.take k :: ·) else none
    | none => none
termination_by ws => ws.length
decreasing_by simp; omega

/-- Reads exactly `c` framed entries and returns the rest. -/
def unframeN (V : Values σ W) : Nat → List W → Option (List (List W) × List W)
  | 0, ws => some ([], ws)
  | _ + 1, [] => none
  | c + 1, w :: ws =>
    match V.ofNat w with
    | some k =>
      if k ≤ ws.length then (unframeN V c (ws.drop k)).map fun r => (ws.take k :: r.1, r.2)
      else none
    | none => none

theorem unframe_frame (V : Values σ W) : ∀ es : List (List W), unframe V (frame V es) = some es := by
  intro es
  induction es with
  | nil => simp [frame, unframe]
  | cons e es ih =>
    rw [frame, unframe]
    simp [V.ofNat_nat, ih]

theorem frame_unframe_bound (V : Values σ W) :
    ∀ (m : Nat) (ws : List W), ws.length ≤ m → ∀ es, unframe V ws = some es → frame V es = ws := by
  intro m
  induction m with
  | zero =>
    intro ws hl es h
    have : ws = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp only [unframe, Option.some.injEq, List.nil_eq] at h
    subst h; rfl
  | succ m ihm =>
    intro ws hl es h
    cases ws with
    | nil => simp only [unframe, Option.some.injEq, List.nil_eq] at h; subst h; rfl
    | cons w ws =>
      rw [unframe] at h
      split at h
      · rename_i k hk
        split at h
        · rename_i hle
          obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.mp h
          have := ihm (ws.drop k) (by simp at hl ⊢; omega) rest hrest
          simp only [frame, List.length_take, Nat.min_eq_left hle, V.nat_ofNat w k hk, this,
            List.take_append_drop]
        · cases h
      · cases h

theorem frame_unframe (V : Values σ W) (ws : List W) (es : List (List W))
    (h : unframe V ws = some es) : frame V es = ws :=
  frame_unframe_bound V _ ws (Nat.le_refl _) es h

theorem unframeN_frame (V : Values σ W) :
    ∀ (es : List (List W)) (rest : List W),
      unframeN V es.length (frame V es ++ rest) = some (es, rest) := by
  intro es
  induction es with
  | nil => intro rest; simp [frame, unframeN]
  | cons e es ih =>
    intro rest
    simp [frame, unframeN, V.ofNat_nat, ih]

theorem frame_unframeN (V : Values σ W) :
    ∀ (c : Nat) (ws : List W) (es : List (List W)) (rest : List W),
      unframeN V c ws = some (es, rest) → frame V es ++ rest = ws ∧ es.length = c := by
  intro c
  induction c with
  | zero => intro ws es rest h; simp only [unframeN, Option.some.injEq, Prod.mk.injEq, List.nil_eq] at h; obtain ⟨rfl, rfl⟩ := h; simp [frame]
  | succ c ih =>
    intro ws es rest h
    cases ws with
    | nil => simp [unframeN] at h
    | cons w ws =>
      simp only [unframeN] at h
      split at h
      · rename_i k hk
        split at h
        · rename_i hle
          obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨r1, r2⟩ := r
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          obtain ⟨h1, h2⟩ := ih _ _ _ hr
          refine ⟨?_, by simp [h2]⟩
          simp only [frame, List.length_take, Nat.min_eq_left hle, V.nat_ofNat w k hk,
            List.cons_append, List.append_assoc, h1, List.take_append_drop]
        · cases h
      · cases h

theorem mapM_ofNat (V : Values σ W) :
    ∀ ds : List Nat, (ds.map V.nat).mapM V.ofNat = some ds := by
  intro ds
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [List.mapM_cons, V.ofNat_nat, ih]

theorem ofNat_mapM (V : Values σ W) :
    ∀ (ws : List W) (ds : List Nat), ws.mapM V.ofNat = some ds → ds.map V.nat = ws := by
  intro ws
  induction ws with
  | nil =>
    intro ds h
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq, List.nil_eq] at h
    subst h; rfl
  | cons w ws ih =>
    intro ds h
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases hw : V.ofNat w with
    | none => simp [hw] at h
    | some d =>
      cases hr : ws.mapM V.ofNat with
      | none => simp [hw, hr] at h
      | some r =>
        simp only [hw, hr, Option.bind_some, Option.some.injEq] at h
        subst h
        simp [V.nat_ofNat w d hw, ih r hr]

def encodeControl (V : Values σ W) (ids : List Nat) (shapes layouts : List (List W)) : List W :=
  ids.map V.nat ++ (V.nat shapes.length :: (frame V shapes ++ frame V layouts))

/-- Splits the control array of a document with `n` nodes. -/
def decodeControl (V : Values σ W) (n : Nat) (ws : List W) :
    Option (List Nat × List (List W) × List (List W)) :=
  if n ≤ ws.length then
    match (ws.take n).mapM V.ofNat, ws.drop n with
    | some ids, c :: rest =>
      match V.ofNat c with
      | some k =>
        match unframeN V k rest with
        | some (shapes, tail) => (unframe V tail).map fun layouts => (ids, shapes, layouts)
        | none => none
      | none => none
    | _, _ => none
  else none

theorem decode_encode_control (V : Values σ W) (ids : List Nat) (shapes layouts : List (List W)) :
    decodeControl V ids.length (encodeControl V ids shapes layouts) = some (ids, shapes, layouts) := by
  have ht : (encodeControl V ids shapes layouts).take ids.length = ids.map V.nat := by
    simp [encodeControl]
  have hd : (encodeControl V ids shapes layouts).drop ids.length =
      V.nat shapes.length :: (frame V shapes ++ frame V layouts) := by
    simp [encodeControl]
  have hl : ids.length ≤ (encodeControl V ids shapes layouts).length := by simp [encodeControl]
  simp only [decodeControl, if_pos hl, ht, hd, mapM_ofNat, V.ofNat_nat, unframeN_frame,
    unframe_frame, Option.map_some]

theorem encode_decode_control (V : Values σ W) {n : Nat} {ws : List W}
    {ids : List Nat} {shapes layouts : List (List W)}
    (h : decodeControl V n ws = some (ids, shapes, layouts)) :
    encodeControl V ids shapes layouts = ws ∧ ids.length = n := by
  unfold decodeControl at h
  split at h
  · rename_i hn
    split at h
    · rename_i ids' c rest hm hd
      split at h
      · rename_i k hk
        split at h
        · rename_i sh tail hu
          obtain ⟨ls, hl, he⟩ := Option.map_eq_some_iff.mp h
          simp only [Prod.mk.injEq] at he
          obtain ⟨e1, e2, e3⟩ := he
          rw [← e1, ← e2, ← e3]
          obtain ⟨h1, h2⟩ := frame_unframeN V k rest sh tail hu
          have h3 := frame_unframe V tail ls hl
          have h4 := ofNat_mapM V _ _ hm
          have hlen : ids'.length = n := by
            have := congrArg List.length h4; simp at this; omega
          refine ⟨?_, hlen⟩
          rw [encodeControl, h4, h2, V.nat_ofNat c k hk, h3, h1, ← hd, List.take_append_drop]
        · cases h
      · cases h
    · cases h
  · cases h

/-! ## Typed references -/

/-- A dependent native (a view's buffer, an owned parameter list's URL) must reference a node of
the required kind, not merely an existing one. -/
def typedRef {κ : Type} (kindAt : Nat → Option κ) (required : κ → Bool) (i : Nat) : Option Nat :=
  match kindAt i with
  | some k => if required k then some i else none
  | none => none

theorem typedRef_sound {κ : Type} {kindAt : Nat → Option κ} {required : κ → Bool} {i j : Nat}
    (h : typedRef kindAt required i = some j) : j = i ∧ ∃ k, kindAt i = some k ∧ required k := by
  unfold typedRef at h
  split at h
  · rename_i k hk
    split at h
    · cases h; exact ⟨rfl, k, hk, by assumption⟩
    · cases h
  · cases h

/-! ## Renumbering provisional ids -/

theorem idxOf_map_injective {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (x : α) :
    ∀ (table : List α), (table.map f).idxOf (f x) = table.idxOf x := by
  intro table
  induction table with
  | nil => simp
  | cons y ys ih =>
    by_cases h : y = x
    · subst h; simp [List.idxOf_cons_self]
    · have : f y ≠ f x := fun e => h (hf e)
      simp [List.idxOf_cons_ne _ h, List.idxOf_cons_ne _ this, ih]

theorem intern_map {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (table : List α) (x : α) :
    intern (table.map f) (f x) = ((intern table x).1, (intern table x).2.map f) := by
  unfold intern
  by_cases hx : x ∈ table
  · have hm : f x ∈ table.map f := List.mem_map_of_mem hx
    simp [hx, hm, idxOf_map_injective f hf]
  · have hm : f x ∉ table.map f := by
      simp only [List.mem_map, not_exists, not_and]
      intro y hy e; exact hx (hf e ▸ hy)
    simp [hx, hm]

/-- Interning commutes with any injective renaming of the interned values. -/
theorem internAll_map {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) :
    ∀ (xs table : List α), internAll (table.map f) (xs.map f) =
      ((internAll table xs).1, (internAll table xs).2.map f) := by
  intro xs
  induction xs with
  | nil => intro table; simp [internAll]
  | cons x xs ih =>
    intro table
    simp only [List.map_cons, internAll, intern_map f hf, ih]

/-- The encoder learns a container's layout only when the container completes, so it numbers
layouts provisionally by any injective `f` (completion order) and then interns the provisional
ids in node order. That yields exactly the first-use ids of the layouts themselves, and the
renumbered table is the first-use layout table under `f`. -/
theorem renumber_first_use {α : Type} [DecidableEq α] (f : α → Nat)
    (hf : Function.Injective f) (layouts : List α) :
    internAll [] (layouts.map f) =
      ((internAll [] layouts).1, (internAll [] layouts).2.map f) := by
  simpa using internAll_map f hf layouts []

/-! ## Sparse presence -/

/-- Presence kinds of positions `e ..< L` for ascending present indices: `false` is a present
element and `true` a hole, so presence uses the same run encoding as slot kinds. -/
def gapKinds : List Nat → Nat → Nat → List Bool
  | [], e, L => List.replicate (L - e) true
  | i :: is, e, L => List.replicate (i - e) true ++ false :: gapKinds is (i + 1) L

/-- The encoder's incremental presence runs: `e` is the position after the last present element
and `p` the length of the open present run. A whole hole run is emitted at once. -/
def presenceGo : List Nat → Nat → Nat → Nat → List Nat
  | [], e, p, L => if e < L then [p] else []
  | i :: is, e, p, L =>
    if e < i then p :: (i - e) :: presenceGo is (i + 1) 1 L else presenceGo is (i + 1) (p + 1) L

def presenceRuns (is : List Nat) (L : Nat) : List Nat := presenceGo is 0 0 L

/-- Strictly ascending indices, each at least `e` and below `L`. -/
def Ascending : List Nat → Nat → Nat → Prop
  | [], _, _ => True
  | i :: is, e, L => e ≤ i ∧ i < L ∧ Ascending is (i + 1) L

theorem runsGo_holes (m p : Nat) :
    runsGo (List.replicate m true) false p = if 0 < m then [p] else [] := by
  cases m with
  | zero => rfl
  | succ m =>
    rw [List.replicate_succ]
    simp only [runsGo, Bool.true_eq_false, if_false]
    have := runsGo_replicate m true [] 1
    simp only [List.append_nil] at this
    simp [this, runsGo]

theorem presenceGo_runs :
    ∀ (is : List Nat) (e p L : Nat), Ascending is e L →
      presenceGo is e p L = runsGo (gapKinds is e L) false p := by
  intro is
  induction is with
  | nil =>
    intro e p L _
    simp only [presenceGo, gapKinds, runsGo_holes]
    by_cases h : e < L
    · simp [h, show 0 < L - e by omega]
    · simp [h, show ¬0 < L - e by omega]
  | cons i is ih =>
    intro e p L h
    obtain ⟨hei, _, hrest⟩ := h
    simp only [presenceGo, gapKinds]
    by_cases hlt : e < i
    · simp only [hlt, if_true]
      obtain ⟨m, hm⟩ : ∃ m, i - e = m + 1 := ⟨i - e - 1, by omega⟩
      rw [hm, List.replicate_succ, List.cons_append]
      simp only [runsGo, Bool.true_eq_false, if_false, runsGo_replicate, Bool.false_eq_true]
      rw [ih (i + 1) 1 L hrest]
      congr 2
      omega
    · have : i - e = 0 := by omega
      simp only [hlt, if_false, this, List.replicate_zero, List.nil_append, runsGo, if_true]
      exact ih (i + 1) (p + 1) L hrest

theorem gapKinds_length :
    ∀ (is : List Nat) (e L : Nat), Ascending is e L → e ≤ L →
      (gapKinds is e L).length = L - e := by
  intro is
  induction is with
  | nil => intro e L _ _; simp [gapKinds]
  | cons i is ih =>
    intro e L h _
    obtain ⟨hei, hil, hrest⟩ := h
    simp only [gapKinds, List.length_append, List.length_replicate, List.length_cons,
      ih (i + 1) L hrest (by omega)]
    omega

/-- Present positions, counted from `e`. -/
def presentFrom : List Bool → Nat → List Nat
  | [], _ => []
  | false :: ks, e => e :: presentFrom ks (e + 1)
  | true :: ks, e => presentFrom ks (e + 1)

theorem presentFrom_holes (m : Nat) (ks : List Bool) (e : Nat) :
    presentFrom (List.replicate m true ++ ks) e = presentFrom ks (e + m) := by
  induction m generalizing e with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append]
    simp only [presentFrom, ih]
    congr 1; omega

theorem presentFrom_gap :
    ∀ (is : List Nat) (e L : Nat), Ascending is e L → presentFrom (gapKinds is e L) e = is := by
  intro is
  induction is with
  | nil =>
    intro e L _
    simpa [gapKinds] using presentFrom_holes (L - e) [] e
  | cons i is ih =>
    intro e L h
    obtain ⟨hei, _, hrest⟩ := h
    simp only [gapKinds, presentFrom_holes, presentFrom, show e + (i - e) = i by omega,
      ih (i + 1) L hrest]

theorem presentFrom_ge :
    ∀ (ks : List Bool) (e j : Nat), j ∈ presentFrom ks e → e ≤ j := by
  intro ks
  induction ks with
  | nil => intro e j h; simp [presentFrom] at h
  | cons k ks ih =>
    intro e j h
    cases k with
    | false =>
      simp only [presentFrom, List.mem_cons] at h
      rcases h with rfl | h
      · exact Nat.le_refl _
      · have := ih (e + 1) j h; omega
    | true =>
      have := ih (e + 1) j h; omega

/-- Present positions determine the presence kinds of a fixed length. -/
theorem gap_presentFrom :
    ∀ (ks : List Bool) (e : Nat), gapKinds (presentFrom ks e) e (e + ks.length) = ks := by
  intro ks
  induction ks with
  | nil => intro e; simp [presentFrom, gapKinds]
  | cons k ks ih =>
    intro e
    have hl : e + (k :: ks).length = e + 1 + ks.length := by simp; omega
    cases k with
    | false =>
      simp only [presentFrom, gapKinds, Nat.sub_self, List.replicate_zero, List.nil_append]
      rw [hl, ih]
    | true =>
      simp only [presentFrom]
      rw [hl]
      have hih := ih (e + 1)
      cases hp : presentFrom ks (e + 1) with
      | nil =>
        rw [hp] at hih
        simp only [gapKinds] at hih ⊢
        rw [show e + 1 + ks.length - e = (e + 1 + ks.length - (e + 1)) + 1 by omega,
          List.replicate_succ, hih]
      | cons i is =>
        have hi : e + 1 ≤ i := presentFrom_ge ks (e + 1) i (by rw [hp]; simp)
        rw [hp] at hih
        simp only [gapKinds] at hih ⊢
        rw [show i - e = (i - (e + 1)) + 1 by omega, List.replicate_succ, List.cons_append, hih]

/-- Encoder/decoder agreement for a sparse array: the decoder expands the presence runs over
the array length and recovers exactly the present indices. -/
theorem sparse_roundtrip (is : List Nat) (L : Nat) (h : Ascending is 0 L) :
    kindsOf (presenceRuns is L) L = some (gapKinds is 0 L) ∧
      presentFrom (gapKinds is 0 L) 0 = is := by
  have hlen := gapKinds_length is 0 L h (Nat.zero_le _)
  refine ⟨?_, presentFrom_gap is 0 L h⟩
  have := kinds_runs (gapKinds is 0 L)
  rw [hlen, Nat.sub_zero] at this
  simpa [presenceRuns, presenceGo_runs is 0 0 L h, runsOf] using this

/-- Canonicity for a sparse array: accepted presence runs are the encoder's runs for the
positions they place. -/
theorem sparse_canonical {rs : List Nat} {L : Nat} {ks : List Bool}
    (h : kindsOf rs L = some ks) :
    gapKinds (presentFrom ks 0) 0 L = ks ∧ rs = runsOf ks := by
  have hl : ks.length = L := kindsGo_length rs true false L ks h
  refine ⟨?_, (runs_kinds h).symm⟩
  simpa [hl] using gap_presentFrom ks 0

theorem runsGo_nil_iff :
    ∀ (ks : List Bool) (c : Nat), runsGo ks false c = [] ↔ true ∉ ks := by
  intro ks
  induction ks with
  | nil => simp [runsGo]
  | cons k ks ih =>
    intro c
    cases k <;> simp [runsGo, ih]

/-- A sparse array is canonical only with a hole: its runs are empty exactly when every listed
position is present, which is the dense encoding. -/
theorem runsOf_nil_iff (ks : List Bool) : runsOf ks = [] ↔ true ∉ ks := runsGo_nil_iff ks 0

/-! ## Executable witnesses -/

example : runsOf [] = [] := rfl
example : runsOf [true, true] = [0] := rfl
example : runsOf [false, false, true] = [2] := rfl
example : runsOf [true, false] = [0, 1] := rfl
example : kindsOf [1, 1] 2 = none := rfl          -- open last run must be nonempty
example : kindsOf [2, 0, 1] 4 = none := rfl       -- only the first run may be empty
example : kindsOf [0] 0 = none := rfl
example : kindsOf [] 3 = some [false, false, false] := rfl
example : kindsOf [0, 2] 5 = some [true, true, false, false, false] := rfl
example : firstUse 0 [0, 0, 1, 0, 2, 1] = some 3 := rfl
example : firstUse 0 [0, 2] = none := rfl
example : internAll ([] : List Nat) [5, 5, 7, 5, 9] = ([0, 0, 1, 0, 2], [5, 7, 9]) := rfl
example : presenceRuns [2, 5] 9 = [0, 2, 1, 2, 1] := rfl     -- holes 0-1, 3-4, 6-8 open
example : presenceRuns [0, 1] 2 = [] := rfl                   -- dense: no runs
example : presenceRuns [] 3 = [0] := rfl                      -- all holes
example : kindsOf [0, 2, 1, 2, 1] 9 = some (gapKinds [2, 5] 0 9) := rfl

#print axioms kinds_runs
#print axioms runs_kinds
#print axioms kindsGo_length
#print axioms decode_encode_slots
#print axioms encode_decode_slots
#print axioms canonical_intern
#print axioms intern_canonical
#print axioms decode_encode_document
#print axioms encode_decode_document
#print axioms typedRef_sound
#print axioms renumber_first_use
#print axioms sparse_roundtrip
#print axioms sparse_canonical
#print axioms runsOf_nil_iff
#print axioms decode_encode_relaxed
#print axioms decode_encode_control
#print axioms encode_decode_control
#print axioms frame_unframe

end SerializationPositional
