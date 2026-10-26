import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Logic.Relation
import Serialization.Collection
import Serialization.Preorder

/-!
# Decoded size

`deserialize` limits the size of the value it returns. Size is counted in 64-bit words: the
words needed to hold the value when every object is stored once and every primitive is
stored where it occurs. ECMAScript gives objects identity and primitives none, so sharing is
charged once for objects and at every occurrence for strings and bigints; a property key is a
string, so it is charged with every property.

This module proves the finite facts the runtime's accounting relies on:

* `accounting_eq_reachable`: every node the runtime charges is reachable from the root along the
  document's references and links, because the `Preorder` check makes every node reachable, so
  the accounting charges no unreachable node. That each node decodes to at most one new object
  whose words its charges cover, with equality for the encoder's documents, is a runtime
  obligation: a folded `Map` or `Set`, a repeated shape key or a caller-aliased payload keeps
  fewer occurrences than it was charged, so the value can be smaller than the accounting.
* `node_count_le_accounting`: a document has at most as many nodes as words, so a node count
  above the limit can be rejected before any table is allocated.
* `stops_iff`: stopping at the first running total above the limit rejects exactly the
  documents whose total is above it. `accepts_iff_bytes`: in bytes, eight per charged word is
  the smallest accepted limit. That `requiredMaxBytes` returns it is checked by the bridge, not
  proved.
* `image_sum_le`, `foldMap_length_le` and `firstOrder_length_le`: when nodes share an object, or
  repeated `Map` keys or `Set` members fold, the decoded objects and entries are no more than
  the ones charged. They bound counts; that the entries kept are among the occurrences charged,
  so their payload words are covered too, is a runtime obligation.
* `json_words_le_text`: a JSON value's size in words is at most the length of its JSON text,
  so a limit of eight bytes per character accepts every JSON value whose text has that length.
  It bounds the value, not the document that encodes it: a short document can declare a long
  sparse array.
* `decodeInt_encodeInt`, `encodeInt_decodeInt`: hexadecimal bigint text is canonical.

Which words a node is charged (its header, slots and contents) is the runtime's table; the
theorems hold for any charges with the stated premises.
-/

namespace SerializationSize

open SerializationDFS SerializationPreorder SerializationCollection

/-! ## Reachability -/

/-- `v` is reachable from `root` along the document's references and internal links. -/
def Reach (c : Graph) (root v : Nat) : Prop := Relation.ReflTransGen (fun u w => w ∈ c u) root v

/-- What a traversal frame can reach: a visited node, or any remaining child of a parent. -/
def frameReach (c : Graph) : Frame → Nat → Prop
  | .visit node, x => Reach c node x
  | .resume _ _ children, x => ∃ y ∈ children, Reach c y x

/-- Every node a depth-first traversal enters is reachable from where the traversal started. -/
theorem entered_reach {c : Graph} {frame : Frame} {memo final : List Nat} {trace : List Event}
    (h : Recursive c frame memo trace final) : ∀ x ∈ entered trace, frameReach c frame x := by
  induction h with
  | seen => intro x hx; simp [entered] at hx
  | @fresh node memo trace final _ _ ih =>
    intro x hx
    simp only [entered, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Relation.ReflTransGen.refl
    · obtain ⟨y, hy, hr⟩ := ih x hx
      exact Relation.ReflTransGen.head hy hr
  | empty => intro x hx; simp [entered] at hx
  | child _ _ ih₁ ih₂ =>
    intro x hx
    simp only [entered, entered_append, List.mem_append] at hx
    rcases hx with hx | hx
    · exact ⟨_, List.mem_cons_self .., ih₁ x hx⟩
    · obtain ⟨y, hy, hr⟩ := ih₂ x hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hr⟩

/-- A document the runtime accepts has every node reachable from node 0. -/
theorem check_reach {c : Graph} {n : Nat} (h : check c n = true) : ∀ v < n, Reach c 0 v := by
  obtain ⟨trace, _, hrec, hen⟩ := (check_iff c n).1 h
  intro v hv
  exact entered_reach hrec v (by rw [hen]; simpa using hv)

/-- References and links name nodes of the document. -/
def Closed (c : Graph) (n : Nat) : Prop := ∀ v < n, ∀ r ∈ c v, r < n

theorem reach_lt {c : Graph} {n v : Nat} (hc : Closed c n) (hn : 0 < n) (h : Reach c 0 v) :
    v < n := by
  induction h with
  | refl => exact hn
  | tail _ hstep ih => exact hc _ ih _ hstep

/-! ## Size and its accounting -/

/-- Charges in words. `own v`: the header, slots and contents of node `v` when it is an
object, 0 for a primitive node. `lit v`: the words of the primitives written in `v`'s literal
slots. `occ v`: the words of one occurrence of primitive node `v` (a bigint), 0 otherwise. -/
structure Charges where
  own : Nat → Nat
  lit : Nat → Nat
  occ : Nat → Nat

/-- A node's words: its own, its literals', and one occurrence of every node it references. -/
def nodeWords (c : Graph) (w : Charges) (v : Nat) : Nat :=
  w.own v + w.lit v + ((c v).map w.occ).sum

/-- The objects reachable from the root, as nodes of the document. -/
noncomputable def reachable (c : Graph) (n : Nat) : Finset Nat :=
  open Classical in (Finset.range n).filter (Reach c 0)

/-- The root slot and its occurrence, then every node reachable from the root once. -/
noncomputable def reachableWords (c : Graph) (n : Nat) (w : Charges) : Nat :=
  1 + w.occ 0 + ∑ v ∈ reachable c n, nodeWords c w v

/-- The runtime's accounting: every node of the document once. -/
def accounting (c : Graph) (n : Nat) (w : Charges) : Nat :=
  1 + w.occ 0 + ∑ v ∈ Finset.range n, nodeWords c w v

theorem reachable_eq {c : Graph} {n : Nat} (h : check c n = true) :
    reachable c n = Finset.range n := by
  classical
  ext v
  simp only [reachable, Finset.mem_filter, Finset.mem_range, and_iff_left_iff_imp]
  exact check_reach h v

/-- On an accepted document, charging every node is charging every reachable node. -/
theorem accounting_eq_reachable {c : Graph} {n : Nat} (w : Charges) (h : check c n = true) :
    accounting c n w = reachableWords c n w := by
  rw [accounting, reachableWords, reachable_eq h]

/-- Every node except the root is a child of some node: it was reached along a reference or
link. -/
theorem nonroot_child {c : Graph} {n : Nat} (h : check c n = true) (hc : Closed c n) :
    ∀ v < n, v ≠ 0 → ∃ u < n, v ∈ c u := by
  intro v hv hv0
  have hn : 0 < n := by omega
  rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (check_reach h v hv) with h0 | ⟨u, hu, hstep⟩
  · exact absurd h0 hv0
  · exact ⟨u, reach_lt hc hn hu, hstep⟩

/-- When every node is charged at least one word per child (a slot per reference, a header
per link), a document has at most as many nodes as words. The runtime rejects a document
whose node count exceeds the limit before allocating its tables. -/
theorem node_count_le_accounting {c : Graph} {n : Nat} (w : Charges) (h : check c n = true)
    (hc : Closed c n) (hown : ∀ v, (c v).length ≤ w.own v) : n ≤ accounting c n w := by
  classical
  have hsub : (Finset.range n).erase 0 ⊆ (Finset.range n).biUnion (fun u => (c u).toFinset) := by
    intro v hv
    simp only [Finset.mem_erase, Finset.mem_range] at hv
    obtain ⟨u, hu, hvu⟩ := nonroot_child h hc v hv.2 hv.1
    exact Finset.mem_biUnion.2 ⟨u, Finset.mem_range.2 hu, List.mem_toFinset.2 hvu⟩
  have hcard : n - 1 ≤ ∑ u ∈ Finset.range n, (c u).length := by
    calc n - 1 = ((Finset.range n).erase 0).card := by
            by_cases hn : 0 < n
            · rw [Finset.card_erase_of_mem (Finset.mem_range.2 hn), Finset.card_range]
            · simp [show n = 0 by omega]
      _ ≤ ((Finset.range n).biUnion (fun u => (c u).toFinset)).card := Finset.card_le_card hsub
      _ ≤ ∑ u ∈ Finset.range n, (c u).toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ u ∈ Finset.range n, (c u).length :=
            Finset.sum_le_sum fun u _ => List.toFinset_card_le _
  have hwords : ∑ u ∈ Finset.range n, (c u).length ≤ ∑ u ∈ Finset.range n, nodeWords c w u := by
    exact Finset.sum_le_sum fun u _ => by unfold nodeWords; have := hown u; omega
  unfold accounting
  omega

/-! ## Inputs the encoder never writes -/

/-- When distinct nodes decode to one object, charging every node still covers the objects:
the sum over the decoded objects is at most the sum over the nodes. -/
theorem image_sum_le {α : Type} [DecidableEq α] (s : Finset Nat) (f : Nat → α) (cost : α → Nat)
    (nodeCost : Nat → Nat) (h : ∀ v ∈ s, cost (f v) ≤ nodeCost v) :
    ∑ o ∈ s.image f, cost o ≤ ∑ v ∈ s, nodeCost v :=
  (Finset.sum_image_le_of_nonneg fun _ _ => Nat.zero_le _).trans (Finset.sum_le_sum h)

variable {K V : Type} [DecidableEq K]

theorem put_length_le (key : K) (value : V) (rows : List (K × V)) :
    (put key value rows).length ≤ rows.length + 1 := by
  induction rows with
  | nil => simp [put]
  | cons pair rest ih =>
    rcases pair with ⟨first, old⟩
    by_cases h : key = first <;> simp [put, h, ih]

/-- A Map built from repeated keys has at most as many entries as pairs were charged. -/
theorem foldMap_length_le (rows entries : List (K × V)) :
    (foldMap rows entries).length ≤ rows.length + entries.length := by
  induction entries generalizing rows with
  | nil => simp [foldMap]
  | cons pair rest ih =>
    simp only [foldMap, List.foldl_cons, List.length_cons] at *
    have := ih (put pair.1 pair.2 rows)
    have := put_length_le pair.1 pair.2 rows
    omega

theorem remember_length_le (key : K) (keys : List K) :
    (remember key keys).length ≤ keys.length + 1 := by
  induction keys with
  | nil => simp [remember]
  | cons first rest ih => by_cases h : key = first <;> simp [remember, h, ih]

/-- A Set built from repeated members has at most as many members as were charged. -/
theorem firstOrder_length_le (keys incoming : List K) :
    (firstOrder keys incoming).length ≤ keys.length + incoming.length := by
  induction incoming generalizing keys with
  | nil => simp [firstOrder]
  | cons key rest ih =>
    simp only [firstOrder, List.foldl_cons, List.length_cons] at *
    have := ih (remember key keys)
    have := remember_length_le key keys
    omega

/-! ## Stopping early -/

/-- The runtime's check: add each charge to the running total and stop at the first total
above the limit. -/
def stops (limit : Nat) : Nat → List Nat → Bool
  | _, [] => false
  | total, charge :: rest => if limit < total + charge then true else stops limit (total + charge) rest

/-- Charges are never negative, so from a total within the limit, stopping early rejects
exactly the totals above the limit. -/
theorem stops_iff (limit : Nat) :
    ∀ (charges : List Nat) (total : Nat), total ≤ limit →
      (stops limit total charges = true ↔ limit < total + charges.sum) := by
  intro charges
  induction charges with
  | nil =>
    intro total h
    simp only [stops, List.sum_nil, Bool.false_eq_true, false_iff, Nat.add_zero, Nat.not_lt]
    exact h
  | cons charge rest ih =>
    intro total h
    simp only [stops, List.sum_cons]
    split
    · simp only [true_iff]; omega
    · rw [ih (total + charge) (by omega)]; omega

/-- A limit of `m` bytes allows `m / 8` words, so the charges of a document are accepted
exactly when `m` is at least eight bytes per charged word: `8 * charges.sum` is the smallest
accepted limit. -/
theorem accepts_iff_bytes (m : Nat) (charges : List Nat) :
    stops (m / 8) 0 charges = false ↔ 8 * charges.sum ≤ m := by
  have h := stops_iff (m / 8) charges 0 (Nat.zero_le _)
  rw [Nat.zero_add] at h
  rw [Nat.mul_comm, ← Nat.le_div_iff_mul_le (by decide)]
  cases hs : stops (m / 8) 0 charges <;> simp only [hs, true_iff, Bool.false_eq_true, false_iff,
    Nat.not_lt, Bool.true_eq_false] at h ⊢ <;> omega

/-! ## JSON values -/

/-- A JSON value, with each string or key given by its length in UTF-16 code units. -/
inductive Json where
  | null
  | bool (value : Bool)
  | num
  | str (length : Nat)
  | arr (items : List Json)
  | obj (members : List (Nat × Json))

/-- Words of a string payload: four 16-bit code units per word. -/
def stringWords (length : Nat) : Nat := (length + 3) / 4

mutual
/-- The words of a JSON value below its slot: a string's payload, or an object's header,
slots and contents. A number, boolean or null fits its slot. -/
def words : Json → Nat
  | .str length => stringWords length
  | .arr items => 1 + itemWords items
  | .obj members => 1 + memberWords members
  | _ => 0
/-- Each element: its slot and its words. -/
def itemWords : List Json → Nat
  | [] => 0
  | item :: rest => 1 + words item + itemWords rest
/-- Each property: a key slot, a value slot, the key's payload and the value's words. -/
def memberWords : List (Nat × Json) → Nat
  | [] => 0
  | (key, value) :: rest => 2 + stringWords key + words value + memberWords rest
end

mutual
/-- A lower bound on the length of the value's JSON text. Escapes only lengthen a string,
and a number takes at least one character. -/
def text : Json → Nat
  | .null => 4
  | .bool true => 4
  | .bool false => 5
  | .num => 1
  | .str length => length + 2
  | .arr items => 2 + itemText items + (items.length - 1)
  | .obj members => 2 + memberText members + (members.length - 1)
def itemText : List Json → Nat
  | [] => 0
  | item :: rest => text item + itemText rest
/-- `"key":value`: the key, two quotes, a colon and the value. -/
def memberText : List (Nat × Json) → Nat
  | [] => 0
  | (key, value) :: rest => key + 3 + text value + memberText rest
end

mutual
theorem words_lt_text : ∀ value : Json, 1 + words value ≤ text value
  | .null => by simp [words, text]
  | .bool true => by simp [words, text]
  | .bool false => by simp [words, text]
  | .num => by simp [words, text]
  | .str length => by simp only [words, text, stringWords]; omega
  | .arr items => by have := itemWords_le_text items; simp only [words, text]; omega
  | .obj members => by have := memberWords_le_text members; simp only [words, text]; omega
theorem itemWords_le_text : ∀ items : List Json, itemWords items ≤ itemText items
  | [] => by simp [itemWords, itemText]
  | item :: rest => by
    have := words_lt_text item
    have := itemWords_le_text rest
    simp only [itemWords, itemText]; omega
theorem memberWords_le_text : ∀ members : List (Nat × Json), memberWords members ≤ memberText members
  | [] => by simp [memberWords, memberText]
  | (key, value) :: rest => by
    have := words_lt_text value
    have := memberWords_le_text rest
    simp only [memberWords, memberText, stringWords]; omega
end

/-- A JSON value's size (its root slot and its words) is at most its JSON text length, so a
limit of eight bytes per character of JSON text accepts it. -/
theorem json_words_le_text (value : Json) : 1 + words value ≤ text value := words_lt_text value

/-! ## Hexadecimal bigint text -/

/-- The digits of a magnitude, most significant first; zero is the single digit 0. -/
def hexDigits (m : Nat) : List Nat := if m = 0 then [0] else (Nat.digits 16 m).reverse

def ofHex (digits : List Nat) : Nat := Nat.ofDigits 16 digits.reverse

/-- Canonical digits: at least one, each below 16, and no leading zero except `0` itself. -/
def Canonical (digits : List Nat) : Prop :=
  digits ≠ [] ∧ (∀ d ∈ digits, d < 16) ∧ (digits.head? = some 0 → digits = [0])

theorem ofHex_hexDigits (m : Nat) : ofHex (hexDigits m) = m := by
  unfold hexDigits ofHex
  split
  · subst m; simp
  · simp [Nat.ofDigits_digits]

theorem hexDigits_ofHex (digits : List Nat) (h : Canonical digits) :
    hexDigits (ofHex digits) = digits := by
  obtain ⟨hne, hlt, hlead⟩ := h
  by_cases h0 : digits.head? = some 0
  · rw [hlead h0]; simp [hexDigits, ofHex]
  · have hlast : ∀ hr : digits.reverse ≠ [], digits.reverse.getLast hr ≠ 0 := by
      intro hr hl
      rw [List.getLast_reverse] at hl
      exact h0 (by rw [List.head?_eq_some_head hne, hl])
    have hd := Nat.digits_ofDigits 16 (by norm_num) _
      (fun d hd => hlt d (List.mem_reverse.1 hd)) hlast
    unfold hexDigits ofHex
    rw [if_neg]
    · rw [hd, List.reverse_reverse]
    · intro hz
      rw [hz, Nat.digits_zero] at hd
      exact hne (List.reverse_eq_nil_iff.1 hd.symm)

/-- A bigint as text: a sign, then the canonical digits of its magnitude; `-0` is not one. The
runtime writes it `0x…` or `-0x…`. -/
def encodeInt (z : Int) : Bool × List Nat := (decide (z < 0), hexDigits z.natAbs)

def decodeInt : Bool × List Nat → Int
  | (negative, digits) => if negative then -(ofHex digits : Int) else ofHex digits

def CanonicalInt (text : Bool × List Nat) : Prop :=
  Canonical text.2 ∧ (text.1 = true → ofHex text.2 ≠ 0)

theorem decodeInt_encodeInt (z : Int) : decodeInt (encodeInt z) = z := by
  simp only [decodeInt, encodeInt, ofHex_hexDigits, decide_eq_true_eq]
  split <;> omega

theorem encodeInt_decodeInt (text : Bool × List Nat) (h : CanonicalInt text) :
    encodeInt (decodeInt text) = text := by
  obtain ⟨negative, digits⟩ := text
  obtain ⟨hc, hneg⟩ := h
  cases negative
  · simp only [decodeInt, encodeInt, Bool.false_eq_true, if_false, Int.natAbs_natCast,
      hexDigits_ofHex digits hc]
    simp
  · have := hneg rfl
    dsimp only at this
    simp only [decodeInt, encodeInt, if_true, Int.natAbs_neg, Int.natAbs_natCast]
    rw [hexDigits_ofHex digits hc]
    simp only [Prod.mk.injEq, and_true, decide_eq_true_eq]
    omega

/-- A bigint occurrence's words: sixteen hexadecimal digits per 64-bit word. -/
def bigintWords (digits : List Nat) : Nat := (digits.length + 15) / 16

/-! ## Examples and counterexamples -/

/-- Root node 0 references primitive node 1 (a bigint) twice. -/
def sharedPrimitive : Graph := fun v => if v = 0 then [1, 1] else []

/-- The root is an array of two slots (header and slots: 3 words); the bigint takes 5 words. -/
def sharedCharges : Charges := ⟨fun v => if v = 0 then 3 else 0, fun _ => 0,
  fun v => if v = 1 then 5 else 0⟩

example : check sharedPrimitive 2 = true := by decide

/-- The bigint is charged at both occurrences: 1 + 0 + (3 + 5 + 5) + 0. -/
example : accounting sharedPrimitive 2 sharedCharges = 14 := by
  simp [accounting, Finset.sum_range_succ, nodeWords, sharedPrimitive, sharedCharges]

example : reachableWords sharedPrimitive 2 sharedCharges = 14 := by
  rw [← accounting_eq_reachable _ (by decide)]
  simp [accounting, Finset.sum_range_succ, nodeWords, sharedPrimitive, sharedCharges]

/-- Node 1 is unreachable: the check rejects the document, and the accounting would charge
the unreachable node, which `accounting_eq_reachable` needs the check to exclude. -/
def unreachable : Graph := fun _ => []

def unitCharges : Charges := ⟨fun _ => 1, fun _ => 0, fun _ => 0⟩

example : check unreachable 2 = false := by decide

example : accounting unreachable 2 unitCharges = 3 ∧
    reachableWords unreachable 2 unitCharges = 2 := by
  refine ⟨by simp [accounting, nodeWords, unreachable, unitCharges], ?_⟩
  have : reachable unreachable 2 = {0} := by
    classical
    ext v
    simp only [reachable, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h⟩
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 h with h | ⟨_, _, h⟩
      · exact h
      · simp [unreachable] at h
    · rintro rfl; exact ⟨by omega, Relation.ReflTransGen.refl⟩
  simp [reachableWords, this, nodeWords, unreachable, unitCharges]

/-- Without a word per child, a two-node chain charges fewer words than it has nodes:
`node_count_le_accounting` needs that premise. -/
def chain : Graph := fun v => if v = 0 then [1] else []

example : check chain 2 = true ∧ accounting chain 2 ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩ < 2 := by
  refine ⟨by decide, ?_⟩
  simp [accounting, nodeWords, chain]

/-- `[0]` meets the JSON bound exactly: three words, three characters. -/
example : 1 + words (.arr [.num]) = 3 ∧ text (.arr [.num]) = 3 := by
  simp [words, itemWords, text, itemText]

/-- Without a starting total within the limit, a run with no charges never stops, although
its total is already above the limit; `stops_iff` needs that premise. -/
example : stops 0 1 [] = false ∧ 0 < 1 + ([] : List Nat).sum := by decide

/-- One byte below eight per word is rejected: a two-word document needs sixteen bytes. -/
example : stops (15 / 8) 0 [1, 1] = true ∧ stops (16 / 8) 0 [1, 1] = false := by decide

example : hexDigits 255 = [15, 15] ∧ hexDigits 0 = [0] := by
  simp [hexDigits]

/-- `-0` is not canonical bigint text. -/
example : ¬ CanonicalInt (true, [0]) := by
  simp [CanonicalInt, ofHex]

end SerializationSize
