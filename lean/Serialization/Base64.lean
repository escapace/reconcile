import Mathlib.Data.List.Basic

/-!
# Table-driven base64 encoding

RFC 4648 §4 encodes each group of three bytes as four 6-bit values, high bits first; a final
group of one or two bytes is completed with zero bits, and the missing values become padding.
`sextets` states that definition bytewise. The runtime packs a group into one 24-bit word and
reads its four 6-bit fields by shifts and masks (`fields`), then maps each value through the
64-entry alphabet. This file proves:

* the word fields are the bytewise sextets whenever the two low bytes are bytes
  (`fields_sextets`);
* the runtime's loop over a byte list, including its one- and two-byte final groups, emits
  exactly the specification (`encode_spec`);
* the output has four values per started group (`encode_length`).

The table decoder (`decodeTable`) reads each group of four values as one little-endian word and
writes the group's three bytes as one. Each value contributes fixed bits at its position
(`position`), so the word's low three bytes are the bytes RFC 4648 decodes the group to
(`groupWord_bytes`). This file also proves:

* the decoder returns RFC 4648's bytes for any text of alphabet values with final padding
  (`decode_spec`), and the bytes the encoder started from (`decode_encode`);
* decoding in place over one buffer, as `decodeTable` does (`decodeInPlace`: group `g` reads the
  word at `4g` and writes four bytes from `3g`, then the final group reads two or three values at
  `4 * groups` and writes one or two bytes at `3 * groups`), never overwrites a value before it is
  read (`wholeGroups_memory`), and its first `decodedSize` bytes are `decode`'s and RFC 4648's
  (`decodeInPlace_eq`, `decode_in_place`).

Values are alphabet indices, with `pad` for `=`; the in-place model's buffer holds each code's
value, which the runtime's position tables look up from the code. That the alphabet maps index i
to the i-th character of `A–Z a–z 0–9 + /`, that `>>`, `&` and `|` on these nonnegative words
agree with the division, remainder and sum used here (the decoder's position fields are
disjoint), that the ASCII bytes decode to the same string, that `encodeInto` writes each ASCII
code of the text as one byte, that a code outside the alphabet sets the sign bit of the OR, that
`DataView` reads and writes the little-endian words, that a `Uint8Array` store keeps a word's low
byte, and that `transfer` keeps the buffer's first bytes, are runtime obligations; the tests
compare the runtime encoder with the native `btoa` and the decoder with the `atob` path.
-/

namespace SerializationBase64

/-- The padding value, outside the alphabet's indices. -/
def pad : Nat := 64

/-- RFC 4648: the four 6-bit values of bytes `a b c`, high bits first. -/
def sextets (a b c : Nat) : List Nat :=
  [a / 4, a % 4 * 16 + b / 16, b % 16 * 4 + c / 64, c % 64]

/-- The specification: whole groups, then a final group completed with zero bits. -/
def spec : List Nat → List Nat
  | a :: b :: c :: rest => sextets a b c ++ spec rest
  | [a, b] => (sextets a b 0).take 3 ++ [pad]
  | [a] => (sextets a 0 0).take 2 ++ [pad, pad]
  | [] => []

/-- The runtime's packed group and its four fields. -/
def word (a b c : Nat) : Nat := a * 65536 + b * 256 + c

def fields (v : Nat) : List Nat := [v / 262144, v / 4096 % 64, v / 64 % 64, v % 64]

theorem fields_sextets {a b c : Nat} (hb : b < 256) (hc : c < 256) :
    fields (word a b c) = sextets a b c := by
  simp only [fields, sextets, word, List.cons.injEq, and_true]
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- The runtime loop: whole groups from packed words; a final group of two bytes keeps three
fields, of one byte two, each followed by padding. -/
def encode : List Nat → List Nat
  | a :: b :: c :: rest => fields (word a b c) ++ encode rest
  | [a, b] => (fields (word a b 0)).take 3 ++ [pad]
  | [a] => (fields (word a 0 0)).take 2 ++ [pad, pad]
  | [] => []

theorem encode_spec : ∀ bytes : List Nat, (∀ x ∈ bytes, x < 256) → encode bytes = spec bytes
  | a :: b :: c :: rest, h => by
    simp only [encode, spec]
    rw [fields_sextets (h b (by simp)) (h c (by simp)),
      encode_spec rest (fun x hx => h x (by simp [hx]))]
  | [a, b], h => by
    simp only [encode, spec]
    rw [fields_sextets (h b (by simp)) (by omega)]
  | [a], h => by
    simp only [encode, spec]
    rw [fields_sextets (by omega) (by omega)]
  | [], _ => rfl

theorem encode_length : ∀ bytes : List Nat, (encode bytes).length = 4 * ((bytes.length + 2) / 3)
  | _ :: _ :: _ :: rest => by
    have := encode_length rest
    simp only [encode, List.length_append, fields, List.length_cons, List.length_nil] at this ⊢
    omega
  | [_, _] => by simp [encode, fields]
  | [_] => by simp [encode, fields]
  | [] => rfl

example : encode [77, 97, 110] = [19, 22, 5, 46] := by decide
example : encode [77, 97] = [19, 22, 4, pad] := by decide
example : encode [77] = [19, 16, pad, pad] := by decide

/-! ## Table decoding -/

/-- The bits that value `v` contributes at position `k` of a group of four, little-endian: the
group's first byte in the low eight bits. -/
def position (k v : Nat) : Nat :=
  match k with
  | 0 => v * 4
  | 1 => v / 16 + v % 16 * 4096
  | 2 => v / 4 * 256 + v % 4 * 4194304
  | _ => v * 65536

/-- A group's word: the sum (the runtime's OR) of its four positions' bits. -/
def groupWord (v0 v1 v2 v3 : Nat) : Nat :=
  position 0 v0 + position 1 v1 + position 2 v2 + position 3 v3

/-- The low three bytes of a little-endian word, in memory order. -/
def leBytes (w : Nat) : List Nat := [w % 256, w / 256 % 256, w / 65536 % 256]

/-- RFC 4648: the three bytes whose sextets are `v0 v1 v2 v3`. -/
def unsextets (v0 v1 v2 v3 : Nat) : List Nat :=
  [v0 * 4 + v1 / 16, v1 % 16 * 16 + v2 / 4, v2 % 4 * 64 + v3]

/-- A sum of three bytes in base 256 reads back as those bytes. -/
private theorem base256 {x y z : Nat} (hx : x < 256) (hy : y < 256) (hz : z < 256) :
    leBytes (x + 256 * y + 65536 * z) = [x, y, z] := by
  simp only [leBytes, List.cons.injEq, and_true]
  refine ⟨by omega, by omega, by omega⟩

/-- The word's bytes are the group's RFC 4648 bytes. -/
theorem groupWord_bytes {v0 v1 v2 v3 : Nat} (h0 : v0 < 64) (h1 : v1 < 64) (h2 : v2 < 64)
    (h3 : v3 < 64) : leBytes (groupWord v0 v1 v2 v3) = unsextets v0 v1 v2 v3 := by
  have hw : groupWord v0 v1 v2 v3 =
      (v0 * 4 + v1 / 16) + 256 * (v1 % 16 * 16 + v2 / 4) + 65536 * (v2 % 4 * 64 + v3) := by
    simp only [groupWord, position]
    omega
  rw [hw, base256 (by omega) (by omega) (by omega)]
  rfl

/-- The runtime decoder over values: whole groups, then a final group of three values and a pad,
which keeps two bytes, or of two values and two pads, which keeps one. -/
def decode : List Nat → List Nat
  | [v0, v1, v2, v3] =>
    if v2 = pad then (leBytes (groupWord v0 v1 0 0)).take 1
    else if v3 = pad then (leBytes (groupWord v0 v1 v2 0)).take 2
    else leBytes (groupWord v0 v1 v2 v3)
  | v0 :: v1 :: v2 :: v3 :: rest => leBytes (groupWord v0 v1 v2 v3) ++ decode rest
  | _ => []

/-- RFC 4648 decoding, bytewise: whole groups, then the final group's one or two bytes. -/
def specDecode : List Nat → List Nat
  | [v0, v1, v2, v3] =>
    if v2 = pad then (unsextets v0 v1 0 0).take 1
    else if v3 = pad then (unsextets v0 v1 v2 0).take 2
    else unsextets v0 v1 v2 v3
  | v0 :: v1 :: v2 :: v3 :: rest => unsextets v0 v1 v2 v3 ++ specDecode rest
  | _ => []

/-- Text the decoder takes: groups of alphabet values, the last possibly ending in one or two
pads, which `decodedSize` counts. -/
def Valid : List Nat → Prop
  | [v0, v1, v2, v3] => v0 < 64 ∧ v1 < 64 ∧ (v2 < 64 ∨ (v2 = pad ∧ v3 = pad)) ∧ (v3 < 64 ∨ v3 = pad)
  | v0 :: v1 :: v2 :: v3 :: rest => v0 < 64 ∧ v1 < 64 ∧ v2 < 64 ∧ v3 < 64 ∧ rest ≠ [] ∧ Valid rest
  | _ => False

/-- On valid text the decoder returns RFC 4648's bytes. -/
theorem decode_spec : ∀ values : List Nat, Valid values → decode values = specDecode values
  | [v0, v1, v2, v3], h => by
    obtain ⟨h0, h1, h2, h3⟩ := h
    have z : (0 : Nat) < 64 := by decide
    simp only [decode, specDecode]
    by_cases hp2 : v2 = pad
    · simp only [hp2, if_true]
      rw [groupWord_bytes h0 h1 z z]
    · have h2' : v2 < 64 := by
        rcases h2 with h2 | ⟨h2, _⟩
        · exact h2
        · exact absurd h2 hp2
      simp only [hp2, if_false]
      by_cases hp3 : v3 = pad
      · simp only [hp3, if_true]
        rw [groupWord_bytes h0 h1 h2' z]
      · have h3' : v3 < 64 := by
          rcases h3 with h3 | h3
          · exact h3
          · exact absurd h3 hp3
        simp only [hp3, if_false]
        rw [groupWord_bytes h0 h1 h2' h3']
  | v0 :: v1 :: v2 :: v3 :: w :: rest, h => by
    obtain ⟨h0, h1, h2, h3, -, hrest⟩ := h
    simp only [decode, specDecode]
    rw [groupWord_bytes h0 h1 h2 h3, decode_spec (w :: rest) hrest]
  | [], h | [_], h | [_, _], h | [_, _, _], h => by simp [Valid] at h

/-- RFC 4648 decoding inverts the sextets of three bytes. -/
theorem unsextets_sextets {a b c : Nat} (hb : b < 256) (hc : c < 256) :
    unsextets (a / 4) (a % 4 * 16 + b / 16) (b % 16 * 4 + c / 64) (c % 64) = [a, b, c] := by
  simp only [unsextets, List.cons.injEq, and_true]
  refine ⟨by omega, by omega, by omega⟩

/-- The specification's output of a nonempty byte list starts with a whole group. -/
theorem spec_cons : ∀ bytes : List Nat, bytes ≠ [] →
    ∃ e0 e1 e2 e3 tail, spec bytes = e0 :: e1 :: e2 :: e3 :: tail
  | a :: b :: c :: rest, _ =>
    ⟨a / 4, a % 4 * 16 + b / 16, b % 16 * 4 + c / 64, c % 64, spec rest, by
      simp only [spec, sextets, List.cons_append, List.nil_append]⟩
  | [a, b], _ => ⟨a / 4, a % 4 * 16 + b / 16, b % 16 * 4 + 0 / 64, pad, [], rfl⟩
  | [a], _ => ⟨a / 4, a % 4 * 16 + 0 / 16, pad, pad, [], rfl⟩
  | [], h => absurd rfl h

/-- The specification's output of bytes is valid text. -/
theorem spec_valid : ∀ bytes : List Nat, bytes ≠ [] → (∀ x ∈ bytes, x < 256) → Valid (spec bytes)
  | [a, b, c], _, h => by
    have ha := h a (by simp); have hb := h b (by simp); have hc := h c (by simp)
    simp only [spec, sextets, List.cons_append, List.nil_append, Valid]
    omega
  | a :: b :: c :: d :: rest, _, h => by
    have ha := h a (by simp); have hb := h b (by simp); have hc := h c (by simp)
    have hrest := spec_valid (d :: rest) (by simp) (fun x hx => h x (by simp_all))
    obtain ⟨e0, e1, e2, e3, tail, htail⟩ := spec_cons (d :: rest) (by simp)
    simp only [spec, sextets, List.cons_append, List.nil_append]
    rw [htail] at hrest ⊢
    exact ⟨by omega, by omega, by omega, by omega, by simp, hrest⟩
  | [a, b], _, h => by
    have ha := h a (by simp); have hb := h b (by simp)
    simp only [spec, sextets, List.take, List.cons_append, List.nil_append, Valid]
    exact ⟨by omega, by omega, Or.inl (by omega), Or.inr trivial⟩
  | [a], _, h => by
    have ha := h a (by simp)
    simp only [spec, sextets, List.take, List.cons_append, List.nil_append, Valid]
    exact ⟨by omega, by omega, Or.inr ⟨trivial, trivial⟩, Or.inr trivial⟩
  | [], h, _ => absurd rfl h

/-- RFC 4648 decoding of the specification's output returns the bytes. -/
theorem specDecode_spec : ∀ bytes : List Nat, (∀ x ∈ bytes, x < 256) → specDecode (spec bytes) = bytes
  | [a, b, c], h => by
    have ha := h a (by simp); have hb := h b (by simp); have hc := h c (by simp)
    simp only [spec, sextets, List.append_nil, specDecode, pad,
      show ¬b % 16 * 4 + c / 64 = 64 by omega, show ¬c % 64 = 64 by omega, if_false]
    exact unsextets_sextets hb hc
  | a :: b :: c :: d :: rest, h => by
    have ha := h a (by simp); have hb := h b (by simp); have hc := h c (by simp)
    have hrest := specDecode_spec (d :: rest) (fun x hx => h x (by simp_all))
    obtain ⟨e0, e1, e2, e3, tail, htail⟩ := spec_cons (d :: rest) (by simp)
    simp only [spec, sextets, List.cons_append, List.nil_append]
    rw [htail] at hrest ⊢
    simp only [specDecode]
    rw [hrest, unsextets_sextets hb hc]
    rfl
  | [a, b], h => by
    have ha := h a (by simp); have hb := h b (by simp)
    simp only [spec, sextets, List.take, List.cons_append, List.nil_append, specDecode, pad,
      show ¬b % 16 * 4 + 0 / 64 = 64 by omega, if_false, if_true]
    rw [unsextets_sextets hb (by omega : (0 : Nat) < 256)]
    rfl
  | [a], h => by
    have ha := h a (by simp)
    simp only [spec, sextets, List.take, List.cons_append, List.nil_append, specDecode, pad, if_true]
    rw [show (0 : Nat) = 0 / 64 from rfl, show a % 4 * 16 = a % 4 * 16 + 0 / 16 by omega,
      unsextets_sextets (by omega : (0 : Nat) < 256) (by omega : (0 : Nat) < 256)]
    rfl
  | [], _ => rfl

/-- Decoding the encoder's output returns the bytes it encoded. -/
theorem decode_encode (bytes : List Nat) (h : ∀ x ∈ bytes, x < 256) :
    decode (encode bytes) = bytes := by
  rw [encode_spec bytes h]
  by_cases hb : bytes = []
  · subst hb; rfl
  · rw [decode_spec _ (spec_valid bytes hb h), specDecode_spec bytes h]

example : decode (encode [77, 97, 110, 1, 2]) = [77, 97, 110, 1, 2] := by decide
example : decode [19, 22, 5, 46] = [77, 97, 110] := by decide

/-! ## Decoding in place -/

/-- The decoder's buffer: byte offset ↦ byte. It starts as the text's values, one per byte. -/
abbrev Memory := Nat → Nat

/-- `bytes` stored from `offset`; every other byte is left as it was. -/
def store (memory : Memory) (offset : Nat) (bytes : List Nat) : Memory :=
  fun i => if offset ≤ i ∧ i < offset + bytes.length then bytes.getD (i - offset) 0 else memory i

/-- `getInt32(4 * group, true)` as the tables read it: the word of the four values from
`4 * group`. -/
def readWord (memory : Memory) (group : Nat) : Nat :=
  groupWord (memory (4 * group)) (memory (4 * group + 1)) (memory (4 * group + 2))
    (memory (4 * group + 3))

/-- `setInt32(3 * group, word, true)`: the word's four little-endian bytes. -/
def int32Bytes (w : Nat) : List Nat := leBytes w ++ [w / 16777216 % 256]

theorem int32Bytes_getD (w j : Nat) (hj : j < 3) :
    (int32Bytes w).getD j 0 = (leBytes w).getD j 0 := by
  simp only [int32Bytes, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp [leBytes]; omega)]

/-- One iteration of the loop over whole groups. -/
def wholeStep (memory : Memory) (group : Nat) : Memory :=
  store memory (3 * group) (int32Bytes (readWord memory group))

/-- The word of the final group of `rest` bytes after `groups` whole ones: its two or three
values, read from `4 * groups`. -/
def finalWord (memory : Memory) (groups rest : Nat) : Nat :=
  position 0 (memory (4 * groups)) + position 1 (memory (4 * groups + 1)) +
    (if rest = 2 then position 2 (memory (4 * groups + 2)) else 0)

/-- The final group: its one or two bytes, written from `3 * groups`. -/
def finalStep (memory : Memory) (groups rest : Nat) : Memory :=
  if rest = 0 then memory
  else store memory (3 * groups) ((leBytes (finalWord memory groups rest)).take rest)

/-- `decodeTable`: the text's values decoded in place in one buffer; its first `length` bytes. -/
def decodeInPlace (values : List Nat) (length : Nat) : List Nat :=
  let groups := length / 3
  let memory := finalStep ((List.range groups).foldl wholeStep (values.getD · 0)) groups
    (length - 3 * groups)
  (List.range length).map memory

/-- The byte count `decodedSize` predicts: three per group of four values, less one per final
pad. -/
def decodedSize (values : List Nat) : Nat :=
  values.length / 4 * 3 -
    match values.reverse with
    | v :: w :: _ => if v = pad then (if w = pad then 2 else 1) else 0
    | _ => 0

/-- No write reaches a value still to be read: after `k` whole groups, every byte from `4k` on
is still the text's value, and the bytes before `3k` are the groups' decoded bytes. -/
theorem wholeGroups_memory (values : List Nat) (k : Nat) :
    (∀ i, 4 * k ≤ i → (List.range k).foldl wholeStep (values.getD · 0) i = values.getD i 0) ∧
    (∀ i, i < 3 * k → (List.range k).foldl wholeStep (values.getD · 0) i =
      (leBytes (readWord (values.getD · 0) (i / 3))).getD (i % 3) 0) := by
  induction k with
  | zero => exact ⟨fun _ _ => rfl, fun i h => absurd h (by omega)⟩
  | succ k ih =>
    obtain ⟨ahead, behind⟩ := ih
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range k).foldl wholeStep (values.getD · 0) = memory at ahead behind
    have hword : readWord memory k = readWord (values.getD · 0) k := by
      simp only [readWord]
      rw [ahead _ (by omega), ahead _ (by omega), ahead _ (by omega), ahead _ (by omega)]
    have hlen : (int32Bytes (readWord memory k)).length = 4 := by simp [int32Bytes, leBytes]
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · simp only [wholeStep, store, hlen]
      rw [if_neg (by omega)]
      exact ahead i (by omega)
    · simp only [wholeStep, store, hlen]
      by_cases hk : 3 * k ≤ i
      · rw [if_pos (by omega), hword, show i / 3 = k by omega, show i % 3 = i - 3 * k by omega]
        exact int32Bytes_getD _ _ (by omega)
      · rw [if_neg (by omega)]
        exact behind i (by omega)

/-- A text's tail after one group is read four values further on. -/
theorem readWord_cons (v0 v1 v2 v3 : Nat) (rest : List Nat) (g : Nat) :
    readWord ((v0 :: v1 :: v2 :: v3 :: rest).getD · 0) (g + 1) = readWord (rest.getD · 0) g := by
  have e : ∀ j, (v0 :: v1 :: v2 :: v3 :: rest).getD (4 * (g + 1) + j) 0 =
      rest.getD (4 * g + j) 0 := by
    intro j
    rw [show 4 * (g + 1) + j = 4 * g + j + 1 + 1 + 1 + 1 by omega]
    simp
  have e0 := e 0
  simp only [Nat.add_zero] at e0
  simp only [readWord]
  rw [e0, e 1, e 2, e 3]

/-- Valid text is whole groups, then a last group: its bytes are the whole groups' bytes, then
the last group's. -/
theorem decode_split : ∀ values : List Nat, Valid values →
    ∃ m, values.length = 4 * m + 4 ∧ Valid (values.drop (4 * m)) ∧
      (decode values).length = 3 * m + (decode (values.drop (4 * m))).length ∧
      ∀ i, (decode values).getD i 0 =
        if i < 3 * m then (leBytes (readWord (values.getD · 0) (i / 3))).getD (i % 3) 0
        else (decode (values.drop (4 * m))).getD (i - 3 * m) 0
  | [v0, v1, v2, v3], h => ⟨0, rfl, by simpa using h, by simp, fun i => by simp⟩
  | v0 :: v1 :: v2 :: v3 :: w :: rest, h => by
    obtain ⟨-, -, -, -, -, hrest⟩ := h
    obtain ⟨m, hlen, hvalid, hdl, hget⟩ := decode_split (w :: rest) hrest
    have hdrop : (v0 :: v1 :: v2 :: v3 :: w :: rest).drop (4 * (m + 1)) =
        (w :: rest).drop (4 * m) := by
      rw [show 4 * (m + 1) = 4 * m + 1 + 1 + 1 + 1 by omega]
      simp
    have hd : decode (v0 :: v1 :: v2 :: v3 :: w :: rest) =
        leBytes (groupWord v0 v1 v2 v3) ++ decode (w :: rest) := by
      simp only [decode]
    have hl3 : (leBytes (groupWord v0 v1 v2 v3)).length = 3 := by simp [leBytes]
    refine ⟨m + 1, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_cons] at hlen ⊢; omega
    · rw [hdrop]; exact hvalid
    · rw [hdrop, hd, List.length_append, hl3, hdl]; omega
    · intro i
      rw [hdrop, hd]
      simp only [List.getD_eq_getElem?_getD]
      by_cases hi : i < 3
      · rw [List.getElem?_append_left (by omega), if_pos (by omega),
          show i / 3 = 0 by omega, show i % 3 = i by omega]
        rfl
      · rw [List.getElem?_append_right (by omega), hl3]
        have := hget (i - 3)
        simp only [List.getD_eq_getElem?_getD] at this
        rw [this]
        by_cases hm : i - 3 < 3 * m
        · have hc := readWord_cons v0 v1 v2 v3 (w :: rest) ((i - 3) / 3)
          simp only [List.getD_eq_getElem?_getD] at hc
          rw [if_pos hm, if_pos (by omega), show i / 3 = (i - 3) / 3 + 1 by omega,
            show i % 3 = (i - 3) % 3 by omega, hc]
        · rw [if_neg hm, if_neg (by omega)]
          congr 2
          omega
  | [], h | [_], h | [_, _], h | [_, _, _], h => by simp [Valid] at h

/-- The last group of the text and the text's values there. -/
theorem last_group {values : List Nat} {m : Nat} (hlen : values.length = 4 * m + 4) :
    ∃ a b c d, values.drop (4 * m) = [a, b, c, d] ∧ values.getD (4 * m) 0 = a ∧
      values.getD (4 * m + 1) 0 = b ∧ values.getD (4 * m + 2) 0 = c ∧
      values.getD (4 * m + 3) 0 = d := by
  have hl : (values.drop (4 * m)).length = 4 := by simp [hlen]
  match hq : values.drop (4 * m), hl with
  | [a, b, c, d], _ =>
    have e : ∀ j, values.getD (4 * m + j) 0 = [a, b, c, d].getD j 0 := by
      intro j
      rw [← hq]
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
    exact ⟨a, b, c, d, rfl, by simpa using e 0, e 1, e 2, e 3⟩

/-- The final group's bytes, where it writes them. -/
theorem finalStep_at (memory : Memory) (m rest i : Nat) (hrest : rest = 1 ∨ rest = 2)
    (hi : 3 * m ≤ i) (hir : i < 3 * m + rest) :
    finalStep memory m rest i = (leBytes (finalWord memory m rest)).getD (i - 3 * m) 0 := by
  have h0 : rest ≠ 0 := by omega
  have hlen : ((leBytes (finalWord memory m rest)).take rest).length = rest := by
    simp [leBytes]; omega
  simp only [finalStep, h0, if_false, store, hlen, if_pos (And.intro hi hir)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
  rw [if_pos (by omega)]

/-- Before the final group's bytes, the final group changes nothing. -/
theorem finalStep_before (memory : Memory) (m rest i : Nat) (hi : i < 3 * m) :
    finalStep memory m rest i = memory i := by
  unfold finalStep
  split
  · rfl
  · rw [store, if_neg (by omega)]

/-- The runtime's decoder, run in place over one buffer, returns the bytes `decode` gives. -/
theorem decodeInPlace_eq (values : List Nat) (h : Valid values) :
    decodeInPlace values (decode values).length = decode values := by
  obtain ⟨m, hlen, hlast, hdl, hget⟩ := decode_split values h
  obtain ⟨a, b, c, d, hq, ha, hb, hc, hd⟩ := last_group hlen
  rw [hq] at hlast hdl hget
  obtain ⟨_, _, h2, h3⟩ := hlast
  apply List.ext_getElem (by simp [decodeInPlace])
  intro i _ hi
  have hgetD : (decode values)[i] = (decode values).getD i 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp only [decodeInPlace, List.getElem_map, List.getElem_range]
  rw [hgetD, hget i]
  clear hgetD
  have hL := hdl
  generalize (decode values).length = L at hL hi ⊢
  obtain ⟨ahead, behind⟩ := wholeGroups_memory values m
  by_cases hp2 : c = pad
  · have hp3 : d = pad := by
      rcases h2 with h2 | ⟨_, h3⟩
      · simp [pad, hp2] at h2
      · exact h3
    have hdec : decode [a, b, c, d] = (leBytes (groupWord a b 0 0)).take 1 := by
      simp [decode, hp2]
    rw [hdec] at hL ⊢
    have hL' : L = 3 * m + 1 := by rw [hL]; simp [leBytes]
    subst hL'
    rw [show (3 * m + 1) / 3 = m by omega, show 3 * m + 1 - 3 * m = 1 by omega]
    by_cases hi3 : i < 3 * m
    · rw [if_pos hi3, finalStep_before _ _ _ _ hi3]
      exact behind i hi3
    · rw [if_neg hi3, finalStep_at _ _ _ _ (Or.inl rfl) (by omega) (by omega)]
      have hw : finalWord ((List.range m).foldl wholeStep (values.getD · 0)) m 1 =
          groupWord a b 0 0 := by
        simp only [finalWord, if_neg (show (1 : Nat) ≠ 2 by decide)]
        rw [ahead _ (by omega), ahead _ (by omega), ha, hb, groupWord,
          show position 2 0 = 0 from rfl, show position 3 0 = 0 from rfl]
      rw [hw, show i - 3 * m = 0 by omega]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
      rw [if_pos (by omega)]
  · have hc' : c < 64 := by
      rcases h2 with h2 | ⟨h2, _⟩
      · exact h2
      · exact absurd h2 hp2
    by_cases hp3 : d = pad
    · have hdec : decode [a, b, c, d] = (leBytes (groupWord a b c 0)).take 2 := by
        simp [decode, hp2, hp3]
      rw [hdec] at hL ⊢
      have hL' : L = 3 * m + 2 := by rw [hL]; simp [leBytes]
      subst hL'
      rw [show (3 * m + 2) / 3 = m by omega, show 3 * m + 2 - 3 * m = 2 by omega]
      by_cases hi3 : i < 3 * m
      · rw [if_pos hi3, finalStep_before _ _ _ _ hi3]
        exact behind i hi3
      · rw [if_neg hi3, finalStep_at _ _ _ _ (Or.inr rfl) (by omega) (by omega)]
        have hw : finalWord ((List.range m).foldl wholeStep (values.getD · 0)) m 2 =
            groupWord a b c 0 := by
          simp only [finalWord, if_true]
          rw [ahead _ (by omega), ahead _ (by omega), ahead _ (by omega), ha, hb, hc, groupWord,
            show position 3 0 = 0 from rfl, Nat.add_zero]
        rw [hw]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
        rw [if_pos (by omega)]
    · have hdec : decode [a, b, c, d] = leBytes (groupWord a b c d) := by
        simp [decode, hp2, hp3]
      rw [hdec] at hL ⊢
      have hL' : L = 3 * (m + 1) := by rw [hL]; simp [leBytes]; omega
      subst hL'
      rw [show 3 * (m + 1) / 3 = m + 1 by omega, show 3 * (m + 1) - 3 * (m + 1) = 0 by omega]
      obtain ⟨_, behind'⟩ := wholeGroups_memory values (m + 1)
      simp only [finalStep, if_true]
      rw [behind' i (by omega)]
      by_cases hi3 : i < 3 * m
      · rw [if_pos hi3]
      · have hword : readWord (values.getD · 0) m = groupWord a b c d := by
          simp only [readWord, ha, hb, hc, hd]
        rw [if_neg hi3, show i / 3 = m by omega, show i % 3 = i - 3 * m by omega, hword]

/-- On valid text `decodedSize` predicts the decoded length. -/
theorem decodedSize_eq (values : List Nat) (h : Valid values) :
    decodedSize values = (decode values).length := by
  obtain ⟨m, hlen, hlast, hdl, -⟩ := decode_split values h
  obtain ⟨a, b, c, d, hq, -, -, -, -⟩ := last_group hlen
  rw [hq] at hlast hdl
  have hv : values = values.take (4 * m) ++ [a, b, c, d] := by
    rw [← hq, List.take_append_drop]
  have hrev : values.reverse = d :: c :: b :: a :: (values.take (4 * m)).reverse := by
    conv_lhs => rw [hv]
    simp
  obtain ⟨_, _, h2, h3⟩ := hlast
  simp only [decodedSize, hrev, hlen, hdl]
  rw [show (4 * m + 4) / 4 * 3 = 3 * m + 3 by omega]
  by_cases hp2 : c = pad
  · have hp3 : d = pad := by
      rcases h2 with h2 | ⟨_, h3⟩
      · simp [pad, hp2] at h2
      · exact h3
    simp [decode, hp2, hp3, leBytes]
  · by_cases hp3 : d = pad
    · simp [decode, hp2, hp3, leBytes]
    · simp [decode, hp2, hp3, leBytes]

/-- `decodeTable` returns RFC 4648's bytes: decoding in place, for the length `decodedSize`
predicts, gives `specDecode`. -/
theorem decode_in_place (values : List Nat) (h : Valid values) :
    decodeInPlace values (decodedSize values) = specDecode values := by
  rw [decodedSize_eq values h, decodeInPlace_eq values h, decode_spec values h]

example : decodeInPlace (encode [77, 97, 110, 1, 2]) 5 = [77, 97, 110, 1, 2] := by decide
example : decodedSize [19, 22, 4, pad] = 2 := by decide

/-- Counterexample for the order: taking the groups last first, the second group's write
reaches the first group's last value before it is read, and the first group decodes wrong. -/
example : (List.range 6).map ([1, 0].foldl wholeStep ((encode [77, 97, 110, 1, 2, 3]).getD · 0)) ≠
    [77, 97, 110, 1, 2, 3] := by
  decide

end SerializationBase64
