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
* decoding in place never overwrites a value before it is read: group `g` writes four bytes from
  `3g`, before the word of any later group and the final group's values (`writes_behind`,
  `final_after`).

Values are alphabet indices, with `pad` for `=`. That the alphabet maps index i to the i-th
character of `A–Z a–z 0–9 + /`, that `>>`, `&` and `|` on these nonnegative words agree with the
division, remainder and sum used here (the decoder's position fields are disjoint), that the ASCII
bytes decode to the same string, that `encodeInto` writes each ASCII code of the text as one byte,
that a code outside the alphabet sets the sign bit of the OR, and that `DataView` reads and writes
the little-endian words, are runtime obligations; the tests compare the runtime encoder with the
native `btoa` and the decoder with the `atob` path.
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

/-- Group `g` writes bytes `3g` to `3g + 3`, all before the word of any later group `g'`, which
starts at `4g'`. -/
theorem writes_behind {g g' : Nat} (h : g < g') : 3 * g + 3 < 4 * g' := by omega

/-- After `groups` whole groups, the writes end at `3 * groups`, before the final group's values,
which start at `4 * groups`; with no whole group, nothing was written. -/
theorem final_after (groups : Nat) (h : 0 < groups) : 3 * (groups - 1) + 3 < 4 * groups := by
  omega

example : decode (encode [77, 97, 110, 1, 2]) = [77, 97, 110, 1, 2] := by decide
example : decode [19, 22, 5, 46] = [77, 97, 110] := by decide

end SerializationBase64
