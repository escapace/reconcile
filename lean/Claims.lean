import Execution
import Mathlib.Data.Nat.Bitwise

/- Private runtime claim masks use only bits 0–30. Native integer/range guards
   establish this domain before JavaScript bit operations. Other numeric labels
   use native Set membership; their identity fidelity is an adapter premise.
   This finite model proves membership and insertion, not JavaScript coercions. -/
namespace Reconcile.Claims

inductive Store where
  | compact (mask : Nat)
  | expanded (modes : Finset Nat)

def decode : Store → Finset Nat
  | .compact mask => (Finset.range 31).filter fun mode => mask.testBit mode
  | .expanded modes => modes

def valid : Store → Prop
  | .compact mask => mask < 2 ^ 31
  | .expanded _ => True

def has (store : Store) (mode : Nat) : Bool :=
  match store with
  | .compact mask => decide (mode < 31) && mask.testBit mode
  | .expanded modes => decide (mode ∈ modes)

def add (store : Store) (mode : Nat) : Store :=
  match store with
  | .compact mask => if mode < 31 then .compact (mask ||| 2 ^ mode)
    else .expanded (insert mode (decode store))
  | .expanded modes => .expanded (insert mode modes)

theorem has_iff (store : Store) (mode : Nat) :
    has store mode = true ↔ mode ∈ decode store := by
  cases store <;> simp [has, decode]

theorem decode_add (store : Store) (mode : Nat) :
    decode (add store mode) = insert mode (decode store) := by
  cases store with
  | expanded modes => rfl
  | compact mask =>
    by_cases h : mode < 31
    · apply Finset.ext
      intro query
      simp only [add, h, ↓reduceIte, decode, Finset.mem_filter, Finset.mem_range,
        Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq,
        Finset.mem_insert]
      constructor
      · rintro ⟨hq, hm | he⟩
        · exact Or.inr ⟨hq, hm⟩
        · exact Or.inl he.symm
      · rintro (rfl | ⟨hq, hm⟩)
        · exact ⟨h, Or.inr rfl⟩
        · exact ⟨hq, Or.inl hm⟩
    · simp [add, h, decode]

theorem add_valid (store : Store) (mode : Nat) (h : valid store) :
    valid (add store mode) := by
  cases store with
  | expanded modes => trivial
  | compact mask =>
    by_cases hm : mode < 31
    · simp only [add, hm, ↓reduceIte, valid]
      exact Nat.or_lt_two_pow h (Nat.pow_lt_pow_right (by decide) hm)
    · simp [add, hm, valid]

theorem no_alias (store : Store) (mode query : Nat) (h : query ≠ mode) :
    has (add store mode) query = has store query := by
  apply Bool.eq_iff_iff.mpr
  simp [has_iff, decode_add, h]

theorem fresh_increases_card (store : Store) (mode : Nat)
    (h : has store mode = false) :
    (decode (add store mode)).card = (decode store).card + 1 := by
  rw [decode_add, Finset.card_insert_of_notMem]
  simpa [← has_iff] using h

end Reconcile.Claims
