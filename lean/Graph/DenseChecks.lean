import Graph.Execution
import Mathlib.Data.Fintype.Card

/-! The call-owned byte membership of `CheckedNodes` (`src/graph/checked.ts`) decodes to the
immutable reducer's finite set. Only 0/1 marks are modeled; native array bounds and linear
ownership are adapter premises. Fresh revisions allocate an empty store, so no epoch wrap is
needed. -/

namespace Reconcile.DenseChecks

structure Store (n : Nat) where
  marks : Fin n → Bool
  count : Nat

def decode {n : Nat} (s : Store n) : Finset (Fin n) :=
  Finset.univ.filter fun i => s.marks i

def Valid {n : Nat} (s : Store n) : Prop := s.count = (decode s).card

def empty (n : Nat) : Store n := ⟨fun _ => false, 0⟩

def mark {n : Nat} (s : Store n) (node : Fin n) : Store n :=
  if s.marks node then s else
    ⟨fun i => if i = node then true else s.marks i, s.count + 1⟩

theorem decode_empty (n : Nat) : decode (empty n) = ∅ := by
  simp [decode, empty]

theorem empty_valid (n : Nat) : Valid (empty n) := by
  simp [Valid, decode, empty]

theorem decode_mark {n : Nat} (s : Store n) (node : Fin n) :
    decode (mark s node) = insert node (decode s) := by
  unfold mark
  split
  · rename_i h
    apply Finset.ext
    intro i
    simp only [decode, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · exact Or.inr
    · rintro (rfl | hi)
      · exact h
      · exact hi
  · apply Finset.ext
    intro i
    by_cases h : i = node <;> simp [decode, h]

theorem mark_valid {n : Nat} (s : Store n) (node : Fin n) (h : Valid s) :
    Valid (mark s node) := by
  unfold Valid
  rw [decode_mark]
  unfold mark
  split
  · rename_i hm
    have hn : node ∈ decode s := by simp [decode, hm]
    simpa [Finset.insert_eq_of_mem hn] using h
  · rename_i hm
    have hn : node ∉ decode s := by simpa [decode] using hm
    change s.count + 1 = (insert node (decode s)).card
    rw [Finset.card_insert_of_notMem hn]
    exact congrArg (· + 1) h

theorem complete_iff_count {n : Nat} (s : Store n) (h : Valid s) :
    s.count = n ↔ decode s = Finset.univ := by
  rw [h]
  constructor
  · intro hc
    exact Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simpa using hc.ge)
  · intro hs
    simp [hs]

/-- Mapping dense indices to graph labels preserves the reducer's insertion operation. -/
def labels {n : Nat} (s : Store n) : Finset Nat := (decode s).image Fin.val

theorem labels_mark {n : Nat} (s : Store n) (node : Fin n) :
    labels (mark s node) = insert node.val (labels s) := by
  simp [labels, decode_mark]

end Reconcile.DenseChecks

namespace Reconcile.Execution

/-- Reverse construction membership depends only on the selected plan's fixed edge facts. -/
noncomputable def incoming (s : State) (node : Nat) : List Nat :=
  s.domain.toList.flatMap fun owner =>
    ((s.bindings owner).construction.filter fun edge => edge.node = node).map (·.identity)

theorem incoming_stable_iff (s : State) (node actual : Nat) :
    (∀ identity ∈ incoming s node, identity = actual) ↔ constructionStable s node actual := by
  simp only [incoming, List.mem_flatMap, List.mem_map, List.mem_filter,
    Finset.mem_toList, decide_eq_true_eq, forall_exists_index, and_imp,
    constructionStable]
  constructor
  · intro h owner ho edge he hn
    exact h edge.identity owner ho edge he hn rfl
  · intro h identity owner ho edge he hn hi
    exact hi.symm.trans (h owner ho edge he hn)

end Reconcile.Execution
