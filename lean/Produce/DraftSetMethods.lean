import Produce.DraftMembers

/-!
# Draft `Set` methods

A `Set` draft's `union`, `intersection`, `difference`, `symmetricDifference`, `isSubsetOf`,
`isSupersetOf` and `isDisjointFrom` follow the native algorithms over a set-like operand, which
supplies `size`, `has` and `keys`. Where the native algorithm decides whether a value is a member
of the draft, the draft compares member identities, as its `has` does (`DraftMembers`); the
operand's own `has` decides membership in the operand and receives the draft's members as the
draft returns them.

`members` lists the draft's members and `keys` the operand's, each in iteration order and
distinct by identity; the operand's `has` answers by identity over `keys`. Where the native
algorithm chooses by the two sizes between walking the draft and walking the operand's keys, the
model does too, and each method gives the same members either way. The model assumes an operand
whose `has` and `keys` agree and change nothing; the runtime calls them in the native order,
which native tests check.
-/

namespace Reconcile.DraftSetMethods

open Reconcile.DraftMembers

variable {α β : Type} [DecidableEq β] (identity : α → β)

/-- Whether `l` holds a value with `x`'s identity. -/
abbrev mem (l : List α) (x : α) : Bool := includes identity l x

/-- The draft's members, then the operand's keys the draft does not hold. -/
def union (members keys : List α) : List α :=
  members ++ keys.filter fun k => !mem identity members k

/-- Walks the draft when it is not larger than the operand, otherwise the operand's keys. -/
def intersection (members keys : List α) : List α :=
  if members.length ≤ keys.length then members.filter fun e => mem identity keys e
  else keys.filter fun k => mem identity members k

/-- Either walk removes the same members from a copy of the draft's. -/
def difference (members keys : List α) : List α :=
  members.filter fun e => !mem identity keys e

/-- The draft's members the operand lacks, then the operand's keys the draft lacks. -/
def symmetricDifference (members keys : List α) : List α :=
  members.filter (fun e => !mem identity keys e) ++ keys.filter fun k => !mem identity members k

def isSubsetOf (members keys : List α) : Bool :=
  members.length ≤ keys.length && members.all fun e => mem identity keys e

def isSupersetOf (members keys : List α) : Bool :=
  keys.length ≤ members.length && keys.all fun k => mem identity members k

def isDisjointFrom (members keys : List α) : Bool :=
  if members.length ≤ keys.length then members.all fun e => !mem identity keys e
  else keys.all fun k => !mem identity members k

theorem mem_iff (l : List α) (x : α) : mem identity l x = true ↔ ∃ e ∈ l, identity e = identity x := by
  simp [mem, includes]

/-- A value is in a union when it is in either side. -/
theorem mem_union (members keys : List α) (x : α) :
    mem identity (union identity members keys) x = (mem identity members x || mem identity keys x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [union, Bool.or_eq_true, mem_iff, List.mem_append, List.mem_filter,
    Bool.not_eq_true']
  constructor
  · rintro ⟨e, h | ⟨h, -⟩, he⟩
    · exact Or.inl ⟨e, h, he⟩
    · exact Or.inr ⟨e, h, he⟩
  · rintro (⟨e, h, he⟩ | ⟨e, h, he⟩)
    · exact ⟨e, Or.inl h, he⟩
    · cases hm : mem identity members e
      · exact ⟨e, Or.inr ⟨h, hm⟩, he⟩
      · obtain ⟨f, hf, hfe⟩ := (mem_iff identity members e).mp hm
        exact ⟨f, Or.inl hf, hfe.trans he⟩

/-- A value is in an intersection when it is in both sides, whichever side the algorithm walks. -/
theorem mem_intersection (members keys : List α) (x : α) :
    mem identity (intersection identity members keys) x =
      (mem identity members x && mem identity keys x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true]
  unfold intersection
  split
  · simp only [mem_iff, List.mem_filter]
    constructor
    · rintro ⟨e, ⟨h, f, hf, hfe⟩, he⟩
      exact ⟨⟨e, h, he⟩, f, hf, hfe.trans he⟩
    · rintro ⟨⟨e, h, he⟩, f, hf, hfe⟩
      exact ⟨e, ⟨h, f, hf, hfe.trans he.symm⟩, he⟩
  · simp only [mem_iff, List.mem_filter]
    constructor
    · rintro ⟨e, ⟨h, f, hf, hfe⟩, he⟩
      exact ⟨⟨f, hf, hfe.trans he⟩, e, h, he⟩
    · rintro ⟨⟨e, h, he⟩, f, hf, hfe⟩
      exact ⟨f, ⟨hf, e, h, he.trans hfe.symm⟩, hfe⟩

/-- A value is in a difference when it is in the draft and not in the operand. -/
theorem mem_difference (members keys : List α) (x : α) :
    mem identity (difference identity members keys) x =
      (mem identity members x && !mem identity keys x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, Bool.not_eq_true', difference, mem_iff, List.mem_filter]
  constructor
  · rintro ⟨e, ⟨h, hk⟩, he⟩
    refine ⟨⟨e, h, he⟩, ?_⟩
    rw [Bool.eq_false_iff, ne_eq, mem_iff] at hk ⊢
    rintro ⟨f, hf, hfe⟩
    exact hk ⟨f, hf, hfe.trans he.symm⟩
  · rintro ⟨⟨e, h, he⟩, hk⟩
    refine ⟨e, ⟨h, ?_⟩, he⟩
    rw [Bool.eq_false_iff, ne_eq, mem_iff] at hk ⊢
    rintro ⟨f, hf, hfe⟩
    exact hk ⟨f, hf, hfe.trans he⟩

/-- A value is in a symmetric difference when it is in exactly one side. -/
theorem mem_symmetricDifference (members keys : List α) (x : α) :
    mem identity (symmetricDifference identity members keys) x =
      (mem identity members x != mem identity keys x) := by
  have hd := mem_difference identity members keys x
  have hd' := mem_difference identity keys members x
  unfold difference at hd hd'
  unfold symmetricDifference
  simp only [mem, includes, List.any_append] at hd hd' ⊢
  rw [hd, hd']
  generalize members.any (fun e => identity e == identity x) = a
  generalize keys.any (fun e => identity e == identity x) = b
  cases a <;> cases b <;> rfl

/-- `isDisjointFrom` gives the same answer whichever side the algorithm walks. -/
theorem isDisjointFrom_walk (members keys : List α) :
    isDisjointFrom identity members keys = members.all fun e => !mem identity keys e := by
  unfold isDisjointFrom
  split
  · rfl
  · apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, mem_iff]
    constructor
    · rintro h e he ⟨f, hf, hfe⟩
      exact h f hf ⟨e, he, hfe.symm⟩
    · rintro h f hf ⟨e, he, hfe⟩
      exact h e he ⟨f, hf, hfe.symm⟩

/-- The methods see only identities: the draft's members as drafts, or the operand's keys in any
form, give results with the same identities. -/
theorem union_identity (members keys : List α) :
    (union identity members keys).map identity =
      union id (members.map identity) (keys.map identity) := by
  simp [union, mem, includes, List.filter_map, Function.comp_def, List.any_map]

theorem intersection_identity (members keys : List α) :
    (intersection identity members keys).map identity =
      intersection id (members.map identity) (keys.map identity) := by
  unfold intersection
  simp only [List.length_map]
  split <;> simp [mem, includes, List.filter_map, Function.comp_def, List.any_map]

theorem difference_identity (members keys : List α) :
    (difference identity members keys).map identity =
      difference id (members.map identity) (keys.map identity) := by
  simp [difference, mem, includes, List.filter_map, Function.comp_def, List.any_map]

theorem symmetricDifference_identity (members keys : List α) :
    (symmetricDifference identity members keys).map identity =
      symmetricDifference id (members.map identity) (keys.map identity) := by
  simp [symmetricDifference, mem, includes, List.filter_map, Function.comp_def, List.any_map]

theorem isSubsetOf_identity (members keys : List α) :
    isSubsetOf identity members keys = isSubsetOf id (members.map identity) (keys.map identity) := by
  simp [isSubsetOf, mem, includes, Function.comp_def, List.any_map, List.all_map]

theorem isSupersetOf_identity (members keys : List α) :
    isSupersetOf identity members keys =
      isSupersetOf id (members.map identity) (keys.map identity) := by
  simp [isSupersetOf, mem, includes, Function.comp_def, List.any_map, List.all_map]

theorem isDisjointFrom_identity (members keys : List α) :
    isDisjointFrom identity members keys =
      isDisjointFrom id (members.map identity) (keys.map identity) := by
  unfold isDisjointFrom
  simp only [List.length_map]
  split <;> simp [mem, includes, Function.comp_def, List.any_map, List.all_map]

section drafted

variable (draft : α → α) (same : ∀ a, identity (draft a) = identity a)
include same

omit [DecidableEq β] in
private theorem map_drafted (l : List α) : (l.map draft).map identity = l.map identity := by
  simp [List.map_map, Function.comp_def, same]

/-- A draft that holds drafts of its members gives results with the same identities, and the same
answers, as one that holds the members. -/
theorem union_drafted (members keys : List α) :
    (union identity (members.map draft) keys).map identity =
      (union identity members keys).map identity := by
  rw [union_identity, union_identity, map_drafted identity draft same]

theorem intersection_drafted (members keys : List α) :
    (intersection identity (members.map draft) keys).map identity =
      (intersection identity members keys).map identity := by
  rw [intersection_identity, intersection_identity, map_drafted identity draft same]

theorem difference_drafted (members keys : List α) :
    (difference identity (members.map draft) keys).map identity =
      (difference identity members keys).map identity := by
  rw [difference_identity, difference_identity, map_drafted identity draft same]

theorem symmetricDifference_drafted (members keys : List α) :
    (symmetricDifference identity (members.map draft) keys).map identity =
      (symmetricDifference identity members keys).map identity := by
  rw [symmetricDifference_identity, symmetricDifference_identity,
    map_drafted identity draft same]

theorem isSubsetOf_drafted (members keys : List α) :
    isSubsetOf identity (members.map draft) keys = isSubsetOf identity members keys := by
  rw [isSubsetOf_identity identity (members.map draft), isSubsetOf_identity identity members,
    map_drafted identity draft same]

theorem isSupersetOf_drafted (members keys : List α) :
    isSupersetOf identity (members.map draft) keys = isSupersetOf identity members keys := by
  rw [isSupersetOf_identity identity (members.map draft), isSupersetOf_identity identity members,
    map_drafted identity draft same]

theorem isDisjointFrom_drafted (members keys : List α) :
    isDisjointFrom identity (members.map draft) keys = isDisjointFrom identity members keys := by
  rw [isDisjointFrom_identity identity (members.map draft), isDisjointFrom_identity identity members,
    map_drafted identity draft same]

end drafted

/-- Counterexample: comparing the values themselves, as a `Set` operation on the draft's stored
members would, misses an object the operand holds as its draft. -/
example : intersection id [0] [1] = [] ∧ intersection (fun n : Nat => n % 2) [0] [2] = [0] := by
  decide

end Reconcile.DraftSetMethods
