import Mathlib.Data.List.Nodup

/-!
# Storage views

A Vue proxy is a view of its raw object (`storageIdentity` in `src/adapters/vue.ts`): the two
hold one storage and are one object. Identity restoration (`compileImmutable` in
`src/restore-identities.ts`) registers the objects a result holds in order and gives each storage
one node: an object whose storage a registered node already has resolves to that node, and the
edge from its slot carries the object as the view that slot keeps where the result keeps the node;
folding inside a fixed subtree skips an object whose storage is registered or already folded.

`register` models that discipline. The registered objects have pairwise distinct storages
(`register_storages_nodup`), every object resolves to a registered object of its storage
(`register_covers`), and registration adds no object it was not given (`register_subset`).
Registering the fixed nodes and records first and the folded objects after them is one
registration of the whole sequence (`register_append`), so the folded objects' storages differ
from each other and from every registered node (`folded_storages_nodup`). That is the storage
premise of `FoldedLeaves`, and the distinct storages `PromotedLeaves.kept_whole` asks of a result
kept whole, so the runtime's storage-conflict check never fires and a result kept whole is kept
without a walk.
-/

namespace Reconcile.StorageViews

variable {α β : Type} [DecidableEq β]

/-- Registers `xs` after the objects `acc` already registered, keeping the first object of each
storage. -/
def register (storage : α → β) : List α → List α → List α
  | acc, [] => acc
  | acc, x :: xs =>
    if storage x ∈ acc.map storage then register storage acc xs
    else register storage (acc ++ [x]) xs

/-- The registered objects have pairwise distinct storages. -/
theorem register_storages_nodup (storage : α → β) :
    ∀ (acc xs : List α), (acc.map storage).Nodup →
      ((register storage acc xs).map storage).Nodup
  | _, [], h => h
  | acc, x :: xs, h => by
    unfold register
    by_cases hx : storage x ∈ acc.map storage
    · rw [if_pos hx]
      exact register_storages_nodup storage acc xs h
    · rw [if_neg hx]
      apply register_storages_nodup storage
      rw [List.map_append, List.nodup_append]
      refine ⟨h, List.nodup_singleton _, ?_⟩
      intro a ha b hb
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      subst hb
      intro he
      exact hx (he ▸ ha)

/-- Every object, registered before or given, resolves to a registered object of its storage. -/
theorem register_covers (storage : α → β) :
    ∀ (acc xs : List α) (x : α), x ∈ acc ++ xs →
      ∃ y ∈ register storage acc xs, storage y = storage x
  | acc, [], x, hx => ⟨x, by simpa using hx, rfl⟩
  | acc, z :: xs, x, hx => by
    unfold register
    by_cases hz : storage z ∈ acc.map storage
    · rw [if_pos hz]
      rcases List.mem_append.mp hx with ha | hb
      · exact register_covers storage acc xs x (List.mem_append_left _ ha)
      · rcases List.mem_cons.mp hb with he | ht
        · subst he
          obtain ⟨w, hw, hs⟩ := List.mem_map.mp hz
          obtain ⟨y, hy, hys⟩ :=
            register_covers storage acc xs w (List.mem_append_left _ hw)
          exact ⟨y, hy, hys.trans hs⟩
        · exact register_covers storage acc xs x (List.mem_append_right _ ht)
    · rw [if_neg hz]
      apply register_covers storage (acc ++ [z]) xs x
      rcases List.mem_append.mp hx with ha | hb
      · exact List.mem_append_left _ (List.mem_append_left _ ha)
      · rcases List.mem_cons.mp hb with he | ht
        · subst he; simp
        · exact List.mem_append_right _ ht

/-- Registration adds no object it was not given. -/
theorem register_subset (storage : α → β) :
    ∀ (acc xs : List α) (y : α), y ∈ register storage acc xs → y ∈ acc ∨ y ∈ xs
  | _, [], _, hy => Or.inl hy
  | acc, x :: xs, y, hy => by
    unfold register at hy
    by_cases hx : storage x ∈ acc.map storage
    · rw [if_pos hx] at hy
      rcases register_subset storage acc xs y hy with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rw [if_neg hx] at hy
      rcases register_subset storage (acc ++ [x]) xs y hy with h | h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · exact Or.inr (by simp_all)
      · exact Or.inr (List.mem_cons_of_mem _ h)

/-- Registering two sequences in turn is registering their concatenation. -/
theorem register_append (storage : α → β) :
    ∀ (acc xs ys : List α),
      register storage acc (xs ++ ys) = register storage (register storage acc xs) ys
  | _, [], _ => rfl
  | acc, x :: xs, ys => by
    simp only [List.cons_append, register]
    split <;> exact register_append storage _ xs ys

/-- The fixed nodes and records registered first, then the objects folded inside fixed subtrees:
all their storages are pairwise distinct. -/
theorem folded_storages_nodup (storage : α → β) (registered descendants : List α) :
    ((register storage (register storage [] registered) descendants).map storage).Nodup := by
  rw [← register_append]
  exact register_storages_nodup storage [] _ List.nodup_nil

end Reconcile.StorageViews
