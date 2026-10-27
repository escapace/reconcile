import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Property.PropertyPlacement

/-! The own-key order of an ordinary object, and why `produce` keeps it.

`ownKeys` is `OrdinaryOwnPropertyKeys` over an object's keys in creation order: integer keys in
ascending order, then names and then symbols in creation order. Assignment adds a key the object
lacks at the end, and `delete` removes one, so deleting and assigning again moves a key to the
end of its sector.

A draft stores its properties in an ordinary object filled with the base object's keys in their
own order (`preparePropertyCopy`); the recipe's assignments and deletions apply to that store, and
finalization defines the result's keys in the store's own order. Applying the same mutations to
the base object itself is the reference. The store's creation order can differ from the base's,
since its integer keys are created in ascending order, but own keys depend on the integer keys only
as a set (`SameKeys`), and rebuilding an object from its own keys preserves them
(`rebuild_preserves`), so the result has the reference's order (`produce_key_order`). Native
correspondence requires the engine to implement `ownKeys` and the draft store to follow ordinary
assignment and deletion, which the KeyOrder bridge checks against both. -/
namespace Reconcile.KeyOrder

open Reconcile.PropertyOrder Reconcile.PropertyPlacement

def label : Key → Nat
  | .index n => n
  | .name n => n
  | .symbol n => n

def indexLe (a b : Key) : Bool := decide (label a ≤ label b)

/-- `OrdinaryOwnPropertyKeys` over keys in creation order. -/
def ownKeys (created : List Key) : List Key :=
  (created.filter isIndex).mergeSort indexLe ++ created.filter isName ++ created.filter isSymbol

inductive Op where
  | assign (key : Key)
  | remove (key : Key)
  deriving DecidableEq, Repr

/-- Assignment adds a missing key at the end; `delete` removes a key. -/
def apply (created : List Key) : Op → List Key
  | .assign key => if key ∈ created then created else created ++ [key]
  | .remove key => created.erase key

def run (created : List Key) (ops : List Op) : List Key := ops.foldl apply created

/-- An object created by assigning `keys` in order. -/
def build (keys : List Key) : List Key := run [] (keys.map .assign)

theorem apply_nodup (created : List Key) (op : Op) (h : created.Nodup) :
    (apply created op).Nodup := by
  cases op with
  | assign key =>
    by_cases hk : key ∈ created
    · simpa [apply, hk] using h
    · simp only [apply, hk, if_false]
      exact h.append (List.nodup_singleton key) (List.disjoint_singleton.mpr hk)
  | remove key => exact h.erase key

theorem run_nodup (created : List Key) (ops : List Op) (h : created.Nodup) :
    (run created ops).Nodup := by
  induction ops generalizing created with
  | nil => exact h
  | cons op ops ih => exact ih _ (apply_nodup created op h)

theorem run_assigns (front keys : List Key) (h : (front ++ keys).Nodup) :
    run front (keys.map .assign) = front ++ keys := by
  induction keys generalizing front with
  | nil => simp [run]
  | cons k ks ih =>
    have hk : k ∉ front := fun m => (List.nodup_append.mp h).2.2 k m k (by simp) rfl
    have step : apply front (.assign k) = front ++ [k] := by simp [apply, hk]
    change run (apply front (.assign k)) (ks.map .assign) = front ++ k :: ks
    rw [step, ih (front ++ [k]) (by simpa using h)]
    simp

/-- Assigning duplicate-free keys in order creates them in that order. -/
theorem build_nodup (keys : List Key) (h : keys.Nodup) : build keys = keys := by
  simpa [build] using run_assigns [] keys (by simpa using h)

theorem indexLe_total : ∀ a b : Key, (indexLe a b || indexLe b a) = true := by
  intro a b
  simp only [indexLe, Bool.or_eq_true, decide_eq_true_eq]
  omega

theorem indexLe_trans : ∀ a b c : Key, indexLe a b = true → indexLe b c = true →
    indexLe a c = true := by
  intro a b c
  simp only [indexLe, decide_eq_true_eq]
  omega

theorem filter_sector (p : Key → Bool) (q : Key → Bool) (l : List Key)
    (h : ∀ k ∈ l, p k = true → q k = false) : (l.filter p).filter q = [] := by
  rw [List.filter_filter, List.filter_eq_nil_iff]
  intro k hk
  by_cases hp : p k = true <;> simp_all

theorem sorted_isIndex {created : List Key} {k : Key}
    (hk : k ∈ (created.filter isIndex).mergeSort indexLe) : isIndex k = true :=
  (List.mem_filter.mp ((List.mergeSort_perm _ _).subset hk)).2

/-- Own keys hold the integer keys sorted, and the names and the symbols in creation order. -/
theorem ownKeys_filter_index (created : List Key) :
    (ownKeys created).filter isIndex = (created.filter isIndex).mergeSort indexLe := by
  unfold ownKeys
  rw [List.filter_append, List.filter_append, List.filter_eq_self.mpr fun k hk => sorted_isIndex hk,
    filter_sector isName isIndex created (by
      intro k _ h; cases k <;> simp_all [isName, isIndex]),
    filter_sector isSymbol isIndex created (by
      intro k _ h; cases k <;> simp_all [isSymbol, isIndex])]
  simp

theorem ownKeys_filter_name (created : List Key) :
    (ownKeys created).filter isName = created.filter isName := by
  unfold ownKeys
  rw [List.filter_append, List.filter_append,
    List.filter_eq_nil_iff.mpr (fun k hk => by
      have := sorted_isIndex hk; cases k <;> simp_all [isName, isIndex]),
    filter_sector isSymbol isName created (by
      intro k _ h; cases k <;> simp_all [isSymbol, isName]),
    List.filter_filter]
  simp

theorem ownKeys_filter_symbol (created : List Key) :
    (ownKeys created).filter isSymbol = created.filter isSymbol := by
  unfold ownKeys
  rw [List.filter_append, List.filter_append,
    List.filter_eq_nil_iff.mpr (fun k hk => by
      have := sorted_isIndex hk; cases k <;> simp_all [isSymbol, isIndex]),
    filter_sector isName isSymbol created (by
      intro k _ h; cases k <;> simp_all [isSymbol, isName]),
    List.filter_filter]
  simp

/-- Listing own keys is idempotent: their order is already the own-key order. -/
theorem ownKeys_ownKeys (created : List Key) : ownKeys (ownKeys created) = ownKeys created := by
  have sorted := List.pairwise_mergeSort indexLe_trans indexLe_total (created.filter isIndex)
  conv_lhs => rw [ownKeys]
  rw [ownKeys_filter_index, ownKeys_filter_name, ownKeys_filter_symbol,
    List.mergeSort_of_pairwise sorted]
  rfl

theorem ownKeys_nodup (created : List Key) (h : created.Nodup) : (ownKeys created).Nodup := by
  have hperm : (ownKeys created).Perm (created.filter isIndex ++ created.filter isName ++
      created.filter isSymbol) := by
    unfold ownKeys
    exact ((List.mergeSort_perm _ _).append_right _).append_right _
  apply hperm.nodup_iff.mpr
  have hd1 := h.filter isIndex
  have hd2 := h.filter isName
  have hd3 := h.filter isSymbol
  refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨hd1, hd2, ?_⟩, hd3, ?_⟩
  · intro a ha b hb e
    subst e
    have := (List.mem_filter.mp ha).2
    have := (List.mem_filter.mp hb).2
    cases a <;> simp_all [isIndex, isName]
  · intro a ha b hb e
    subst e
    have := (List.mem_filter.mp hb).2
    rcases List.mem_append.mp ha with h' | h' <;> have := (List.mem_filter.mp h').2 <;>
      cases a <;> simp_all [isIndex, isName, isSymbol]

/-- Rebuilding an object by assigning its own keys in order preserves them. -/
theorem rebuild_preserves (created : List Key) (h : created.Nodup) :
    ownKeys (build (ownKeys created)) = ownKeys created := by
  rw [build_nodup _ (ownKeys_nodup created h), ownKeys_ownKeys]

/-- Two creation orders with the same integer keys, and the same names and the same symbols in
order. -/
def SameKeys (l₁ l₂ : List Key) : Prop :=
  (l₁.filter isIndex).Perm (l₂.filter isIndex) ∧ l₁.filter isName = l₂.filter isName ∧
    l₁.filter isSymbol = l₂.filter isSymbol

/-- Such creation orders list the same own keys. -/
theorem SameKeys.ownKeys_eq {l₁ l₂ : List Key} (h : SameKeys l₁ l₂) : ownKeys l₁ = ownKeys l₂ := by
  obtain ⟨hi, hn, hs⟩ := h
  have hsort : (l₁.filter isIndex).mergeSort indexLe = (l₂.filter isIndex).mergeSort indexLe :=
    List.Perm.eq_of_pairwise
      (fun a b ha hb hab hba => by
        have ia := sorted_isIndex ha
        have ib := sorted_isIndex hb
        cases a <;> cases b <;> simp_all [isIndex, indexLe, label]
        omega)
      (List.pairwise_mergeSort indexLe_trans indexLe_total _)
      (List.pairwise_mergeSort indexLe_trans indexLe_total _)
      (((List.mergeSort_perm _ _).trans hi).trans (List.mergeSort_perm _ _).symm)
  unfold ownKeys
  rw [hsort, hn, hs]

theorem SameKeys.mem {l₁ l₂ : List Key} (h : SameKeys l₁ l₂) (k : Key) : k ∈ l₁ ↔ k ∈ l₂ := by
  obtain ⟨hi, hn, hs⟩ := h
  cases k with
  | index n => simpa [isIndex] using hi.mem_iff (a := .index n)
  | name n => simpa [isName] using congrArg (Key.name n ∈ ·) hn
  | symbol n => simpa [isSymbol] using congrArg (Key.symbol n ∈ ·) hs

/-- The same mutations keep two such creation orders such. -/
theorem SameKeys.run {l₁ l₂ : List Key} (h : SameKeys l₁ l₂) (ops : List Op) :
    SameKeys (run l₁ ops) (run l₂ ops) := by
  induction ops generalizing l₁ l₂ with
  | nil => exact h
  | cons op ops ih =>
    refine ih (l₁ := apply l₁ op) (l₂ := apply l₂ op) ?_
    have hmem := h.mem
    obtain ⟨hi, hn, hs⟩ := h
    cases op with
    | assign k =>
      by_cases hk : k ∈ l₁
      · simp only [apply, hk, (hmem k).1 hk, if_true]
        exact ⟨hi, hn, hs⟩
      · have hk₂ : k ∉ l₂ := fun m => hk ((hmem k).2 m)
        simp only [apply, hk, hk₂, if_false]
        refine ⟨?_, ?_, ?_⟩ <;> simp only [List.filter_append]
        · exact hi.append_right _
        · rw [hn]
        · rw [hs]
    | remove k =>
      simp only [apply]
      refine ⟨?_, ?_, ?_⟩ <;> simp only [← List.erase_filter]
      · exact hi.erase k
      · rw [hn]
      · rw [hs]

/-- A copy built from an object's own keys has the same own keys as the object. -/
theorem sameKeys_ownKeys (created : List Key) : SameKeys (ownKeys created) created :=
  ⟨by rw [ownKeys_filter_index]; exact List.mergeSort_perm _ _, ownKeys_filter_name created,
    ownKeys_filter_symbol created⟩

/-- `produce` gives the result the own keys that the recipe's mutations give the base object
itself: the draft store is a copy built from the base's own keys in order, the recipe's
assignments and deletions apply to it, and finalization rebuilds the result from the store's own
keys. -/
theorem produce_key_order (base : List Key) (ops : List Op) (h : base.Nodup) :
    ownKeys (build (ownKeys (run (build (ownKeys base)) ops))) = ownKeys (run base ops) := by
  have hown := ownKeys_nodup base h
  rw [build_nodup _ hown, rebuild_preserves _ (run_nodup _ ops hown)]
  exact ((sameKeys_ownKeys base).run ops).ownKeys_eq

/-- Deleting and assigning again moves a key to the end of its sector, as the engine does. -/
example : ownKeys (run [.name 0, .name 1, .symbol 0] [.remove (.name 0), .assign (.name 0)]) =
    [.name 1, .name 0, .symbol 0] := by
  simp [ownKeys, run, apply, isIndex, isName, isSymbol]

end Reconcile.KeyOrder
