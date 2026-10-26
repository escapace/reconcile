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
finalization defines the result's keys in the store's own order. Applying the same mutations to a
plain copy is the reference. Rebuilding an object from its own keys preserves them
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

/-- Listing own keys is idempotent: their order is already the own-key order. -/
theorem ownKeys_ownKeys (created : List Key) : ownKeys (ownKeys created) = ownKeys created := by
  have sorted := List.pairwise_mergeSort indexLe_trans indexLe_total (created.filter isIndex)
  have hidx : ∀ k ∈ (created.filter isIndex).mergeSort indexLe, isIndex k = true := fun k hk =>
    (List.mem_filter.mp ((List.mergeSort_perm _ _).subset hk)).2
  unfold ownKeys
  have e1 : (((created.filter isIndex).mergeSort indexLe ++ created.filter isName ++
      created.filter isSymbol).filter isIndex) = (created.filter isIndex).mergeSort indexLe := by
    rw [List.filter_append, List.filter_append, List.filter_eq_self.mpr hidx]
    rw [filter_sector isName isIndex created (by intro k _ h; cases k <;> simp_all [isName, isIndex]),
      filter_sector isSymbol isIndex created (by intro k _ h; cases k <;> simp_all [isSymbol, isIndex])]
    simp
  have e2 : (((created.filter isIndex).mergeSort indexLe ++ created.filter isName ++
      created.filter isSymbol).filter isName) = created.filter isName := by
    rw [List.filter_append, List.filter_append,
      List.filter_eq_nil_iff.mpr (fun k hk => by
        have := hidx k hk; cases k <;> simp_all [isName, isIndex]),
      filter_sector isSymbol isName created (by
        intro k _ h; cases k <;> simp_all [isSymbol, isName]),
      List.filter_filter]
    simp
  have e3 : (((created.filter isIndex).mergeSort indexLe ++ created.filter isName ++
      created.filter isSymbol).filter isSymbol) = created.filter isSymbol := by
    rw [List.filter_append, List.filter_append,
      List.filter_eq_nil_iff.mpr (fun k hk => by
        have := hidx k hk; cases k <;> simp_all [isSymbol, isIndex]),
      filter_sector isName isSymbol created (by
        intro k _ h; cases k <;> simp_all [isSymbol, isName]),
      List.filter_filter]
    simp
  rw [e1, e2, e3, List.mergeSort_of_pairwise sorted]

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

/-- `produce` keeps the reference's key order: the draft store is a copy of the base's own keys
in order, the recipe's mutations apply to it, and finalization rebuilds the result from the
store's own keys; the reference applies the same mutations to a plain copy. -/
theorem produce_key_order (base : List Key) (ops : List Op) (h : base.Nodup) :
    let store := run (build (ownKeys base)) ops
    let reference := run (build (ownKeys base)) ops
    ownKeys (build (ownKeys store)) = ownKeys reference := by
  intro store reference
  have hcopy : (build (ownKeys base)).Nodup := by
    rw [build_nodup _ (ownKeys_nodup base h)]
    exact ownKeys_nodup base h
  exact rebuild_preserves _ (run_nodup _ ops hcopy)

/-- Deleting and assigning again moves a key to the end of its sector, as the engine does. -/
example : ownKeys (run [.name 0, .name 1, .symbol 0] [.remove (.name 0), .assign (.name 0)]) =
    [.name 1, .name 0, .symbol 0] := by
  simp [ownKeys, run, apply, isIndex, isName, isSymbol]

end Reconcile.KeyOrder
