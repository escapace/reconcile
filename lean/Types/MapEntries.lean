/-!
# A `Map`'s entries

A `Map` is modelled as its entries in insertion order. `put` is the built-in `Map.prototype.set`:
the entry that holds the key takes the value in place, and a new key is appended. `remove` is the
built-in `Map.prototype.delete`. A `Set` is the case where each member is its own key with a fixed
value. Keys compare by equality: the runtime's keys are canonical (SameValueZero on primitives,
identity on objects), a premise every model built on this one takes.

The collection models share it: publication (`Graph.CollectionPlan`), decoding
(`Serialization.Collection`) and a `Map` draft (`Produce.DraftIteration`). This module uses only
core lemmas, so the models the oracle runs can import it.
-/
namespace Reconcile.Types.MapEntries

variable {K V : Type} [DecidableEq K]

/-- The keys of entries, in order. -/
def keys (m : List (K × V)) : List K := m.map Prod.fst

/-- `Map.prototype.set`: the entry holding `key` takes `value` in place; a new key is appended. -/
def put (key : K) (value : V) : List (K × V) → List (K × V)
  | [] => [(key, value)]
  | (first, old) :: rest =>
    if key = first then (first, value) :: rest else (first, old) :: put key value rest

/-- `Map.prototype.delete`: the entry holding `key` is removed. -/
def remove (key : K) (m : List (K × V)) : List (K × V) := m.filter (·.1 ≠ key)

omit [DecidableEq K] in
theorem keys_append (a b : List (K × V)) : keys (a ++ b) = keys a ++ keys b :=
  List.map_append

/-- Putting a key that an entry holds, past entries that do not, replaces its value in place. -/
theorem put_middle (a b : List (K × V)) (key : K) (old value : V) (ha : key ∉ keys a) :
    put key value (a ++ (key, old) :: b) = a ++ (key, value) :: b := by
  induction a with
  | nil => simp [put]
  | cons e a ih =>
    obtain ⟨first, v⟩ := e
    simp only [keys, List.map_cons, List.mem_cons, not_or] at ha
    simp only [List.cons_append, put, if_neg ha.1, ih ha.2]

/-- Putting a new key appends it. -/
theorem put_new (m : List (K × V)) (key : K) (value : V) (h : key ∉ keys m) :
    put key value m = m ++ [(key, value)] := by
  induction m with
  | nil => rfl
  | cons e m ih =>
    obtain ⟨first, v⟩ := e
    simp only [keys, List.map_cons, List.mem_cons, not_or] at h
    simp only [List.cons_append, put, if_neg h.1, ih h.2]

/-- Removing a key that no entry holds changes nothing. -/
theorem remove_absent (m : List (K × V)) (key : K) (h : key ∉ keys m) : remove key m = m :=
  List.filter_eq_self.mpr fun e he => by
    have : e.1 ≠ key := fun eq => h (eq ▸ List.mem_map_of_mem he)
    simpa using this

/-- Removing a key that one entry holds removes that entry. -/
theorem remove_middle (a b : List (K × V)) (key : K) (value : V) (ha : key ∉ keys a)
    (hb : key ∉ keys b) : remove key (a ++ (key, value) :: b) = a ++ b := by
  have h1 := remove_absent a key ha
  have h2 := remove_absent b key hb
  unfold remove at h1 h2 ⊢
  rw [List.filter_append, List.filter_cons_of_neg (by simp), h1, h2]

end Reconcile.Types.MapEntries
