/-!
# Per-call shape trie

Record shapes are interned per `stringify` call: equal own-key sequences share one id, and
ids are assigned in first-occurrence order. The previous runtime keyed a `Map` by
`JSON.stringify(keys)`; the trie runtime walks one `Map` per key, creating missing nodes,
and stores the id on the node reached by the whole sequence.

This file models both and proves they assign identical id sequences. Keys have any type `κ`
with decidable equality; JavaScript property names are UTF-16 code-unit sequences (lone
surrogates included), and runtime `Map` keys compare strings by SameValueZero, which on
strings is code-unit equality. The signature memo is modelled as a finite map keyed by the
key list itself.

Native and runtime premises (not proved here):
- `JSON.stringify` is injective on arrays of strings and observes nothing on the fresh key
  arrays from `Object.getOwnPropertyNames` (no inherited `toJSON`; built-ins unmodified).
- Trie nodes are fresh per call and reachable by exactly one key path, so the runtime's
  in-place `Map.set` on a node agrees with the functional `ensure`/`set` below.
- `next` is the current `shapes.length`; the same keys array is pushed in both runtimes.
-/

namespace SerializationShapeTrie

variable {κ : Type} [DecidableEq κ]

inductive Trie (κ : Type) where
  | node (id : Option Nat) (children : List (κ × Trie κ))

def Trie.id : Trie κ → Option Nat
  | .node id _ => id

def Trie.children : Trie κ → List (κ × Trie κ)
  | .node _ children => children

def empty : Trie κ := .node none []

/-- First child stored under `key`, or a fresh empty node when absent. -/
def find (key : κ) : List (κ × Trie κ) → Trie κ
  | [] => empty
  | (k, t) :: rest => if k = key then t else find key rest

/-- Replace the first child under `key`, or append it. -/
def update (key : κ) (child : Trie κ) : List (κ × Trie κ) → List (κ × Trie κ)
  | [] => [(key, child)]
  | (k, t) :: rest => if k = key then (key, child) :: rest else (k, t) :: update key child rest

theorem find_update_same (key : κ) (child : Trie κ) (cs : List (κ × Trie κ)) :
    find key (update key child cs) = child := by
  induction cs with
  | nil => simp [update, find]
  | cons head rest ih =>
    rcases head with ⟨k, t⟩
    by_cases h : k = key <;> simp [update, find, h, ih]

theorem find_update_other {key other : κ} (child : Trie κ) (cs : List (κ × Trie κ))
    (h : other ≠ key) : find other (update key child cs) = find other cs := by
  induction cs with
  | nil => simp [update, find, Ne.symm h, empty]
  | cons head rest ih =>
    rcases head with ⟨k, t⟩
    by_cases hk : k = key
    · subst hk
      simp [update, find, Ne.symm h]
    · simp [update, find, hk, ih]

def get : Trie κ → List κ → Option Nat
  | t, [] => t.id
  | t, k :: ks => get (find k t.children) ks

/-- Runtime walk: create every missing node on the path, leaving ids unchanged. -/
def ensure : Trie κ → List κ → Trie κ
  | t, [] => t
  | t, k :: ks => .node t.id (update k (ensure (find k t.children) ks) t.children)

/-- Runtime store: set the id on the node reached by the whole path. -/
def set : Trie κ → List κ → Nat → Trie κ
  | t, [], v => .node (some v) t.children
  | t, k :: ks, v => .node t.id (update k (set (find k t.children) ks v) t.children)

theorem get_ensure (t : Trie κ) (p q : List κ) : get (ensure t p) q = get t q := by
  induction p generalizing t q with
  | nil => rfl
  | cons k ks ih =>
    cases q with
    | nil => rfl
    | cons k' qs =>
      by_cases h : k' = k
      · subst h
        simp [ensure, get, Trie.children, find_update_same, ih]
      · simp [ensure, get, Trie.children, find_update_other _ _ h]

theorem get_set (t : Trie κ) (p q : List κ) (v : Nat) :
    get (set t p v) q = if q = p then some v else get t q := by
  induction p generalizing t q with
  | nil =>
    cases q with
    | nil => rfl
    | cons k qs => simp [set, get, Trie.children]
  | cons k ks ih =>
    cases q with
    | nil => simp [set, get, Trie.id]
    | cons k' qs =>
      by_cases h : k' = k
      · subst h
        simp [set, get, Trie.children, find_update_same, ih]
      · simp [set, get, Trie.children, find_update_other _ _ h, h]

/-- One trie interning step as the runtime performs it: walk (creating nodes), then reuse
the stored id or assign the next table index. -/
def internTrie (t : Trie κ) (next : Nat) (keys : List κ) : Nat × Trie κ × Nat :=
  let walked := ensure t keys
  match get walked keys with
  | some id => (id, walked, next)
  | none => (next, set walked keys next, next + 1)

/-- One signature-memo interning step. -/
def internMemo (m : List κ → Option Nat) (next : Nat) (keys : List κ) :
    Nat × (List κ → Option Nat) × Nat :=
  match m keys with
  | some id => (id, m, next)
  | none => (next, fun q => if q = keys then some next else m q, next + 1)

def runTrie : Trie κ → Nat → List (List κ) → List Nat
  | _, _, [] => []
  | t, next, keys :: rest =>
    let r := internTrie t next keys
    r.1 :: runTrie r.2.1 r.2.2 rest

def runMemo : (List κ → Option Nat) → Nat → List (List κ) → List Nat
  | _, _, [] => []
  | m, next, keys :: rest =>
    let r := internMemo m next keys
    r.1 :: runMemo r.2.1 r.2.2 rest

theorem intern_step (t : Trie κ) (m : List κ → Option Nat) (next : Nat) (keys : List κ)
    (h : ∀ q, get t q = m q) :
    (internTrie t next keys).1 = (internMemo m next keys).1 ∧
      (internTrie t next keys).2.2 = (internMemo m next keys).2.2 ∧
      ∀ q, get (internTrie t next keys).2.1 q = (internMemo m next keys).2.1 q := by
  have hw : ∀ q, get (ensure t keys) q = m q := fun q => by rw [get_ensure, h]
  simp only [internTrie, internMemo]
  rw [hw keys]
  cases hm : m keys with
  | some id => exact ⟨rfl, rfl, hw⟩
  | none =>
    refine ⟨rfl, rfl, fun q => ?_⟩
    rw [get_set, hw]

/-- The trie assigns exactly the signature memo's ids for every sequence of shapes. -/
theorem trie_matches_memo (shapes : List (List κ)) :
    ∀ (t : Trie κ) (m : List κ → Option Nat) (next : Nat), (∀ q, get t q = m q) →
      runTrie t next shapes = runMemo m next shapes := by
  induction shapes with
  | nil => intro _ _ _ _; rfl
  | cons keys rest ih =>
    intro t m next h
    obtain ⟨h1, h2, h3⟩ := intern_step t m next keys h
    simp only [runTrie, runMemo, h1, h2]
    rw [ih _ _ _ h3]

theorem get_empty (q : List κ) : get (empty : Trie κ) q = none := by
  induction q with
  | nil => rfl
  | cons k ks ih => simpa [get, Trie.children, empty, find] using ih

theorem trie_matches_signature (shapes : List (List κ)) :
    runTrie (empty : Trie κ) 0 shapes = runMemo (fun _ => none) 0 shapes :=
  trie_matches_memo shapes empty _ 0 get_empty

/-- Ids are first-occurrence indices: equal key lists share ids, and a prefix is a distinct
shape from its extension. -/
example : runTrie (empty : Trie String) 0 [["a", "b"], ["a"], ["a", "b"], [], ["b", "a"], ["a"]] =
    [0, 1, 0, 2, 3, 1] := by decide
/-- UTF-16 code units: the lone surrogate 0xD800 and the pair 0xD83D 0xDE00 are distinct keys. -/
example : runTrie (empty : Trie (List UInt16)) 0
    [[[0xD800]], [[0xD83D, 0xDE00]], [[0xD800]], [[0xD800], [0x61]]] = [0, 1, 0, 2] := by decide

#print axioms find_update_same
#print axioms find_update_other
#print axioms get_ensure
#print axioms get_set
#print axioms intern_step
#print axioms trie_matches_memo
#print axioms get_empty
#print axioms trie_matches_signature

end SerializationShapeTrie
