/-! Bulk owned-child publication. Native correspondence must establish that clearing a nonempty
URL parameter list has the same context effect as `URL.search = ""`; appending to the empty list
preserves that context and serializes the new list. Context includes opaque-path normalization.
Equal payloads perform no mutation. -/

namespace Reconcile.OwnedPublication

structure State (E Q C : Type) where
  owner : Nat
  child : Nat
  payload : List E
  query : Q
  context : C
  deriving DecidableEq

variable {E Q C : Type}

def appendOne (serialize : List E → Q) (entry : E) (state : State E Q C) : State E Q C :=
  { state with payload := state.payload ++ [entry], query := serialize (state.payload ++ [entry]) }

def appendMany (serialize : List E → Q) (entries : List E) (state : State E Q C) : State E Q C :=
  entries.foldl (fun current entry => appendOne serialize entry current) state

theorem append_many (serialize : List E → Q) (entries : List E) (state : State E Q C) :
    appendMany serialize entries state =
      { state with
        payload := state.payload ++ entries
        query := if entries.isEmpty then state.query else serialize (state.payload ++ entries) } := by
  induction entries generalizing state with
  | nil => simp [appendMany]
  | cons entry rest ih =>
    simp only [appendMany, List.foldl_cons]
    rw [show List.foldl (fun current entry => appendOne serialize entry current)
      (appendOne serialize entry state) rest = appendMany serialize rest
      (appendOne serialize entry state) from rfl, ih]
    cases rest <;> simp [appendOne, List.append_assoc]

def clear (serialize : List E → Q) (normalize : C → C) (state : State E Q C) : State E Q C :=
  if state.payload.isEmpty then state
  else { state with payload := [], query := serialize [], context := normalize state.context }

def sequential (serialize : List E → Q) (normalize : C → C) (entries : List E)
    (state : State E Q C) : State E Q C :=
  appendMany serialize entries (clear serialize normalize state)

def bulk (serialize : List E → Q) (normalize : C → C) (entries : List E)
    (state : State E Q C) : State E Q C :=
  let cleared := clear serialize normalize state
  { cleared with
    payload := entries
    query := if entries.isEmpty then cleared.query else serialize entries }

theorem clear_empty (serialize : List E → Q) (normalize : C → C) (state : State E Q C) :
    (clear serialize normalize state).payload = [] := by
  unfold clear
  split
  · rename_i h
    simpa using List.isEmpty_iff.mp h
  · rfl

theorem bulk_equivalent (serialize : List E → Q) (normalize : C → C) (entries : List E)
    (state : State E Q C) :
    bulk serialize normalize entries state = sequential serialize normalize entries state := by
  simp [bulk, sequential, append_many, clear_empty]

theorem bulk_identity (serialize : List E → Q) (normalize : C → C) (entries : List E)
    (state : State E Q C) :
    (bulk serialize normalize entries state).owner = state.owner ∧
    (bulk serialize normalize entries state).child = state.child := by
  simp [bulk, clear]; split <;> exact ⟨rfl, rfl⟩

/-- Sealed construction edges justify lookup; no native observation is repeated. -/
theorem sealed_owner_sound (childOf : Nat → Nat) (edges : List (Nat × Nat))
    (valid : ∀ edge ∈ edges, childOf edge.1 = edge.2)
    (owner child : Nat) (found : (owner, child) ∈ edges) : childOf owner = child :=
  valid (owner, child) found

-- Directly assigning the final query without clearing can retain an opaque path
-- that sequential native mutation normalizes. The clear phase cannot be dropped.
example : let state : State Nat (List Nat) Bool := ⟨0, 1, [1], [1], true⟩
    (bulk id (fun _ => false) [2] state).context ≠ state.context := by decide

end Reconcile.OwnedPublication
