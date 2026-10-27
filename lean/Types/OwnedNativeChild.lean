import Types.OwnedPublication

/-! A feasibility witness for lazy ownership discovery, not a JavaScript specification. A native
carrier owner is allocated together with its fixed child before its source owner is known. Public
output uses these native identities. -/

namespace Reconcile.OwnedNativeChild

structure State (Payload Query : Type) where
  carrier : Nat
  child : Nat
  payload : Payload
  query : Query
  touched : Bool
  ownerKnown : Bool
  deriving DecidableEq

variable {P Q : Type}

def mutate (serialize : P → Q) (payload : P) (state : State P Q) : State P Q :=
  { state with payload, query := serialize payload, touched := true }

/-- Preserve the earlier child observation. A later owner's raw query spelling
    survives exactly when no child mutation occurred and its decoded payload agrees.
    Decode is private work on the already captured href, not another source read. -/
def adopt [DecidableEq P] (serialize : P → Q) (decode : Q → P)
    (sourceQuery : Q) (state : State P Q) : State P Q :=
  { state with
    query := if state.touched || decide (decode sourceQuery ≠ state.payload)
      then serialize state.payload else sourceQuery
    ownerKnown := true }

theorem adopt_consistent [DecidableEq P] (serialize : P → Q) (decode : Q → P)
    (law : ∀ payload, decode (serialize payload) = payload)
    (query : Q) (state : State P Q) :
    decode (adopt serialize decode query state).query = state.payload := by
  simp only [adopt]
  split
  · exact law _
  · rename_i h
    by_cases same : decode query = state.payload
    · exact same
    · simp [same] at h

/-- Even a value-preserving mutation changes the query branch. -/
theorem net_equal_mutation_normalizes [DecidableEq P] (serialize : P → Q)
    (decode : Q → P) (query : Q) (state : State P Q) :
    (adopt serialize decode query (mutate serialize state.payload state)).query =
      serialize state.payload := by simp [adopt, mutate]

/-- A selected owner must use the very selected child, not merely an equal child. -/
def admit (childOf : Nat → Nat) (owner child : Nat) : Bool :=
  decide (childOf owner = child)

theorem admitted_iff (childOf : Nat → Nat) (owner child : Nat) :
    admit childOf owner child = true ↔ childOf owner = child := by simp [admit]

/-- Private construction metadata is consulted only after external memo lookup.
    Absence falls back to that exact externally selected value. -/
def constructionResponse (metadata : Nat → Option Nat) (selected : Nat) : Nat :=
  (metadata selected).getD selected

/-- Changed owned parents force the registered child copy to survive immutable
    finalization. Discovery only accumulates force; sealed replay re-evaluates any
    child visited before its parent. -/
def forceChild (forced ownerChanged : Bool) : Bool := forced || ownerChanged

def chooseReuse (equal forced : Bool) : Bool := equal && !forced

def ownedReuseValid (ownerChanged childReused : Bool) : Bool :=
  !ownerChanged || !childReused

theorem replay_owned_valid (equal forced ownerChanged : Bool) :
    ownedReuseValid ownerChanged (chooseReuse equal (forceChild forced ownerChanged)) = true := by
  cases ownerChanged <;> cases equal <;> cases forced <;> rfl

theorem force_monotone (forced changed : Bool) (h : forced = true) :
    forceChild forced changed = true := by simp [forceChild, h]

-- Keeping an earlier equal-child decision after later owner discovery is unsound.
example : ownedReuseValid true (chooseReuse true false) = false := rfl
example : ownedReuseValid true (chooseReuse true (forceChild false true)) = true := rfl

/-- Try ranked immutable choices in order, skipping allocation failures before any
    fresh-write phase. Native preparation must leave prior application objects alone. -/
def firstPrepared {Choice Result : Type} (prepare : Choice → Option Result) :
    List Choice → Option Result
  | [] => none
  | choice :: rest => match prepare choice with
    | some result => some result
    | none => firstPrepared prepare rest

theorem first_prepared_ranked {Choice Result : Type} (prepare : Choice → Option Result)
    (priorChoices : List Choice) (choice : Choice) (rest : List Choice) (result : Result)
    (failed : ∀ prior ∈ priorChoices, prepare prior = none)
    (success : prepare choice = some result) :
    firstPrepared prepare (priorChoices ++ choice :: rest) = some result := by
  induction priorChoices with
  | nil => simp [firstPrepared, success]
  | cons prior tail ih =>
    have hp := failed prior (by simp)
    have ht : ∀ prior ∈ tail, prepare prior = none := by
      intro prior h
      exact failed prior (by simp [h])
    simpa [firstPrepared, hp] using ih ht

example : firstPrepared (fun n : Nat => if n = 0 then none else some n) [0, 1, 2] =
    some 1 := rfl

namespace ContractTest
example : admit (fun n => n + 1) 0 1 = true := rfl
example : admit (fun n => n + 1) 0 2 = false := rfl
example : let state : State Nat Nat := ⟨0, 1, 7, 7, false, false⟩
    (adopt id id 8 state).query = 7 := rfl
example : let state : State Nat String := ⟨0, 1, 0, "?&", false, false⟩
    (adopt (fun _ => "") (fun _ => 0) "?" state).query ≠
      (adopt (fun _ => "") (fun _ => 0) "?"
        (mutate (fun _ => "") 0 state)).query := by decide
end ContractTest

end Reconcile.OwnedNativeChild
