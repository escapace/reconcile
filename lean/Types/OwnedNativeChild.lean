import Std

/- A feasibility witness for lazy ownership discovery, not a JS specification.
   A native carrier owner is allocated together with its fixed child before its
   source owner is known. Public output uses these native identities. -/
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

theorem mutate_keeps_identity (serialize : P → Q) (payload : P) (state : State P Q) :
    (mutate serialize payload state).child = state.child ∧
    (mutate serialize payload state).carrier = state.carrier := ⟨rfl, rfl⟩

theorem adopt_keeps_identity [DecidableEq P] (serialize : P → Q) (decode : Q → P)
    (query : Q) (state : State P Q) :
    (adopt serialize decode query state).child = state.child ∧
    (adopt serialize decode query state).carrier = state.carrier := ⟨rfl, rfl⟩

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

theorem mismatch_normalizes [DecidableEq P] (serialize : P → Q)
    (decode : Q → P) (query : Q) (state : State P Q)
    (h : decode query ≠ state.payload) :
    (adopt serialize decode query state).query = serialize state.payload := by
  simp [adopt, h]

/-- A selected owner must use the very selected child, not merely an equal child. -/
def admit (childOf : Nat → Nat) (owner child : Nat) : Bool :=
  decide (childOf owner = child)

theorem admitted_iff (childOf : Nat → Nat) (owner child : Nat) :
    admit childOf owner child = true ↔ childOf owner = child := by simp [admit]

/-- Choosing the already allocated carrier for a child satisfies the ownership edge.
    The inverse law is established by native allocation and a per-call identity map. -/
theorem carrier_satisfies (childOf carrierOf : Nat → Nat)
    (registered : ∀ child, childOf (carrierOf child) = child) (child : Nat) :
    admit childOf (carrierOf child) child = true := by simp [admit, registered]

/-- Native URL owners have distinct children; selection must not collapse them. -/
theorem admitted_distinct (childOf : Nat → Nat)
    (native : ∀ a b, childOf a = childOf b → a = b)
    (a b x y : Nat) (ha : admit childOf a x = true)
    (hb : admit childOf b y = true) (different : a ≠ b) : x ≠ y := by
  intro h
  have hx := (admitted_iff childOf a x).mp ha
  have hy := (admitted_iff childOf b y).mp hb
  exact different (native a b (hx.trans (h.trans hy.symm)))

/-- Finite fresh allocation witness. Runtime native allocation supplies freshness;
    numbering is an oracle label, not a proposal to number application objects. -/
def freshPair (next : Nat) : Nat × Nat := (next, next + 1)

theorem fresh_pair_distinct (next : Nat) : (freshPair next).1 ≠ (freshPair next).2 := by
  simp [freshPair]

theorem fresh_pair_outside (used : List Nat) (next : Nat)
    (bound : ∀ id ∈ used, id < next) :
    (freshPair next).1 ∉ used ∧ (freshPair next).2 ∉ used := by
  constructor <;> intro h
  · have := bound _ h; simp [freshPair] at this
  · have := bound _ h; simp [freshPair] at this; omega

/-- A fresh owner cannot adopt an arbitrary retained child: reject that allocation
    so the existing execution driver can try another plan. -/
theorem retained_child_rejects (childOf : Nat → Nat) (fresh : List Nat) (child : Nat)
    (cannotAttach : ∀ owner ∈ fresh, childOf owner ≠ child) (owner : Nat)
    (h : owner ∈ fresh) : admit childOf owner child = false := by
  simp [admit, cannotAttach owner h]

/-- Private construction metadata is consulted only after external memo lookup.
    Absence falls back to that exact externally selected value. -/
def constructionResponse (metadata : Nat → Option Nat) (selected : Nat) : Nat :=
  (metadata selected).getD selected

theorem response_missing (metadata : Nat → Option Nat) (selected : Nat)
    (h : metadata selected = none) : constructionResponse metadata selected = selected := by
  simp [constructionResponse, h]

theorem response_registered (metadata : Nat → Option Nat) (selected carrier : Nat)
    (h : metadata selected = some carrier) :
    constructionResponse metadata selected = carrier := by simp [constructionResponse, h]

/-- Changed owned parents force the registered child copy to survive immutable
    finalization. Discovery only accumulates force; sealed replay re-evaluates any
    child visited before its parent. -/
def forceChild (forced ownerChanged : Bool) : Bool := forced || ownerChanged

def chooseReuse (equal forced : Bool) : Bool := equal && !forced

def ownedReuseValid (ownerChanged childReused : Bool) : Bool :=
  !ownerChanged || !childReused

theorem forced_child_not_reused (equal forced : Bool) :
    chooseReuse equal (forceChild forced true) = false := by simp [chooseReuse, forceChild]

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
