import Mathlib.Data.List.Basic

/-!
# Atom classification

The library treats functions and objects whose state it cannot copy (a `RegExp`, `Error`,
`WeakMap`, `WeakSet`, `WeakRef`, `FinalizationRegistry`, `Promise`, boxed primitive, `Blob` or
`SharedArrayBuffer`) as atoms: `Defs.Value.atom`, kept by reference and never traversed.
`Spec.Produce.snapshot` passes atoms through, `Spec.Reconcile` writes the next atom, and drafts
never wrap one.

An object is an atom when its prototype chain reaches one of those prototypes, which is
`instanceof` against each of their constructors at once. The runtime reads the chain once:
`Object.prototype`, `Array.prototype` and `null` end it immediately, because their chains hold
no such prototype. This module proves that the walk decides the specification and counts its
`[[GetPrototypeOf]]` calls, which a proxy can observe, and that ingress recognition splits only
the plain-object fallback into atoms, keeping every kind the structural scan selects
(`ingress_atom_iff`, `ingress_structural`).
-/

namespace Reconcile.Types.Atoms

/-- One prototype in a chain: `Object.prototype`, `Array.prototype`, a prototype the library
keeps by reference, or any other object. -/
inductive Proto where
  | object
  | array
  | listed (label : Nat)
  | data (label : Nat)
  deriving DecidableEq, Repr

def isListed : Proto → Bool
  | .listed _ => true
  | _ => false

/-- The chain from the value's prototype up to `null`. -/
abbrev Chain := List Proto

/-- `instanceof` against every listed constructor: some prototype in the chain is listed. -/
def atomic (chain : Chain) : Bool := chain.any isListed

/-- Real chains end at `Object.prototype`, whose prototype is `null`, and `Array.prototype`
inherits only from it. -/
def Standard (chain : Chain) : Prop :=
  (∀ pre post, chain = pre ++ .object :: post → post = []) ∧
  (∀ tail, chain = .array :: tail → tail = [.object])

/-- The walk continues past a prototype that is neither `Object.prototype` nor listed. -/
def walksOn (proto : Proto) : Bool := proto != .object && !isListed proto

/-- The loop after the first read: `n` reads so far; stops at `null`, `Object.prototype` or a
listed prototype. -/
def scan : Chain → Nat → Bool × Nat
  | [], n => (false, n)
  | .object :: _, n => (false, n)
  | proto :: rest, n => if isListed proto then (true, n) else scan rest (n + 1)

/-- The runtime classifier: one read of the value's prototype, an immediate answer for
`Array.prototype`, then the loop. Returns the answer and the number of reads. -/
def classify : Chain → Bool × Nat
  | .array :: _ => (false, 1)
  | chain => scan chain 1

theorem scan_reads (chain : Chain) (n : Nat) :
    (scan chain n).2 = n + (chain.takeWhile walksOn).length := by
  induction chain generalizing n with
  | nil => rfl
  | cons proto rest ih =>
    cases proto with
    | object => simp [scan, walksOn]
    | array => simp [scan, isListed, walksOn, ih]; omega
    | listed label => simp [scan, isListed, walksOn]
    | data label => simp [scan, isListed, walksOn, ih]; omega

theorem scan_atomic (chain : Chain) (n : Nat) (hstd : ∀ pre post,
    chain = pre ++ .object :: post → post = []) : (scan chain n).1 = atomic chain := by
  induction chain generalizing n with
  | nil => rfl
  | cons proto rest ih =>
    have hrest : ∀ pre post, rest = pre ++ .object :: post → post = [] := fun pre post h =>
      hstd (proto :: pre) post (by simp [h])
    cases proto with
    | object =>
      have : rest = [] := hstd [] rest rfl
      subst this
      rfl
    | array => simp [scan, isListed, atomic, ih _ hrest]
    | listed label => simp [scan, isListed, atomic]
    | data label => simp [scan, isListed, atomic, ih _ hrest]

/-- The walk decides `instanceof` against every listed constructor. -/
theorem classify_atomic (chain : Chain) (hstd : Standard chain) :
    (classify chain).1 = atomic chain := by
  match chain, hstd with
  | .array :: tail, ⟨_, harray⟩ =>
    rw [harray tail rfl]
    rfl
  | [], _ => rfl
  | .object :: tail, h => exact scan_atomic _ 1 h.1
  | .listed label :: tail, h => exact scan_atomic _ 1 h.1
  | .data label :: tail, h => exact scan_atomic _ 1 h.1

/-- Reads: one for the value, then one for each prototype the walk passes. -/
theorem classify_reads (chain : Chain) (h : chain.head? ≠ some .array) :
    (classify chain).2 = 1 + (chain.takeWhile walksOn).length := by
  match chain, h with
  | [], _ => rfl
  | .object :: tail, _ => exact scan_reads _ 1
  | .listed label :: tail, _ => exact scan_reads _ 1
  | .data label :: tail, _ => exact scan_reads _ 1
  | .array :: tail, h => exact absurd rfl h

/-- Ingress recognition: the structural scan of `Types.Recognition` selects a rank; the
plain-object fallback is then split by the walk. Known-kind checks keep the structural scan. -/
inductive Ingress where
  | structural (rank : Nat)
  | object
  | atom
  deriving DecidableEq, Repr

def ingress (fallback selected : Nat) (chain : Chain) : Ingress :=
  if selected = fallback then (if (classify chain).1 then .atom else .object)
  else .structural selected

/-- Only the fallback becomes an atom, exactly when `instanceof` holds for a listed constructor. -/
theorem ingress_atom_iff (fallback selected : Nat) (chain : Chain) (hstd : Standard chain) :
    ingress fallback selected chain = .atom ↔ selected = fallback ∧ atomic chain = true := by
  unfold ingress
  rw [← classify_atomic chain hstd]
  split_ifs with h1 h2 <;> simp_all

/-- The split never changes a kind the structural scan selected before the fallback. -/
theorem ingress_structural (fallback selected : Nat) (chain : Chain)
    (h : selected ≠ fallback) : ingress fallback selected chain = .structural selected := by
  simp [ingress, h]

-- A `TypeError` is an atom through `Error.prototype`, read on the second step.
example : classify [.data 0, .listed 1, .object] = (true, 2) := rfl
-- A `Map` subclass instance walks to `Object.prototype` and stays data.
example : classify [.data 0, .data 1, .object] = (false, 3) := rfl

end Reconcile.Types.Atoms
