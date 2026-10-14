import Mathlib.Data.List.Basic

/-!
Private deterministic cursor advancement may be delayed to a native demand.
World includes every native observation and mutation. A probe decides demand or
throws; consuming a demanded cursor can also mutate World before returning an
error. Neither native boundary is erased, reordered or memoized. An undemanded
cursor is private and deliberately absent from the observable result.

Native correspondence requires stable private keys, deterministic effect-free
cursor transitions/initialization, and preservation of the last keep result as
part of Cursor. Escaping keys or native work inside advance violate this model.
-/
namespace Reconcile.DeferredOrder

variable {Key Cursor World : Type}

inductive Command (Key : Type) where
  | advance (key : Key)
  | boundary (id : Nat)
  deriving Repr

structure Native (Cursor World : Type) where
  probe : Nat → World → World × Except Nat Bool
  consume : Nat → Cursor → World → World × Option Nat

abbrev Result (World : Type) := World × Option Nat

def eager (advance : Cursor → Key → Cursor) (native : Native Cursor World) :
    List (Command Key) → Cursor → World → Result World
  | [], _, world => (world, none)
  | .advance key :: rest, cursor, world => eager advance native rest (advance cursor key) world
  | .boundary id :: rest, cursor, world =>
    let (observed, request) := native.probe id world
    match request with
    | .error error => (observed, some error)
    | .ok false => eager advance native rest cursor observed
    | .ok true =>
      let (consumed, error) := native.consume id cursor observed
      match error with
      | some error => (consumed, some error)
      | none => eager advance native rest cursor consumed

/-- Pending keys represent a slice of the existing private previous-key array.
The runtime need not allocate this list: a monotonically advancing position suffices. -/
def deferred (advance : Cursor → Key → Cursor) (native : Native Cursor World) :
    List (Command Key) → Cursor → List Key → World → Result World
  | [], _, _, world => (world, none)
  | .advance key :: rest, cursor, pending, world =>
    deferred advance native rest cursor (pending ++ [key]) world
  | .boundary id :: rest, cursor, pending, world =>
    let (observed, request) := native.probe id world
    match request with
    | .error error => (observed, some error)
    | .ok false => deferred advance native rest cursor pending observed
    | .ok true =>
      let caughtUp := pending.foldl advance cursor
      let (consumed, error) := native.consume id caughtUp observed
      match error with
      | some error => (consumed, some error)
      | none => deferred advance native rest caughtUp [] consumed

/-- All finite native histories agree, for arbitrary stateful probes and consumers.
The invariant connects the eager state to the deferred cursor plus pending prefix. -/
theorem catchUp_eq (advance : Cursor → Key → Cursor) (native : Native Cursor World)
    (commands : List (Command Key)) (cursor : Cursor) (pending : List Key) (world : World) :
    eager advance native commands (pending.foldl advance cursor) world =
      deferred advance native commands cursor pending world := by
  induction commands generalizing cursor pending world with
  | nil => rfl
  | cons command rest ih =>
    cases command with
    | advance key =>
      simpa only [eager, deferred, List.foldl_append, List.foldl_cons, List.foldl_nil]
        using ih cursor (pending ++ [key]) world
    | boundary id =>
      simp only [eager, deferred]
      cases hp : native.probe id world with
      | mk observed request =>
        simp only [hp]
        cases request with
        | error error => rfl
        | ok needed =>
          cases needed with
          | false => exact ih cursor pending observed
          | true =>
            cases hc : native.consume id (pending.foldl advance cursor) observed with
            | mk consumed error =>
              simp only [hc]
              cases error with
              | some error => rfl
              | none => exact ih (pending.foldl advance cursor) [] consumed

theorem execute_eq (advance : Cursor → Key → Cursor) (native : Native Cursor World)
    (commands : List (Command Key)) (cursor : Cursor) (world : World) :
    eager advance native commands cursor world =
      deferred advance native commands cursor [] world :=
  catchUp_eq advance native commands cursor [] world

/-- When the ordering certificate establishes an absent cursor, every pure step
fixes that state. The helper can omit the fold, not the native continuation. -/
theorem fold_fixed (advance : Cursor → Key → Cursor) (cursor : Cursor)
    (fixed : ∀ key, advance cursor key = cursor) (keys : List Key) :
    keys.foldl advance cursor = cursor := by
  induction keys with
  | nil => rfl
  | cons key rest ih => simpa only [List.foldl_cons, fixed key] using ih

/-- Dropping pending advancement is wrong when a native continuation demands it. -/
def demanding : Native Nat (List Nat) where
  probe _ world := (world ++ [10], .ok true)
  consume _ cursor world := (world ++ [cursor], none)

example : deferred Nat.add demanding [.advance 3, .boundary 0] 2 [] [] = ([10, 5], none) := by
  decide

example : deferred Nat.add demanding [.boundary 0] 2 [] [] ≠
    eager Nat.add demanding [.advance 3, .boundary 0] 2 [] := by decide

/-- Mutation before a throw remains, and later demanding boundaries never execute. -/
def throwing : Native Nat (List Nat) where
  probe _ world := (world ++ [7], .error 9)
  consume _ cursor world := (world ++ [cursor], none)

example : deferred Nat.add throwing [.advance 3, .boundary 0, .boundary 1] 2 [] [] =
    ([7], some 9) := by decide

/-- This finite witness has no native demand; pending pure work is unobservable. -/
example : deferred Nat.add demanding [.advance 3, .advance 5] 2 [] [] = ([], none) := by decide

end Reconcile.DeferredOrder
