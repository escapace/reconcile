import Mathlib.Data.List.Basic

/-! Finite property-order cursors. Keys are opaque labels with disjoint classes.
The native name offset is desired.length minus names.length; symbol suffixes
start at the first symbol (or encode the native absent-symbol sentinel).
Only classification of the private desired suffix is counted. Current-key
classification, membership and all native receiver observations remain unchanged. -/
namespace Reconcile.PropertyOrder

inductive Key where
  | index : Nat → Key
  | name : Nat → Key
  | symbol : Nat → Key
  deriving DecidableEq, BEq, Repr

structure Cursor where
  names : List Key
  symbols : List Key
  retained : Nat
  deriving DecidableEq, Repr

structure Result where
  cursor : Cursor
  kept : Bool
  checks : Nat
  deriving DecidableEq, Repr

structure CandidateResult where
  result : Result
  ready : Bool
  deriving Repr

def Stable : List Key → Prop
  | .index _ :: _ => False
  | _ => True

/-- Counts every tested desired key, including the terminating non-index test. -/
def normalize : List Key → List Key × Nat
  | [] => ([], 0)
  | .index _ :: rest =>
    let next := normalize rest
    (next.1, next.2 + 1)
  | key :: rest => (key :: rest, 1)

theorem normalize_stable (keys : List Key) : Stable (normalize keys).1 := by
  induction keys with
  | nil => trivial
  | cons key rest ih => cases key <;> simp_all [normalize, Stable]

theorem normalize_identity (keys : List Key) (h : Stable keys) :
    (normalize keys).1 = keys := by
  cases keys with
  | nil => rfl
  | cons key rest => cases key <;> simp_all [Stable, normalize]

def finishName (cursor : Cursor) (key : Key) (suffix : List Key) (checks : Nat) : Result :=
  let kept := suffix.head? == some key
  { cursor := { names := if kept then suffix.tail else suffix
                symbols := cursor.symbols
                retained := cursor.retained + if kept then 1 else 0 }
    kept := kept
    checks := checks }

def referenceStep (desired : List Key) (key : Key) (cursor : Cursor) : Result :=
  match key with
  | .index _ =>
    let kept := desired.contains key
    { cursor := { cursor with retained := cursor.retained + if kept then 1 else 0 }
      kept := kept, checks := 0 }
  | .symbol _ =>
    let kept := cursor.symbols.head? == some key
    { cursor := { cursor with
        symbols := if kept then cursor.symbols.tail else cursor.symbols
        retained := cursor.retained + if kept then 1 else 0 }
      kept := kept, checks := 0 }
  | .name _ =>
    let prepared := normalize cursor.names
    finishName cursor key prepared.1 prepared.2

def candidateStep (desired : List Key) (key : Key) (cursor : Cursor)
    (ready : Bool) : CandidateResult :=
  match key with
  | .name _ =>
    let prepared := if ready then (cursor.names, 0) else normalize cursor.names
    let result := finishName cursor key prepared.1 prepared.2
    { result := result, ready := !result.kept }
  | _ => { result := referenceStep desired key cursor, ready := ready }

/-- Native nameNeedsNormalization is the negation of ready. -/
def Valid (cursor : Cursor) (ready : Bool) : Prop :=
  ready = true → Stable cursor.names

theorem finishName_valid (cursor : Cursor) (key : Key) (suffix : List Key)
    (checks : Nat) (h : Stable suffix) :
    Valid (finishName cursor key suffix checks).cursor
      (!(finishName cursor key suffix checks).kept) := by
  simp only [Valid, finishName]
  split <;> simp_all

theorem step_equivalence (desired : List Key) (key : Key) (cursor : Cursor)
    (ready : Bool) (h : Valid cursor ready) :
    let old := referenceStep desired key cursor
    let next := candidateStep desired key cursor ready
    next.result.cursor = old.cursor ∧ next.result.kept = old.kept ∧
      next.result.checks ≤ old.checks ∧ Valid next.result.cursor next.ready := by
  cases key with
  | index label => simpa [candidateStep, referenceStep, Valid] using h
  | symbol label => simpa [candidateStep, referenceStep, Valid] using h
  | name label =>
    cases ready with
    | false =>
      simpa [candidateStep, referenceStep] using
        finishName_valid cursor (.name label) (normalize cursor.names).1
          (normalize cursor.names).2 (normalize_stable cursor.names)
    | true =>
      have hs := h rfl
      have hn := normalize_identity cursor.names hs
      have hv := finishName_valid cursor (.name label) cursor.names 0 hs
      simpa [candidateStep, referenceStep, hn, finishName] using hv

structure Run where
  keeps : List Bool
  cursor : Cursor
  checks : Nat
  deriving DecidableEq, Repr

def runReference (desired : List Key) : List Key → Cursor → Run
  | [], cursor => { keeps := [], cursor := cursor, checks := 0 }
  | key :: rest, cursor =>
    let first := referenceStep desired key cursor
    let next := runReference desired rest first.cursor
    { keeps := first.kept :: next.keeps, cursor := next.cursor,
      checks := first.checks + next.checks }

def runCandidate (desired : List Key) : List Key → Cursor → Bool → Run
  | [], cursor, _ => { keeps := [], cursor := cursor, checks := 0 }
  | key :: rest, cursor, ready =>
    let first := candidateStep desired key cursor ready
    let next := runCandidate desired rest first.result.cursor first.ready
    { keeps := first.result.kept :: next.keeps, cursor := next.cursor,
      checks := first.result.checks + next.checks }

theorem stream_equivalence (desired current : List Key) (cursor : Cursor)
    (ready : Bool) (h : Valid cursor ready) :
    (runCandidate desired current cursor ready).keeps =
        (runReference desired current cursor).keeps ∧
      (runCandidate desired current cursor ready).cursor =
        (runReference desired current cursor).cursor ∧
      (runCandidate desired current cursor ready).checks ≤
        (runReference desired current cursor).checks := by
  induction current generalizing cursor ready with
  | nil => simp [runCandidate, runReference]
  | cons key rest ih =>
    obtain ⟨hc, hk, hw, hv⟩ := step_equivalence desired key cursor ready h
    have tail := ih (candidateStep desired key cursor ready).result.cursor
      (candidateStep desired key cursor ready).ready hv
    rcases tail with ⟨tk, tc, tw⟩
    simp only [hc] at tk tc tw
    exact ⟨by simpa only [runCandidate, runReference, hc] using congrArg₂ List.cons hk tk,
      by simpa only [runCandidate, runReference, hc] using tc,
      by simpa only [runCandidate, runReference, hc] using Nat.add_le_add hw tw⟩

def initial (desired : List Key) : Cursor :=
  { names := desired
    symbols := desired.dropWhile (fun key => match key with | .symbol _ => false | _ => true)
    retained := 0 }

theorem initial_equivalence (desired current : List Key) :
    (runCandidate desired current (initial desired) false).keeps =
        (runReference desired current (initial desired)).keeps ∧
      (runCandidate desired current (initial desired) false).cursor =
        (runReference desired current (initial desired)).cursor ∧
      (runCandidate desired current (initial desired) false).checks ≤
        (runReference desired current (initial desired)).checks :=
  stream_equivalence desired current (initial desired) false (by simp [Valid])

-- Nonempty executable witnesses: repeated misses save work; numeric-only input
-- does not prepare the name cursor; later numeric positions still get skipped.
example : (runCandidate [.name 0] [.name 1, .name 1, .name 0]
    (initial [.name 0]) false).checks = 1 := by decide
example : (runReference [.name 0] [.name 1, .name 1, .name 0]
    (initial [.name 0])).checks = 3 := by decide
example : (runCandidate [.index 0, .name 0] [.index 0]
    (initial [.index 0, .name 0]) false).checks = 0 := by decide
example : (runCandidate [.name 0, .index 0, .name 1] [.name 0, .name 1]
    (initial [.name 0, .index 0, .name 1]) false).keeps = [true, true] := by decide

end Reconcile.PropertyOrder
