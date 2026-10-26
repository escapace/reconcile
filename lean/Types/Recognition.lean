/-! Recognition by ordered native predicate probes (`src/types/builtins.ts`,
`src/types/temporal.ts`): the unrolled built-in and Temporal probes select the same result, throw
at the same position and visit the same native prefix as an ordered scan, which
`scripts/recognition-scan.ts` runs as the tests' reference. -/

namespace Reconcile.Types.Recognition

-- Flags encode stable native predicate results in declared precedence order.
-- A final fallback has flag true. This does not model predicate side effects;
-- expected validation observes only the prefix through its requested rank.
def first : List Bool → Option Nat
  | [] => none
  | true :: _ => some 0
  | false :: rest => (first rest).map Nat.succ

def accepts : List Bool → Nat → Bool
  | [], _ => false
  | flag :: _, 0 => flag
  | true :: _, _ + 1 => false
  | false :: rest, rank + 1 => accepts rest rank

/-- Supplied native outcomes; a throw terminates the observed predicate prefix. -/
inductive ProbeOutcome where
  | miss
  | hit
  | raised
  deriving DecidableEq, Repr

/-- Both the selected result and the exact predicate-call prefix are observable. -/
structure ProbeTrace where
  selected : Option Nat := none
  raised : Option Nat := none
  visited : List Nat := []
  deriving DecidableEq, Repr

/-- One bounded native call, followed by its continuation only after a miss. -/
def probe (rank last : Nat) (outcome : ProbeOutcome) (rest : Unit → ProbeTrace) : ProbeTrace :=
  if rank > last then {} else
  match outcome with
  | .hit => { selected := some rank, visited := [rank] }
  | .raised => { raised := some rank, visited := [rank] }
  | .miss => let tail := rest (); { tail with visited := rank :: tail.visited }

/-- Generic ordered scan; its final fallback makes no predicate call. -/
def scanTrace (last : Nat) (rank : Nat) : List ProbeOutcome → ProbeTrace
  | [] => if rank ≤ last then { selected := some rank } else {}
  | outcome :: rest => probe rank last outcome (fun _ => scanTrace last (rank + 1) rest)

/-- Fixed built-in prefix, preserving every bounded call and exception boundary. -/
def builtinTrace (last : Nat) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 : ProbeOutcome) : ProbeTrace :=
  probe 0 last p0 fun _ =>
  probe 1 last p1 fun _ =>
  probe 2 last p2 fun _ =>
  probe 3 last p3 fun _ =>
  probe 4 last p4 fun _ =>
  probe 5 last p5 fun _ =>
  probe 6 last p6 fun _ =>
  probe 7 last p7 fun _ =>
  probe 8 last p8 fun _ =>
  probe 9 last p9 fun _ =>
  if 10 ≤ last then { selected := some 10 } else {}

/-- Unrolling changes neither selection, throw position, nor the visited native prefix. -/
theorem builtinTrace_eq_scanTrace (last : Nat) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 : ProbeOutcome) :
    builtinTrace last p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 =
      scanTrace last 0 [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9] := by
  rfl

example : scanTrace 1 0 [.miss, .raised, .hit] =
    { raised := some 1, visited := [0, 1] } := by decide

example : scanTrace 0 0 [.miss, .raised] = { visited := [0] } := by decide

example : scanTrace 2 0 [.hit, .raised] =
    { selected := some 0, visited := [0] } := by decide

/-- Eight Temporal constructor probes; unlike built-in recognition there is no fallback kind. -/
def temporalTrace (p0 p1 p2 p3 p4 p5 p6 p7 : ProbeOutcome) : ProbeTrace :=
  probe 0 7 p0 fun _ =>
  probe 1 7 p1 fun _ =>
  probe 2 7 p2 fun _ =>
  probe 3 7 p3 fun _ =>
  probe 4 7 p4 fun _ =>
  probe 5 7 p5 fun _ =>
  probe 6 7 p6 fun _ =>
  probe 7 7 p7 fun _ => {}

/-- Fixed constructor call sites retain property-get and instanceof stage ordering. -/
theorem temporalTrace_eq_scanTrace (p0 p1 p2 p3 p4 p5 p6 p7 : ProbeOutcome) :
    temporalTrace p0 p1 p2 p3 p4 p5 p6 p7 =
      scanTrace 7 0 [p0, p1, p2, p3, p4, p5, p6, p7] := by
  rfl

/-- A full traversal has no prefix cutoff test between its native probes. -/
def fullProbe (rank : Nat) (outcome : ProbeOutcome) (rest : Unit → ProbeTrace) : ProbeTrace :=
  match outcome with
  | .hit => { selected := some rank, visited := [rank] }
  | .raised => { raised := some rank, visited := [rank] }
  | .miss => let tail := rest (); { tail with visited := rank :: tail.visited }

def builtinFullTrace (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 : ProbeOutcome) : ProbeTrace :=
  fullProbe 0 p0 fun _ =>
  fullProbe 1 p1 fun _ =>
  fullProbe 2 p2 fun _ =>
  fullProbe 3 p3 fun _ =>
  fullProbe 4 p4 fun _ =>
  fullProbe 5 p5 fun _ =>
  fullProbe 6 p6 fun _ =>
  fullProbe 7 p7 fun _ =>
  fullProbe 8 p8 fun _ =>
  fullProbe 9 p9 fun _ => { selected := some 10 }

/-- Removing constant full-prefix cutoffs preserves selection and the native trace. -/
theorem builtinFullTrace_eq_scanTrace (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 : ProbeOutcome) :
    builtinFullTrace p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 =
      scanTrace 10 0 [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9] := by
  rfl

/-- A maximum-bound dispatch uses the full evaluator without changing any probe. -/
theorem builtinDispatch_eq_scanTrace (last : Nat)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 : ProbeOutcome) :
    (if last = 10 then builtinFullTrace p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
     else builtinTrace last p0 p1 p2 p3 p4 p5 p6 p7 p8 p9) =
      scanTrace last 0 [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9] := by
  split
  · rename_i h
    subst last
    exact builtinFullTrace_eq_scanTrace p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
  · exact builtinTrace_eq_scanTrace last p0 p1 p2 p3 p4 p5 p6 p7 p8 p9

end Reconcile.Types.Recognition
