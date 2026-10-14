import Mathlib.Data.List.Basic

/-!
A bounded model of Map's incremental snapshot writes. Edges are opaque reference
tokens, not resolved native values. The emitter receives a complete pair only when
the value edge arrives. It may update an arbitrary live state, including a target
image and an observation trace. No JavaScript object or iterator semantics appear.

This justifies the current pending-key writer without retained edge history.
Native adapters must still preserve intervening child observations, memo timing,
construction inputs and property behavior. It is not full snapshot refinement.
-/
namespace Reconcile.SnapshotStream

/-- The complete pairs represented by a captured edge prefix. A trailing key has
no write yet, matching the snapshot writer's pair boundary. -/
def pairs {Edge : Type} : List Edge → List (Edge × Edge)
  | key :: value :: rest => (key, value) :: pairs rest
  | _ => []

/-- An incremental writer stores at most one unresolved edge. -/
def run {Edge State : Type} (emit : State → Edge → Edge → State)
    (pending : Option Edge) (state : State) : List Edge → State
  | [] => state
  | edge :: rest =>
    match pending with
    | none => run emit (some edge) state rest
    | some key => run emit none (emit state key edge) rest

/-- Incremental writes have exactly the same order and state transitions as
writing complete adjacent pairs from the retained history. -/
theorem run_eq_pairs {Edge State : Type} (emit : State → Edge → Edge → State)
    (state : State) (edges : List Edge) :
    run emit none state edges =
      (pairs edges).foldl (fun state pair => emit state pair.1 pair.2) state := by
  match edges with
  | [] => rfl
  | [_] => rfl
  | key :: value :: rest =>
    simpa [run, pairs] using run_eq_pairs emit (emit state key value) rest

/-- Every observable prefix agrees, not merely the final graph. -/
theorem prefix_agreement {Edge State : Type} (emit : State → Edge → Edge → State)
    (state : State) (edges : List Edge) (count : Nat) :
    run emit none state (edges.take count) =
      (pairs (edges.take count)).foldl (fun state pair => emit state pair.1 pair.2) state :=
  run_eq_pairs emit state (edges.take count)

/-- A key-only prefix performs no resolution or native insertion. -/
theorem pending_key_no_write {Edge State : Type} (emit : State → Edge → Edge → State)
    (state : State) (key : Edge) : run emit none state [key] = state := rfl


/-- The retained history's unmatched last edge, if its length is odd. -/
def pending {Edge : Type} : List Edge → Option Edge
  | [] => none
  | [key] => some key
  | _ :: _ :: rest => pending rest

theorem pending_append {Edge : Type} (edges : List Edge) (edge : Edge) :
    pending (edges ++ [edge]) =
      match pending edges with
      | none => some edge
      | some _ => none := by
  match edges with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: rest => simpa [pending] using pending_append rest edge

inductive Event (Edge State : Type) where
  | edge : Edge → Event Edge State
  | effect : (State → State) → Event Edge State

structure History (Edge State : Type) where
  edges : List Edge
  live : State

structure Writer (Edge State : Type) where
  key : Option Edge
  live : State

def project {Edge State : Type} (history : History Edge State) : Writer Edge State :=
  ⟨pending history.edges, history.live⟩

def historyStep {Edge State : Type} (emit : State → Edge → Edge → State)
    (history : History Edge State) : Event Edge State → History Edge State
  | .effect update => { history with live := update history.live }
  | .edge edge =>
    ⟨history.edges ++ [edge], match pending history.edges with
      | none => history.live
      | some key => emit history.live key edge⟩

def writerStep {Edge State : Type} (emit : State → Edge → Edge → State)
    (writer : Writer Edge State) : Event Edge State → Writer Edge State
  | .effect update => { writer with live := update writer.live }
  | .edge edge =>
    match writer.key with
    | none => ⟨some edge, writer.live⟩
    | some key => ⟨none, emit writer.live key edge⟩

/-- Projection commutes with each edge or intervening child-state update. -/
theorem step_agreement {Edge State : Type} (emit : State → Edge → Edge → State)
    (history : History Edge State) (event : Event Edge State) :
    project (historyStep emit history event) = writerStep emit (project history) event := by
  cases event with
  | effect update => rfl
  | edge edge =>
    simp only [project, historyStep, writerStep, pending_append]
    cases pending history.edges <;> rfl

/-- Complete writer state agrees after every finite interleaving of edges and
child effects. Reference resolution can inspect the live image at emission time. -/
theorem interleaved_agreement {Edge State : Type} (emit : State → Edge → Edge → State)
    (history : History Edge State) (events : List (Event Edge State)) :
    project (events.foldl (historyStep emit) history) =
      events.foldl (writerStep emit) (project history) := by
  induction events generalizing history with
  | nil => rfl
  | cons event rest ih =>
    simp only [List.foldl]
    rw [ih, step_agreement]

end Reconcile.SnapshotStream
