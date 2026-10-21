/-!
Snapshot's native adapter writes targets during observation. Its final captured
payload is not the public result. This model isolates the erasure obligation:
a metadata-only finishing step may be omitted when every subsequent operation
uses only the live projection (targets, memo and construction answers).

The premise is essential. This does not prove that an arbitrary native type's
seal is erasable, nor refine the JavaScript traversal or model host exceptions.
Array/Map/Set discharge the premise at the adapter boundary: their construction
answer is always absent, finishing changes only captured payload, and writes have
already completed. Publication still consumes that payload and is outside scope.
-/
namespace Reconcile.SnapshotProjection

structure State (Live Metadata : Type) where
  live : Live
  metadata : Metadata

inductive Event (Live Metadata : Type) where
  | observe : (Live → Live) → Event Live Metadata
  | finish : (Metadata → Metadata) → Event Live Metadata

def step {Live Metadata : Type} (state : State Live Metadata) :
    Event Live Metadata → State Live Metadata
  | .observe update => { state with live := update state.live }
  | .finish update => { state with metadata := update state.metadata }

def projectedStep {Live Metadata : Type} (live : Live) : Event Live Metadata → Live
  | .observe update => update live
  | .finish _ => live

/-- Every finite prefix preserves the live state when metadata finishing is erased. -/
theorem erase_finishing {Live Metadata : Type} (events : List (Event Live Metadata))
    (state : State Live Metadata) :
    (events.foldl step state).live = events.foldl projectedStep state.live := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
    have h := ih (step state event)
    cases event <;> exact h

/-- Final public observations may depend on any part of live state, not metadata. -/
theorem public_result_preserved {Live Metadata Result : Type}
    (events : List (Event Live Metadata)) (state : State Live Metadata)
    (result : Live → Result) :
    result (events.foldl step state).live =
      result (events.foldl projectedStep state.live) := by
  rw [erase_finishing]

end Reconcile.SnapshotProjection
