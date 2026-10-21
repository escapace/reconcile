/-!
Immutable compilation reserves one fresh label for each node before interning
native identities. Reserving the whole range and using node indices removes an
intermediate label array. This finite model proves exact labels and the next free
label agree; it does not model JavaScript arrays, allocation costs or native reads.
-/
namespace Reconcile.ImmutableLabels

def repeated : Nat → Nat → List Nat × Nat
  | 0, start => ([], start)
  | count + 1, start =>
    let rest := repeated count (start + 1)
    (start :: rest.1, rest.2)

def block (count start : Nat) : List Nat × Nat :=
  (List.range' start count, start + count)

theorem repeated_eq_block (count start : Nat) :
    repeated count start = block count start := by
  induction count generalizing start with
  | zero => simp [repeated, block]
  | succ count ih =>
    simp [repeated, ih, block, List.range', Nat.add_comm, Nat.add_left_comm]

theorem initial_labels (count : Nat) :
    (repeated count 0).1 = List.range count := by
  rw [repeated_eq_block]
  simp [block, List.range_eq_range']

theorem next_free (count start : Nat) :
    (repeated count start).2 = start + count := by
  rw [repeated_eq_block]
  rfl

theorem fresh_below_native (count index native : Nat)
    (fresh : index < count) (interned : count ≤ native) : index ≠ native := by
  omega

end Reconcile.ImmutableLabels
