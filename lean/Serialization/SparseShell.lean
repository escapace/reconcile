import Serialization.Reconstruction

/-! A private fresh array shell: install a configurable temporary index, resize,
delete that index, and only then publish/fill. Native allocation and heap layout
are correspondence obligations; this model proves observable finite state. -/
namespace SerializationSparseShell
open SerializationV9

structure Flags where
  writable : Bool
  enumerable : Bool
  configurable : Bool
  deriving DecidableEq

structure Data (α : Type) where
  value : α
  flags : Flags

def dataFlags : Flags := ⟨true, true, true⟩
def lengthFlags : Flags := ⟨true, false, false⟩
def temporaryFlags : Flags := ⟨false, false, true⟩

structure Shell (Handle α : Type) where
  handle : Handle
  elements : Sparse (Data α)
  lengthAttributes : Flags

def empty {Handle α : Type} (handle : Handle) (length : Nat) : Shell Handle α :=
  ⟨handle, allocatedSparse length, lengthFlags⟩

-- Defining index zero on a fresh empty array raises its length to one.
def seed {Handle α : Type} (handle : Handle) (temporary : α) : Shell Handle α :=
  ⟨handle, ⟨1, fun i => if i = 0 then some ⟨temporary, temporaryFlags⟩ else none⟩,
    lengthFlags⟩

def resizeShell {Handle α : Type} (shell : Shell Handle α) (length : Nat) : Shell Handle α :=
  { shell with elements := resize shell.elements length }

-- Failed deletion is represented explicitly: arbitrary nonconfigurable entries
-- cannot be erased by this operation.
def deleteZero {Handle α : Type} (shell : Shell Handle α) : Option (Shell Handle α) :=
  let erase := some { shell with elements :=
    ⟨shell.elements.length, fun i => if i = 0 then none else shell.elements.slot i⟩ }
  match shell.elements.slot 0 with
  | none => erase
  | some value => if value.flags.configurable then erase else none

def prepare {Handle α : Type} (handle : Handle) (temporary : α) (length : Nat) :
    Option (Shell Handle α) :=
  if length ≤ 4294967295 then deleteZero (resizeShell (seed handle temporary) length) else none

theorem erase_resized_seed {Handle α : Type} (handle : Handle) (temporary : α) (length : Nat) :
    deleteZero (resizeShell (seed handle temporary) length) = some (empty handle length) := by
  cases length with
  | zero => simp [deleteZero, resizeShell, seed, resize, empty, allocatedSparse]
  | succ n =>
    suffices h : (fun i => if i = 0 then none else
        if i < n + 1 then
          if i = 0 then some (Data.mk temporary temporaryFlags) else none
        else none) = (fun _ => none) by
      simpa [deleteZero, resizeShell, seed, resize, temporaryFlags, empty, allocatedSparse] using h
    funext i
    by_cases h : i = 0 <;> simp [h]

theorem prepare_exact {Handle α : Type} (handle : Handle) (temporary : α) (length : Nat)
    (valid : length ≤ 4294967295) : prepare handle temporary length = some (empty handle length) := by
  simp only [prepare, if_pos valid, erase_resized_seed]

theorem invalid_length_rejected {Handle α : Type} (handle : Handle) (temporary : α) (length : Nat)
    (invalid : ¬ length ≤ 4294967295) : prepare handle temporary length = none := by
  simp only [prepare, if_neg invalid]

theorem zero_boundary {Handle α : Type} (handle : Handle) (temporary : α) :
    prepare handle temporary 0 = some (empty handle 0) := prepare_exact handle temporary 0 (by decide)

def fillShell {Handle α : Type} (shell : Shell Handle α) (pairs : List (Nat × α)) :
    Option (Shell Handle α) :=
  (fill shell.elements (pairs.map fun (index, value) => (index, Data.mk value dataFlags))).map
    fun entries => { shell with elements := entries }

theorem prepared_fill_exact {Handle α : Type} (handle : Handle) (temporary : α) (length : Nat)
    (pairs : List (Nat × α)) (valid : length ≤ 4294967295) :
    (prepare handle temporary length).bind (fun shell => fillShell shell pairs) =
      fillShell (empty handle length) pairs := by
  rw [prepare_exact handle temporary length valid]
  rfl

theorem fill_handle {Handle α : Type} (shell result : Shell Handle α) (pairs : List (Nat × α))
    (filled : fillShell shell pairs = some result) : result.handle = shell.handle := by
  unfold fillShell at filled
  cases h : fill shell.elements (pairs.map fun (index, value) => (index, Data.mk value dataFlags)) with
  | none => simp [h] at filled
  | some entries => simp only [h, Option.map_some, Option.some.injEq] at filled; cases filled; rfl

theorem empty_observations {Handle α : Type} (handle : Handle) (length index : Nat) :
    (empty (α := α) handle length).handle = handle ∧
    (empty (α := α) handle length).elements.length = length ∧
    (empty (α := α) handle length).elements.slot index = none ∧
    (empty (α := α) handle length).lengthAttributes = lengthFlags := by
  exact ⟨rfl, rfl, rfl, rfl⟩

-- A present undefined-like value and a hole remain different after filling.
example : (fillShell (empty (α := Option Nat) 7 3) [(1, none)]).map
    (fun shell => (shell.handle, shell.elements.length,
      (shell.elements.slot 1).map Data.value, shell.elements.slot 0 |>.isNone)) =
      some (7, 3, some none, true) := by decide

-- Competing construction: a default data descriptor at the final index sets
-- the requested length, then configurable deletion leaves an empty shell.
def deleteAt {Handle α : Type} (shell : Shell Handle α) (index : Nat) : Option (Shell Handle α) :=
  let erase := some { shell with elements :=
    ⟨shell.elements.length, fun i => if i = index then none else shell.elements.slot i⟩ }
  match shell.elements.slot index with
  | none => erase
  | some value => if value.flags.configurable then erase else none

def lastSeed {Handle α : Type} (handle : Handle) (temporary : α) (index : Nat) : Shell Handle α :=
  ⟨handle, ⟨index + 1, fun i => if i = index then some ⟨temporary, dataFlags⟩ else none⟩,
    lengthFlags⟩

def prepareLast {Handle α : Type} (handle : Handle) (temporary : α) (length : Nat) :
    Option (Shell Handle α) :=
  if length ≤ 4294967295 then
    match length with
    | 0 => some (empty handle 0)
    | index + 1 => deleteAt (lastSeed handle temporary index) index
  else none

theorem erase_last_seed {Handle α : Type} (handle : Handle) (temporary : α) (index : Nat) :
    deleteAt (lastSeed handle temporary index) index = some (empty handle (index + 1)) := by
  suffices h : (fun i => if i = index then none else
      if i = index then some (Data.mk temporary dataFlags) else none) = (fun _ => none) by
    simpa [deleteAt, lastSeed, dataFlags, empty, allocatedSparse] using h
  funext i
  by_cases h : i = index <;> simp [h]

theorem prepareLast_exact {Handle α : Type} (handle : Handle) (temporary : α) (length : Nat)
    (valid : length ≤ 4294967295) :
    prepareLast handle temporary length = some (empty handle length) := by
  cases length with
  | zero => simp [prepareLast, empty]
  | succ index => simp only [prepareLast, if_pos valid, erase_last_seed]

theorem alternatives_equal {Handle α : Type} (handle : Handle) (temporary : α) (length : Nat)
    (valid : length ≤ 4294967295) :
    prepareLast handle temporary length = prepare handle temporary length := by
  rw [prepareLast_exact handle temporary length valid, prepare_exact handle temporary length valid]

theorem last_fill_exact {Handle α : Type} (handle : Handle) (temporary : α) (length : Nat)
    (pairs : List (Nat × α)) (valid : length ≤ 4294967295) :
    (prepareLast handle temporary length).bind (fun shell => fillShell shell pairs) =
      fillShell (empty handle length) pairs := by
  rw [prepareLast_exact handle temporary length valid]
  rfl

-- Known dense callers may retain ordinary allocation. Unknown occupancy uses
-- the proved sparse constructor; the choice changes no finite shell state.
def selectShell {Handle α : Type} (knownDense : Bool) (handle : Handle) (temporary : α)
    (length : Nat) : Option (Shell Handle α) :=
  if knownDense then some (empty handle length) else prepareLast handle temporary length

theorem selected_shell_exact {Handle α : Type} (knownDense : Bool) (handle : Handle)
    (temporary : α) (length : Nat) (valid : length ≤ 4294967295) :
    selectShell knownDense handle temporary length = some (empty handle length) := by
  cases knownDense <;> simp [selectShell, prepareLast_exact handle temporary length valid]

-- Codec-only alternative: the temporary descriptor is always at the maximum
-- valid array index. Delete it BEFORE assigning the requested final length.
def prepareMax {Handle α : Type} (handle : Handle) (temporary : α) (length : Nat) :
    Option (Shell Handle α) :=
  if length ≤ 4294967295 then
    (deleteAt (lastSeed handle temporary 4294967294) 4294967294).map
      (fun shell => resizeShell shell length)
  else none

theorem resize_empty_shell {Handle α : Type} (handle : Handle) (oldLength length : Nat) :
    resizeShell (empty (α := α) handle oldLength) length = empty handle length := by
  simp [resizeShell, empty, resize, allocatedSparse]

theorem prepareMax_exact {Handle α : Type} (handle : Handle) (temporary : α) (length : Nat)
    (valid : length ≤ 4294967295) :
    prepareMax handle temporary length = some (empty handle length) := by
  simp only [prepareMax, if_pos valid, erase_last_seed, Option.map_some, resize_empty_shell]

theorem max_matches_last {Handle α : Type} (handle : Handle) (temporary : α) (length : Nat)
    (valid : length ≤ 4294967295) :
    prepareMax handle temporary length = prepareLast handle temporary length := by
  rw [prepareMax_exact handle temporary length valid, prepareLast_exact handle temporary length valid]

theorem max_fill_exact {Handle α : Type} (handle : Handle) (temporary : α) (length : Nat)
    (pairs : List (Nat × α)) (valid : length ≤ 4294967295) :
    (prepareMax handle temporary length).bind (fun shell => fillShell shell pairs) =
      fillShell (empty handle length) pairs := by
  rw [prepareMax_exact handle temporary length valid]
  rfl

theorem max_boundaries {Handle α : Type} (handle : Handle) (temporary : α) :
    prepareMax handle temporary 0 = some (empty handle 0) ∧
    prepareMax handle temporary 4294967295 = some (empty handle 4294967295) := by
  exact ⟨prepareMax_exact handle temporary 0 (by decide),
    prepareMax_exact handle temporary 4294967295 (by decide)⟩

#print axioms resize_empty_shell
#print axioms prepareMax_exact
#print axioms max_matches_last
#print axioms max_fill_exact
#print axioms max_boundaries
#print axioms selected_shell_exact
#print axioms erase_last_seed
#print axioms prepareLast_exact
#print axioms alternatives_equal
#print axioms last_fill_exact
#print axioms erase_resized_seed
#print axioms prepare_exact
#print axioms invalid_length_rejected
#print axioms zero_boundary
#print axioms prepared_fill_exact
#print axioms fill_handle
#print axioms empty_observations
end SerializationSparseShell
