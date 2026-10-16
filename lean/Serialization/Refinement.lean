import Serialization.DFS

namespace SerializationV7
open SerializationDFS

inductive IndexedFrame where
  | visit : Nat → IndexedFrame
  | cursor : Nat → Nat → IndexedFrame
  deriving DecidableEq, Repr
structure IndexedConfig where
  stack : List IndexedFrame
  seen : List Nat
  deriving DecidableEq, Repr

def lowerFrame (g : Graph) : IndexedFrame → Frame
  | .visit node => .visit node
  | .cursor parent index => .resume parent index ((g parent).drop index)
def lower (g : Graph) (c : IndexedConfig) : Config :=
  ⟨c.stack.map (lowerFrame g), c.seen⟩

def indexedStep (g : Graph) (c : IndexedConfig) : Option (List Event × IndexedConfig) :=
  match c.stack with
  | [] => none
  | .visit node :: rest =>
    if node ∈ c.seen then some ([], ⟨rest, c.seen⟩)
    else some ([.enter node], ⟨.cursor node 0 :: rest, node :: c.seen⟩)
  | .cursor parent index :: rest =>
    match (g parent).drop index with
    | [] => some ([], ⟨rest, c.seen⟩)
    | child :: _ => some ([.edge parent index child],
        ⟨.visit child :: .cursor parent (index + 1) :: rest, c.seen⟩)

theorem indexed_step_exact (g : Graph) (c : IndexedConfig) :
    (indexedStep g c).map (fun (events, next) => (events, lower g next)) = step g (lower g c) := by
  rcases c with ⟨stack, seen⟩
  cases stack with
  | nil => rfl
  | cons frame rest =>
    cases frame with
    | visit node => by_cases h : node ∈ seen <;> simp [indexedStep, lower, lowerFrame, step, h]
    | cursor parent index =>
      cases h : (g parent).drop index <;>
        simp [indexedStep, lower, lowerFrame, step, h, List.drop_add_one_eq_tail_drop]

def indexedRun (g : Graph) : Nat → IndexedConfig → List Event × IndexedConfig
  | 0, c => ([], c)
  | fuel + 1, c => match indexedStep g c with
    | none => ([], c)
    | some (events, next) =>
      let (trace, final) := indexedRun g fuel next
      (events ++ trace, final)

theorem indexed_run_exact (g : Graph) (fuel : Nat) (c : IndexedConfig) :
    ((indexedRun g fuel c).1, lower g (indexedRun g fuel c).2) = run g fuel (lower g c) := by
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
    have hs := indexed_step_exact g c
    cases hi : indexedStep g c with
    | none => simp only [hi, indexedRun, run, Option.map_none] at hs ⊢; rw [← hs]
    | some pair =>
      rcases pair with ⟨events, next⟩
      simp only [hi, Option.map_some] at hs
      simp only [indexedRun, hi, run, ← hs]
      have hr := ih next
      cases hn : indexedRun g fuel next with
      | mk trace final =>
        simp only [hn] at hr ⊢
        rw [← hr]

theorem leaf_contract (g : Graph) (node : Nat) (memo : List Nat) (rest : List Frame)
    (fresh : node ∉ memo) (empty : g node = []) :
    Steps g ⟨.visit node :: rest, memo⟩ [.enter node] ⟨rest, node :: memo⟩ := by
  have enter : Steps g ⟨.visit node :: rest, memo⟩ [.enter node]
      ⟨.resume node 0 [] :: rest, node :: memo⟩ := Steps.single (by simp [step, fresh, empty])
  have finish : Steps g ⟨.resume node 0 [] :: rest, node :: memo⟩ [] ⟨rest, node :: memo⟩ :=
    Steps.single rfl
  simpa using enter.trans finish

def leafStep (g : Graph) (c : Config) : Option (List Event × Config) :=
  match c.stack with
  | .visit node :: rest =>
    if node ∉ c.seen ∧ g node = [] then some ([.enter node], ⟨rest, node :: c.seen⟩)
    else step g c
  | _ => step g c

theorem leaf_step_refines {g : Graph} {a b : Config} {events : List Event}
    (h : leafStep g a = some (events, b)) : Steps g a events b := by
  rcases a with ⟨stack, seen⟩
  cases stack with
  | nil => exact Steps.single h
  | cons frame rest =>
    cases frame with
    | resume parent index children => exact Steps.single h
    | visit node =>
      simp only [leafStep] at h
      split at h
      · rename_i hs
        cases h
        exact leaf_contract g node seen rest hs.1 hs.2
      · exact Steps.single h

def indexedValues : Nat → List Nat → List (Nat × Nat)
  | _, [] => []
  | start, value :: rest => (start, value) :: indexedValues (start + 1) rest

theorem indexedValues_append (start : Nat) (values : List Nat) (value : Nat) :
    indexedValues start (values ++ [value]) =
      indexedValues start values ++ [(start + values.length, value)] := by
  induction values generalizing start with
  | nil => simp [indexedValues]
  | cons head tail ih => simp [indexedValues, ih, Nat.add_comm, Nat.add_left_comm]

inductive Accumulator where
  | dense : List Nat → Accumulator
  | sparse : List (Nat × Nat) → Accumulator
  deriving DecidableEq, Repr

def materialize : Accumulator → List (Nat × Nat)
  | .dense values => indexedValues 0 values
  | .sparse pairs => pairs

def push (a : Accumulator) (index value : Nat) : Accumulator := match a with
  | .dense values =>
    if index = values.length then .dense (values ++ [value])
    else .sparse (indexedValues 0 values ++ [(index, value)])
  | .sparse pairs => .sparse (pairs ++ [(index, value)])

theorem push_exact (a : Accumulator) (index value : Nat) :
    materialize (push a index value) = materialize a ++ [(index, value)] := by
  cases a with
  | sparse pairs => rfl
  | dense values =>
    by_cases h : index = values.length <;>
      simp [push, materialize, h, indexedValues_append]

def accumulate : Accumulator → List (Nat × Nat) → Accumulator
  | a, [] => a
  | a, (index, value) :: rest => accumulate (push a index value) rest

theorem accumulate_exact (a : Accumulator) (pairs : List (Nat × Nat)) :
    materialize (accumulate a pairs) = materialize a ++ pairs := by
  induction pairs generalizing a with
  | nil => simp [accumulate]
  | cons pair rest ih =>
    rcases pair with ⟨index, value⟩
    simp [accumulate, ih, push_exact, List.append_assoc]

theorem array_length_exact (initial : Nat) (pairs : List (Nat × Nat)) :
    capturedLength initial ((materialize (accumulate (.dense []) pairs)).map Prod.fst) =
      capturedLength initial (pairs.map Prod.fst) := by
  rw [accumulate_exact]
  rfl

example : materialize (accumulate (.dense []) [(0, 10), (1, 20), (4, 30), (6, 40)]) =
    [(0, 10), (1, 20), (4, 30), (6, 40)] := by decide
example : (indexedRun exampleGraph 20 ⟨[.visit 0], []⟩).1 =
    [.enter 0, .edge 0 0 1, .enter 1, .edge 1 0 0, .edge 0 1 1] := by decide

#print axioms indexed_step_exact
#print axioms indexed_run_exact
#print axioms leaf_contract
#print axioms leaf_step_refines
#print axioms indexedValues_append
#print axioms push_exact
#print axioms accumulate_exact
#print axioms array_length_exact

end SerializationV7
