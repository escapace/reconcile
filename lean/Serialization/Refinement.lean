import Serialization.DFS

/-! Refinements of the `SerializationDFS` stack machine: index-cursor frames that step exactly as
the list-suffix frames (`indexed_step_exact`), and a leaf step for a node without children
(`leaf_step_refines`), as in `src/serialization/frames.ts` and `leaf.ts`. -/

namespace SerializationRefinement
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

example : (indexedRun exampleGraph 20 ⟨[.visit 0], []⟩).1 =
    [.enter 0, .edge 0 0 1, .enter 1, .edge 1 0 0, .edge 0 1 1] := by decide

end SerializationRefinement
