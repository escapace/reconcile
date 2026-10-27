import Serialization.DFS

/-!
# In-place child tokenization (encoder traversal)

The active encoder keeps one cursor frame per entered non-leaf node. Instead of returning
to the driver loop for every child, a container tokenizes consecutive children in place and
yields only after a child was entered (its frame pushed). This file models that machine and
proves it refines the stack machine `SerializationDFS.step`, hence the recursive
specification `Recursive`, with an identical event trace.

Events are `SerializationDFS`'s `enter`/`edge` observations: `edge` stands for reading the child
slot and tokenizing it, `enter` for reserving the child's identity. A child that is already
in `seen` produces only its edge. The runtime has no visit frame: it reserves a child's identity
on discovery and captures a leaf at once (`node` in `src/serialization/emit.ts`), which is
`scan`'s `leaf` branch and refines the stack machine by `leaf_contract`
(`inline_step_refines`, given that every `leaf` node has no children).
-/

namespace SerializationInline
open SerializationDFS

structure IConfig where
  stack : List (Nat × Nat)
  seen : List Nat
  deriving DecidableEq, Repr

/-- Each in-place cursor is the existing resumable frame over the remaining children. -/
def lowerFrame (g : Graph) (f : Nat × Nat) : Frame := .resume f.1 f.2 ((g f.1).drop f.2)

def lowerI (g : Graph) (c : IConfig) : Config := ⟨c.stack.map (lowerFrame g), c.seen⟩

/-- Tokenize `children` of `parent` starting at `index` until a non-leaf child is entered or
none remain. A fresh `leaf` child (a native kind captured synchronously, without a frame) is
entered in place and the scan continues. -/
def scan (g : Graph) (leaf : Nat → Bool) (parent : Nat) :
    Nat → List Nat → List Nat → List (Nat × Nat) → List Event × IConfig
  | _, [], seen, rest => ([], ⟨rest, seen⟩)
  | index, child :: children, seen, rest =>
    if child ∈ seen then
      let r := scan g leaf parent (index + 1) children seen rest
      (.edge parent index child :: r.1, r.2)
    else if leaf child then
      let r := scan g leaf parent (index + 1) children (child :: seen) rest
      (.edge parent index child :: .enter child :: r.1, r.2)
    else ([.edge parent index child, .enter child],
      ⟨(child, 0) :: (parent, index + 1) :: rest, child :: seen⟩)

def inlineStep (g : Graph) (leaf : Nat → Bool) (c : IConfig) : Option (List Event × IConfig) :=
  match c.stack with
  | [] => none
  | (parent, index) :: rest => some (scan g leaf parent index ((g parent).drop index) c.seen rest)

theorem drop_succ_of_drop_cons {l rest : List Nat} {index child : Nat}
    (h : l.drop index = child :: rest) : l.drop (index + 1) = rest := by
  rw [List.drop_add_one_eq_tail_drop, h]
  rfl

theorem scan_refines (g : Graph) (leaf : Nat → Bool) (hleaf : ∀ n, leaf n → g n = [])
    (parent : Nat) (rest : List (Nat × Nat)) :
    ∀ (children : List Nat) (index : Nat) (seen : List Nat),
      (g parent).drop index = children →
      Steps g ⟨.resume parent index children :: rest.map (lowerFrame g), seen⟩
        (scan g leaf parent index children seen rest).1
        (lowerI g (scan g leaf parent index children seen rest).2) := by
  intro children
  induction children with
  | nil =>
    intro index seen _
    exact Steps.single rfl
  | cons child children ih =>
    intro index seen hd
    have hnext := drop_succ_of_drop_cons hd
    have edge : Steps g ⟨.resume parent index (child :: children) :: rest.map (lowerFrame g), seen⟩
        [.edge parent index child]
        ⟨.visit child :: .resume parent (index + 1) children :: rest.map (lowerFrame g), seen⟩ :=
      Steps.single rfl
    by_cases hs : child ∈ seen
    · have skip : Steps g
          ⟨.visit child :: .resume parent (index + 1) children :: rest.map (lowerFrame g), seen⟩ []
          ⟨.resume parent (index + 1) children :: rest.map (lowerFrame g), seen⟩ :=
        Steps.single (by simp [step, hs])
      have tail := ih (index + 1) seen hnext
      simpa [scan, hs] using edge.trans (skip.trans tail)
    · by_cases hl : leaf child
      · have captured := leaf_contract g child seen
          (.resume parent (index + 1) children :: rest.map (lowerFrame g)) hs (hleaf child hl)
        have tail := ih (index + 1) (child :: seen) hnext
        simpa [scan, hs, hl] using edge.trans (captured.trans tail)
      · have enter : Steps g
            ⟨.visit child :: .resume parent (index + 1) children :: rest.map (lowerFrame g), seen⟩
            [.enter child]
            ⟨.resume child 0 (g child) :: .resume parent (index + 1) children ::
              rest.map (lowerFrame g), child :: seen⟩ :=
          Steps.single (by simp [step, hs])
        have whole := edge.trans enter
        simpa [scan, hs, hl, lowerI, lowerFrame, hnext] using whole

theorem inline_step_refines {g : Graph} {leaf : Nat → Bool} (hleaf : ∀ n, leaf n → g n = [])
    {c c' : IConfig} {events : List Event}
    (h : inlineStep g leaf c = some (events, c')) : Steps g (lowerI g c) events (lowerI g c') := by
  rcases c with ⟨stack, seen⟩
  cases stack with
  | nil => simp [inlineStep] at h
  | cons frame rest =>
    rcases frame with ⟨parent, index⟩
    simp only [inlineStep, Option.some.injEq] at h
    have r := scan_refines g leaf hleaf parent rest ((g parent).drop index) index seen rfl
    rw [h] at r
    simpa [lowerI, lowerFrame] using r

def inlineRun (g : Graph) (leaf : Nat → Bool) : Nat → IConfig → List Event × IConfig
  | 0, c => ([], c)
  | fuel + 1, c => match inlineStep g leaf c with
    | none => ([], c)
    | some (events, next) =>
      let r := inlineRun g leaf fuel next
      (events ++ r.1, r.2)

theorem inline_run_refines (g : Graph) (leaf : Nat → Bool) (hleaf : ∀ n, leaf n → g n = [])
    (fuel : Nat) (c : IConfig) :
    Steps g (lowerI g c) (inlineRun g leaf fuel c).1 (lowerI g (inlineRun g leaf fuel c).2) := by
  induction fuel generalizing c with
  | zero => exact Steps.done _
  | succ fuel ih =>
    cases h : inlineStep g leaf c with
    | none => simpa [inlineRun, h] using Steps.done (lowerI g c)
    | some pair =>
      rcases pair with ⟨events, next⟩
      simpa [inlineRun, h] using (inline_step_refines hleaf h).trans (ih next)

/-- Tokenizing a fresh root enters it and pushes its cursor; a seen or primitive root does not. -/
def start (root : Nat) : List Event × IConfig := ([.enter root], ⟨[(root, 0)], [root]⟩)

theorem start_refines (g : Graph) (root : Nat) :
    Steps g ⟨[.visit root], []⟩ (start root).1 (lowerI g (start root).2) :=
  Steps.single (by simp [step, start, lowerI, lowerFrame])

/-- The stack machine is deterministic, so runs to an empty stack have one trace and result. -/
theorem steps_terminal_unique {g : Graph} {a b₁ b₂ : Config} {t₁ t₂ : List Event}
    (h₁ : Steps g a t₁ b₁) (h₂ : Steps g a t₂ b₂) (e₁ : b₁.stack = []) (e₂ : b₂.stack = []) :
    t₁ = t₂ ∧ b₁ = b₂ := by
  induction h₁ generalizing t₂ with
  | done c =>
    cases h₂ with
    | done => exact ⟨rfl, rfl⟩
    | next hs _ =>
      rcases c with ⟨stack, seen⟩
      cases stack <;> simp_all [step]
  | next hs _ ih =>
    cases h₂ with
    | done =>
      rename_i a _ _ _ _
      rcases a with ⟨stack, seen⟩
      cases stack <;> simp_all [step]
    | next hs' rest' =>
      rw [hs] at hs'
      simp only [Option.some.injEq, Prod.mk.injEq] at hs'
      obtain ⟨rfl, rfl⟩ := hs'
      obtain ⟨ht, hb⟩ := ih rest' e₁
      exact ⟨by rw [ht], hb⟩

/-- A terminating in-place run from a fresh root has exactly the recursive specification's
trace and memo. -/
theorem inline_matches_recursive {g : Graph} {leaf : Nat → Bool}
    (hleaf : ∀ n, leaf n → g n = []) {root fuel : Nat} {trace : List Event}
    {final : List Nat} (spec : Recursive g (.visit root) [] trace final)
    (done : (inlineRun g leaf fuel (start root).2).2.stack = []) :
    (start root).1 ++ (inlineRun g leaf fuel (start root).2).1 = trace ∧
      (inlineRun g leaf fuel (start root).2).2.seen = final := by
  have hs := recursive_refines_stack spec []
  have hi := (start_refines g root).trans (inline_run_refines g leaf hleaf fuel (start root).2)
  have u := steps_terminal_unique hi hs (by simp [lowerI, done]) rfl
  refine ⟨u.1, ?_⟩
  have := congrArg Config.seen u.2
  simpa [lowerI] using this

example : (inlineRun exampleGraph (fun _ => false) 20 (start 0).2).1 =
    [.edge 0 0 1, .enter 1, .edge 1 0 0, .edge 0 1 1] := by decide
example : (start 0).1 ++ (inlineRun exampleGraph (fun _ => false) 20 (start 0).2).1 =
    (run exampleGraph 20 ⟨[.visit 0], []⟩).1 := by decide
/-- Node 0 has children 1, 2, 1; node 2 is a childless leaf entered in place. -/
def leafGraph : Graph := fun n => if n = 0 then [1, 2, 1] else if n = 1 then [2] else []
example : (start 0).1 ++ (inlineRun leafGraph (· = 2) 20 (start 0).2).1 =
    (run leafGraph 20 ⟨[.visit 0], []⟩).1 := by decide
example : (inlineRun leafGraph (· = 2) 20 (start 0).2).2.stack = [] := by decide

end SerializationInline
