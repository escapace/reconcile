import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Nodup

namespace SerializationDFS

abbrev Graph := Nat → List Nat
inductive Frame where
  | visit : Nat → Frame
  | resume : Nat → Nat → List Nat → Frame
  deriving DecidableEq, Repr
inductive Event where
  | enter : Nat → Event
  | edge : Nat → Nat → Nat → Event
  deriving DecidableEq, Repr
structure Config where
  stack : List Frame
  seen : List Nat
  deriving DecidableEq, Repr

-- The unseen node is marked BEFORE its first suspended iterator frame executes.
def step (g : Graph) (c : Config) : Option (List Event × Config) :=
  match c.stack with
  | [] => none
  | .visit node :: rest =>
    if node ∈ c.seen then some ([], ⟨rest, c.seen⟩)
    else some ([.enter node], ⟨.resume node 0 (g node) :: rest, node :: c.seen⟩)
  | .resume _ _ [] :: rest => some ([], ⟨rest, c.seen⟩)
  | .resume parent index (child :: children) :: rest =>
    some ([.edge parent index child],
      ⟨.visit child :: .resume parent (index + 1) children :: rest, c.seen⟩)

inductive Steps (g : Graph) : Config → List Event → Config → Prop where
  | done (c) : Steps g c [] c
  | next {a b c events trace} : step g a = some (events, b) →
      Steps g b trace c → Steps g a (events ++ trace) c

theorem Steps.single {g : Graph} {a b : Config} {events : List Event}
    (h : step g a = some (events, b)) : Steps g a events b := by
  simpa using Steps.next h (Steps.done b)

theorem Steps.trans {g : Graph} {a b c : Config} {left right : List Event}
    (h : Steps g a left b) (j : Steps g b right c) : Steps g a (left ++ right) c := by
  induction h with
  | done => simpa using j
  | next hs _ ih => simpa [List.append_assoc] using Steps.next hs (ih j)

-- Independent recursive specification: a child's entire recursive traversal precedes
-- recursion over the remainder of its parent's ordered adjacency list.
inductive Recursive (g : Graph) : Frame → List Nat → List Event → List Nat → Prop where
  | seen {node memo} : node ∈ memo → Recursive g (.visit node) memo [] memo
  | fresh {node memo trace final} : node ∉ memo →
      Recursive g (.resume node 0 (g node)) (node :: memo) trace final →
      Recursive g (.visit node) memo (.enter node :: trace) final
  | empty {parent index memo} : Recursive g (.resume parent index []) memo [] memo
  | child {parent index node children memo middle final first second} :
      Recursive g (.visit node) memo first middle →
      Recursive g (.resume parent (index + 1) children) middle second final →
      Recursive g (.resume parent index (node :: children)) memo
        (.edge parent index node :: (first ++ second)) final

theorem recursive_refines_stack {g : Graph} {frame : Frame} {memo final : List Nat}
    {trace : List Event} (h : Recursive g frame memo trace final) (continuation : List Frame) :
    Steps g ⟨frame :: continuation, memo⟩ trace ⟨continuation, final⟩ := by
  induction h generalizing continuation with
  | seen hm =>
    apply Steps.single
    simp [step, hm]
  | @fresh node memo trace final hm _ ih =>
    have first : Steps g ⟨.visit node :: continuation, memo⟩ [.enter node]
        ⟨.resume node 0 (g node) :: continuation, node :: memo⟩ :=
      Steps.single (by simp [step, hm])
    simpa using first.trans (ih continuation)
  | empty =>
    apply Steps.single
    rfl
  | @child parent index node children memo middle final left right hchild hrest ihchild ihrest =>
    have first : Steps g ⟨.resume parent index (node :: children) :: continuation, memo⟩
        [.edge parent index node]
        ⟨.visit node :: .resume parent (index + 1) children :: continuation, memo⟩ :=
      Steps.single rfl
    simpa [List.append_assoc] using first.trans
      ((ihchild (.resume parent (index + 1) children :: continuation)).trans (ihrest continuation))

theorem step_seen_nodup {g : Graph} {a b : Config} {events : List Event}
    (h : step g a = some (events, b)) (hn : a.seen.Nodup) : b.seen.Nodup := by
  rcases a with ⟨stack, seen⟩
  cases stack with
  | nil => simp [step] at h
  | cons frame rest =>
    cases frame with
    | visit node =>
      simp only [step] at h
      split at h <;> cases h <;> simp_all [List.nodup_cons]
    | resume parent index children =>
      cases children <;> simp only [step] at h <;> cases h <;> exact hn

theorem steps_seen_nodup {g : Graph} {a b : Config} {events : List Event}
    (h : Steps g a events b) (hn : a.seen.Nodup) : b.seen.Nodup := by
  induction h with
  | done => exact hn
  | next hs _ ih => exact ih (step_seen_nodup hs hn)

def entered : List Event → List Nat
  | [] => []
  | .enter node :: es => node :: entered es
  | .edge _ _ _ :: es => entered es

theorem entered_append (a b : List Event) : entered (a ++ b) = entered a ++ entered b := by
  induction a with
  | nil => rfl
  | cons e es ih => cases e <;> simp [entered, ih]

theorem step_memo_trace {g : Graph} {a b : Config} {events : List Event}
    (h : step g a = some (events, b)) : b.seen = (entered events).reverse ++ a.seen := by
  rcases a with ⟨stack, seen⟩
  cases stack with
  | nil => simp [step] at h
  | cons frame rest =>
    cases frame with
    | visit node =>
      simp only [step] at h
      split at h <;> cases h <;> simp [entered]
    | resume parent index children =>
      cases children <;> simp only [step] at h <;> cases h <;> simp [entered]

theorem steps_memo_trace {g : Graph} {a b : Config} {events : List Event}
    (h : Steps g a events b) : b.seen = (entered events).reverse ++ a.seen := by
  induction h with
  | done => simp [entered]
  | next hs _ ih =>
    rw [ih, step_memo_trace hs]
    simp [entered_append, List.reverse_append, List.append_assoc]

theorem entries_unique {g : Graph} {a b : Config} {events : List Event}
    (h : Steps g a events b) (hn : a.seen.Nodup) : (entered events).Nodup := by
  have hd := steps_seen_nodup h hn
  rw [steps_memo_trace h] at hd
  exact List.nodup_reverse.mp (List.nodup_append.mp hd).1

def run (g : Graph) : Nat → Config → List Event × Config
  | 0, c => ([], c)
  | fuel + 1, c => match step g c with
    | none => ([], c)
    | some (events, next) =>
      let (trace, final) := run g fuel next
      (events ++ trace, final)

theorem run_sound (g : Graph) (fuel : Nat) (c : Config) :
    Steps g c (run g fuel c).1 (run g fuel c).2 := by
  induction fuel generalizing c with
  | zero => exact Steps.done c
  | succ fuel ih =>
    simp only [run]
    cases h : step g c with
    | none => exact Steps.done c
    | some pair =>
      rcases pair with ⟨events, next⟩
      cases hr : run g fuel next with
      | mk trace final =>
        have hi := ih next
        simp only [hr] at hi
        simpa [run, h, hr] using Steps.next h hi

def exampleGraph : Graph := fun n => if n = 0 then [1, 1] else [0]
example : (run exampleGraph 20 ⟨[.visit 0], []⟩).1 =
    [.enter 0, .edge 0 0 1, .enter 1, .edge 1 0 0, .edge 0 1 1] := by decide
example : (run exampleGraph 20 ⟨[.visit 0], []⟩).2.stack = [] := by decide

def capturedLength : Nat → List Nat → Nat
  | initial, [] => initial
  | initial, index :: rest => capturedLength (max initial (index + 1)) rest

theorem initial_le_capturedLength (initial : Nat) (indices : List Nat) :
    initial ≤ capturedLength initial indices := by
  induction indices generalizing initial with
  | nil => exact Nat.le_refl _
  | cons index rest ih => exact (Nat.le_max_left _ _).trans (ih _)

theorem captured_index_lt_length (initial index : Nat) (indices : List Nat)
    (h : index ∈ indices) : index < capturedLength initial indices := by
  induction indices generalizing initial with
  | nil => simp at h
  | cons head rest ih =>
    rcases List.mem_cons.mp h with h | h
    · subst index
      have hm := (Nat.le_max_right initial (head + 1)).trans
        (initial_le_capturedLength (max initial (head + 1)) rest)
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self head) hm
    · exact ih _ h

#print axioms recursive_refines_stack
#print axioms step_seen_nodup
#print axioms steps_seen_nodup
#print axioms step_memo_trace
#print axioms steps_memo_trace
#print axioms entries_unique
#print axioms run_sound
#print axioms initial_le_capturedLength
#print axioms captured_index_lt_length

end SerializationDFS
