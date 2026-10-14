import Execution

namespace Reconcile.IncomingConsensus

/-- Exact sufficient statistic for universal equality, with opaque labels. -/
inductive Summary (α : Type) where
  | empty
  | one (label : α)
  | conflict
  deriving DecidableEq, Repr

variable {α : Type} [DecidableEq α]

def combine : Summary α → Summary α → Summary α
  | .empty, right => right
  | left, .empty => left
  | .one left, .one right => if left = right then .one left else .conflict
  | _, _ => .conflict

def accepts : Summary α → α → Prop
  | .empty, _ => True
  | .one label, actual => label = actual
  | .conflict, _ => False

instance (summary : Summary α) (actual : α) : Decidable (accepts summary actual) := by
  cases summary <;> simp only [accepts] <;> infer_instance

theorem combine_empty (summary : Summary α) :
    combine .empty summary = summary ∧ combine summary .empty = summary := by
  cases summary <;> simp [combine]

theorem combine_assoc (a b c : Summary α) :
    combine (combine a b) c = combine a (combine b c) := by
  cases a <;> cases b <;> cases c <;> simp [combine] <;> split_ifs <;> simp_all

theorem accepts_combine (a b : Summary α) (actual : α) :
    accepts (combine a b) actual ↔ accepts a actual ∧ accepts b actual := by
  cases a <;> cases b <;> simp [combine, accepts]
  split_ifs <;> simp_all
  grind

def summarize : List α → Summary α
  | [] => .empty
  | label :: rest => combine (.one label) (summarize rest)

theorem summarize_accepts (labels : List α) (actual : α) :
    accepts (summarize labels) actual ↔ ∀ label ∈ labels, label = actual := by
  induction labels with
  | nil => simp [summarize, accepts]
  | cons label rest ih =>
    rw [summarize, accepts_combine, ih]
    simp [accepts]

/-- The runtime's incremental left fold is the same statistic as the simple reference. -/
theorem foldl_eq (labels : List α) (seed : Summary α) :
    labels.foldl (fun acc label => combine acc (.one label)) seed =
      combine seed (summarize labels) := by
  induction labels generalizing seed with
  | nil => simp [summarize, (combine_empty seed).2]
  | cons label rest ih => simp [summarize, List.foldl, ih, combine_assoc]

open Execution

/-- Finite reference only: native incoming incidences must correspond to these bindings. -/
noncomputable def incomingLabels (s : State) (node : Nat) : List Nat :=
  ((s.domain.toList.flatMap fun owner => (s.bindings owner).construction).filter
    (fun edge => edge.node == node)).map (fun edge => edge.identity)

theorem construction_iff (s : State) (node actual : Nat) :
    accepts (summarize (incomingLabels s node)) actual ↔ constructionStable s node actual := by
  simp [summarize_accepts, incomingLabels, constructionStable]
  aesop

/-- Only the finite guard differs from the established transition. -/
def rebindSummary (s : State) (r : Receipt) (node actual storage mode : Nat)
    (summary : Summary Nat) : Option State :=
  if current s r ∧ s.phase = .checking ∧ node ∈ s.domain ∧
      (s.bindings node).fixed = false ∧ (s.bindings node).storage = storage ∧
      mode ∈ (s.bindings node).palette ∧ (node, mode) ∉ s.claims ∧
      accepts summary actual then
    some { s with
      bindings := fun n => if n = node then { s.bindings n with exposed := actual, mode } else s.bindings n
      revision := s.revision + 1
      phase := .publishing
      checked := ∅
      claims := insert (node, mode) s.claims }
  else none

theorem rebind_eq (s : State) (r : Receipt) (node actual storage mode : Nat) :
    rebindSummary s r node actual storage mode (summarize (incomingLabels s node)) =
      rebind s r node actual storage mode := by
  simp only [rebindSummary, rebind, construction_iff]

theorem incoming_preserved (s t : State) (r : Receipt) (node actual storage mode target : Nat)
    (h : rebind s r node actual storage mode = some t) :
    incomingLabels t target = incomingLabels s target := by
  obtain ⟨_, hd, hb⟩ := rebind_preserves_selection s t r node actual storage mode h
  unfold incomingLabels
  rw [hd]
  congr 3
  funext owner
  exact (hb owner).2.2.2

-- Native obligations: admitted node indices, identity equality, grouping by target,
-- and receipt/observation boundaries. This file models no JavaScript observations.
example : accepts (summarize ([7, 7, 7] : List Nat)) 7 := by decide
example : ¬ accepts (summarize ([7, 8] : List Nat)) 7 := by decide
example : accepts (summarize ([] : List Nat)) 42 := by decide

end Reconcile.IncomingConsensus
