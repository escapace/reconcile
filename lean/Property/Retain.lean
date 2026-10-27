/-! # The retained prefix: greedy matching of two key orders

JavaScript cannot move an own property or a `Map` or `Set` entry; deleting it and adding it again
appends it. A key or entry that keeps its place is therefore one of a prefix of the desired order
that occurs, in that order, in the current order. `matched` finds it greedily, as the runtime's
publication does: it keeps a current key when it is the next desired key not yet kept. The result
is a prefix of the desired order (`matched_prefix`), a subsequence of the current order
(`matched_sublist`), and the longest such prefix (`matched_maximal`).

`PropertyPlacement` places own keys with it, and `Spec.Reconcile.retainPrefix` is it, for keys and
for entries. This module uses only core lemmas, so the reference models the oracle runs can import
it. -/
namespace Reconcile.PropertyPlacement

open List

variable {α : Type} [DecidableEq α]

/-- The current keys greedy matching keeps, in order. -/
def matched : List α → List α → List α
  | [], _ => []
  | _, [] => []
  | d :: ds, c :: cs => if c = d then d :: matched ds cs else matched (d :: ds) cs

/-- Greedy matching keeps a prefix of the desired order. -/
theorem matched_prefix (ds cs : List α) : matched ds cs <+: ds := by
  induction cs generalizing ds with
  | nil => cases ds <;> simp [matched]
  | cons c cs ih =>
    cases ds with
    | nil => simp [matched]
    | cons d ds =>
      unfold matched
      split
      · exact List.cons_prefix_cons.mpr ⟨rfl, ih ds⟩
      · exact ih (d :: ds)

/-- Greedy matching keeps a subsequence of the current order: nothing it keeps moves. -/
theorem matched_sublist (ds cs : List α) : matched ds cs <+ cs := by
  induction cs generalizing ds with
  | nil => cases ds <;> simp [matched]
  | cons c cs ih =>
    cases ds with
    | nil => simp [matched]
    | cons d ds =>
      unfold matched
      split
      · rename_i h
        subst h
        exact (ih ds).cons₂ c
      · exact (ih (d :: ds)).cons c

/-- Greedy matching keeps the longest desired prefix that occurs in the current order. -/
theorem matched_maximal (ds cs p : List α) (hp : p <+: ds) (hs : p <+ cs) :
    p.length ≤ (matched ds cs).length := by
  induction cs generalizing ds p with
  | nil =>
    have : p = [] := List.eq_nil_of_sublist_nil hs
    simp [this]
  | cons c cs ih =>
    cases p with
    | nil => simp
    | cons x p =>
      cases ds with
      | nil => simp at hp
      | cons d ds =>
        obtain ⟨hx, hp'⟩ := List.cons_prefix_cons.mp hp
        subst hx
        unfold matched
        split
        · rename_i h
          subst h
          simpa using ih ds p hp' (List.cons_sublist_cons.mp hs)
        · rename_i h
          have : x :: p <+ cs := by
            rcases List.sublist_cons_iff.mp hs with hs | ⟨r, hr, _⟩
            · exact hs
            · cases hr; exact absurd rfl h
          exact ih (x :: ds) (x :: p) (List.cons_prefix_cons.mpr ⟨rfl, hp'⟩) this

end Reconcile.PropertyPlacement
