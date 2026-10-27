/-! Finite enumerations that the generated corpora draw from, and the prototype chains of the
`Atoms`, `RecognitionPlain` and `Ingress` corpora (`behind`). Each recursion is structural, on a
list or on a length bound used as fuel. Lists come shortest first, and lists of one length in the
lexicographic order of their elements' positions. A corpus's order is free: its bridge freezes
only its size. -/

namespace Reconcile.Enumerate

/-- Every list whose `i`-th element is one of the `i`-th list of `choices`. -/
def product {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | choice :: rest => choice.flatMap fun first => (product rest).map (first :: ·)

/-- Every word of exactly `length` letters. -/
def words {α : Type} (length : Nat) (letters : List α) : List (List α) :=
  product (List.replicate length letters)

/-- Every word of at most `length` letters. -/
def wordsUpTo {α : Type} (length : Nat) (letters : List α) : List (List α) :=
  (List.range (length + 1)).flatMap (words · letters)

/-- Every list of at most `length` distinct items. -/
def arrangementsUpTo {α : Type} [DecidableEq α] (length : Nat) (items : List α) :
    List (List α) :=
  (wordsUpTo length items).filter fun list => decide list.Nodup

/-- Every list of distinct items. -/
def arrangements {α : Type} [DecidableEq α] (items : List α) : List (List α) :=
  arrangementsUpTo items.length items

/-- A prototype chain of the `Atoms`, `RecognitionPlain` and `Ingress` corpora: `depth` custom
prototypes, labelled from 100 as their bridges number them, in front of the built-in `tail`. -/
def behind {α : Type} (custom : Nat → α) (depth : Nat) (tail : List α) : List α :=
  (List.range depth).map (fun level => custom (100 + level)) ++ tail

example : (words 2 [0, 1]).length = 4 := by decide
example : wordsUpTo 2 [0, 1] = [[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1]] := by decide
example : arrangements [0, 1] = [[], [0], [1], [0, 1], [1, 0]] := by decide

end Reconcile.Enumerate
