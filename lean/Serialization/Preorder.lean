import Serialization.DFS

/-!
# Canonical node numbering

The encoder numbers nodes in the order its depth-first traversal enters them (`DFS.lean`
`Recursive`, `entered`): the root is node 0, and each node's reference slots are visited in
order, a newly reached node's whole subtree before the next slot. The decoder checks that a
document's own reference graph has this numbering without a separate traversal: scanning the
nodes in reverse, each node's subtree ends at a computed position, and a reference either
names an already entered node (below the cursor), or the next node (at the cursor), whose
subtree end becomes the cursor, or is out of order (above the cursor).

`preorder_iff` proves the check accepts exactly the documents whose depth-first traversal from
node 0 enters `0, 1, …, n - 1`, so every node is reachable and the numbering is the encoder's.
`check_iff` lifts it to `check`, the runtime's reverse table fill, and `encoder_canonical` shows
the encoder's entry-order numbering passes.
-/

namespace SerializationPreorder

open SerializationDFS

/-- Scan a node's ordered children with the nodes below `k` entered, given subtree ends. -/
def scan (e : Nat → Option Nat) : List Nat → Nat → Option Nat
  | [], k => some k
  | r :: rs, k => if r < k then scan e rs k else if r = k then (e r).bind (scan e rs) else none

/-- One past the last node entered by `v`'s subtree, when the numbering is canonical. -/
def ends (c : Graph) (n v : Nat) : Option Nat :=
  if hv : v < n then
    scan (fun r => if _h : v < r ∧ r < n then ends c n r else none) (c v) (v + 1)
  else none
termination_by n - v
decreasing_by omega

/-- A scan only moves its cursor forward when every end lies past its node. -/
theorem scan_ge (e : Nat → Option Nat) :
    ∀ (rs : List Nat) (k k' : Nat), scan e rs k = some k' →
      (∀ r y, k ≤ r → e r = some y → r < y) → k ≤ k' := by
  intro rs
  induction rs with
  | nil => intro k k' h _; simp only [scan, Option.some.injEq] at h; omega
  | cons r rs ih =>
    intro k k' h he
    simp only [scan] at h
    split at h
    · exact ih k k' h he
    · split at h
      · rename_i hr
        subst hr
        cases hy : e r with
        | none => simp [hy] at h
        | some y =>
          simp only [hy, Option.bind_some] at h
          have hry := he r y (Nat.le_refl r) hy
          have := ih y k' h (fun x z hx hz => he x z (by omega) hz)
          omega
      · cases h

theorem ends_gt {c : Graph} {n : Nat} : ∀ d v y, n - v = d → ends c n v = some y → v < y := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
    intro v y hd h
    rw [ends] at h
    split at h
    · rename_i hv
      have := scan_ge _ (c v) (v + 1) y h (fun r z hr hz => by
        split at hz
        · rename_i hrn
          exact ihd (n - r) (by omega) r z rfl hz
        · cases hz)
      omega
    · cases h

theorem scan_congr (e e' : Nat → Option Nat) (b : Nat) (he : ∀ r, b ≤ r → e r = e' r)
    (hgt : ∀ r y, e' r = some y → r < y) :
    ∀ (rs : List Nat) (k : Nat), b ≤ k → scan e rs k = scan e' rs k := by
  intro rs
  induction rs with
  | nil => intro k _; rfl
  | cons r rs ih =>
    intro k hk
    simp only [scan]
    split
    · exact ih k hk
    · split
      · rename_i hr
        subst hr
        rw [he r hk]
        cases hy : e' r with
        | none => rfl
        | some y =>
          simp only [Option.bind_some]
          exact ih y (by have := hgt r y hy; omega)
      · rfl

theorem ends_none {c : Graph} {n v : Nat} (h : ¬v < n) : ends c n v = none := by
  rw [ends]; simp [h]

theorem ends_unfold {c : Graph} {n v : Nat} (hv : v < n) :
    ends c n v = scan (ends c n) (c v) (v + 1) := by
  rw [ends]
  simp only [hv, dite_true]
  refine scan_congr _ _ (v + 1) (fun r hr => ?_) (fun r y h => ends_gt (n - r) r y rfl h)
    (c v) (v + 1) (Nat.le_refl _)
  by_cases hn : r < n
  · simp [show v < r by omega, hn]
  · simp [hn, ends_none hn]

/-- The runtime's reverse table step: a table agreeing with `ends` above `v` gives `ends v`. -/
theorem memo_step {c : Graph} {n v : Nat} (hv : v < n) (t : Nat → Option Nat)
    (ht : ∀ r, v < r → t r = ends c n r) : scan t (c v) (v + 1) = ends c n v := by
  rw [ends_unfold hv]
  exact scan_congr t (ends c n) (v + 1) (fun r hr => ht r (by omega))
    (fun r y h => ends_gt (n - r) r y rfl h) (c v) (v + 1) (Nat.le_refl _)

/-- The memo holds exactly the nodes below `k`. -/
def Seg (m : List Nat) (k : Nat) : Prop := ∀ x, x ∈ m ↔ x < k

theorem range'_split {l1 l2 : List Nat} {k j : Nat} (h : l1 ++ l2 = List.range' k j) :
    l1.length ≤ j ∧ l1 = List.range' k l1.length ∧
      l2 = List.range' (k + l1.length) (j - l1.length) := by
  have hl : l1.length ≤ j := by
    have := congrArg List.length h; simp at this; omega
  have hs : List.range' k j =
      List.range' k l1.length ++ List.range' (k + l1.length) (j - l1.length) := by
    rw [List.range'_append_1]; congr 1; omega
  rw [hs] at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  exact ⟨hl, h1, h2⟩

theorem recursive_ends {c : Graph} {n : Nat} {fr : Frame} {m final : List Nat}
    {trace : List Event} (h : Recursive c fr m trace final) :
    ∀ k j, Seg m k → entered trace = List.range' k j → k + j ≤ n →
      Seg final (k + j) ∧
      match fr with
      | .visit v => (v < k ∧ j = 0) ∨ (v = k ∧ ends c n k = some (k + j))
      | .resume _ _ rs => scan (ends c n) rs k = some (k + j) := by
  induction h with
  | @seen node memo hm =>
    intro k j hs he _
    have hj : j = 0 := by
      have := congrArg List.length he; simp [entered] at this; omega
    subst hj
    exact ⟨by simpa using hs, Or.inl ⟨(hs node).mp hm, rfl⟩⟩
  | @fresh node memo trace final hm _ ih =>
    intro k j hs he hb
    cases j with
    | zero => simp [entered] at he
    | succ j =>
      simp only [entered, List.range'_succ, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      have hs' : Seg (node :: memo) (node + 1) := by
        intro x
        simp only [List.mem_cons, hs x]
        omega
      obtain ⟨hf, hscan⟩ := ih (node + 1) j hs' he (by omega)
      refine ⟨by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hf, Or.inr ⟨rfl, ?_⟩⟩
      rw [ends_unfold (by omega)]
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using hscan
  | empty =>
    intro k j hs he _
    have hj : j = 0 := by
      have := congrArg List.length he; simp [entered] at this; omega
    subst hj
    exact ⟨by simpa using hs, by simp [scan]⟩
  | @child parent index node children memo middle final first second _ _ ih1 ih2 =>
    intro k j hs he hb
    simp only [entered, entered_append] at he
    obtain ⟨hl, h1, h2⟩ := range'_split he
    obtain ⟨hm, hv⟩ := ih1 k _ hs h1 (by omega)
    obtain ⟨hf, hscan⟩ := ih2 (k + (entered first).length) _ hm h2 (by omega)
    have hj : k + (entered first).length + (j - (entered first).length) = k + j := by omega
    rw [hj] at hf hscan
    refine ⟨hf, ?_⟩
    simp only [scan]
    rcases hv with ⟨hlt, hz⟩ | ⟨rfl, hend⟩
    · simp only [hlt, if_true]
      simpa [hz] using hscan
    · simp [hend, hscan]

theorem scan_recursive {c : Graph} {n b : Nat}
    (H : ∀ r e, b ≤ r → ends c n r = some e → ∀ m, Seg m r → ∃ trace final,
      Recursive c (.visit r) m trace final ∧ entered trace = List.range' r (e - r) ∧
        Seg final e ∧ r < e) :
    ∀ (rs : List Nat) (k k' p i : Nat) (m : List Nat), b ≤ k → Seg m k →
      scan (ends c n) rs k = some k' →
      ∃ trace final, Recursive c (.resume p i rs) m trace final ∧
        entered trace = List.range' k (k' - k) ∧ Seg final k' ∧ k ≤ k' := by
  intro rs
  induction rs with
  | nil =>
    intro k k' p i m _ hs h
    simp only [scan, Option.some.injEq] at h
    subst h
    exact ⟨[], m, .empty, by simp [entered], hs, Nat.le_refl _⟩
  | cons r rs ih =>
    intro k k' p i m hb hs h
    simp only [scan] at h
    split at h
    · rename_i hr
      obtain ⟨t, f, hrec, he, hf, hk⟩ := ih k k' p (i + 1) m hb hs h
      exact ⟨.edge p i r :: ([] ++ t), f, .child (.seen ((hs r).mpr hr)) hrec,
        by simpa [entered] using he, hf, hk⟩
    · split at h
      · rename_i _ hr
        subst hr
        cases he1 : ends c n r with
        | none => simp [he1] at h
        | some e1 =>
          simp only [he1, Option.bind_some] at h
          obtain ⟨t1, f1, hrec1, hen1, hf1, hlt⟩ := H r e1 hb he1 m hs
          obtain ⟨t2, f2, hrec2, hen2, hf2, hk⟩ := ih e1 k' p (i + 1) f1 (by omega) hf1 h
          refine ⟨.edge p i r :: (t1 ++ t2), f2, .child hrec1 hrec2, ?_, hf2, by omega⟩
          simp only [entered, entered_append, hen1, hen2]
          have hc := @List.range'_append_1 r (e1 - r) (k' - e1)
          rw [show r + (e1 - r) = e1 by omega] at hc
          rw [hc]; congr 1; omega
      · cases h

theorem ends_recursive {c : Graph} {n : Nat} :
    ∀ d v e, n - v = d → ends c n v = some e → ∀ m, Seg m v → ∃ trace final,
      Recursive c (.visit v) m trace final ∧ entered trace = List.range' v (e - v) ∧
        Seg final e ∧ v < e := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
    intro v e hd he m hs
    by_cases hv : v < n
    · rw [ends_unfold hv] at he
      have hs' : Seg (v :: m) (v + 1) := by
        intro x; simp only [List.mem_cons, hs x]; omega
      have H : ∀ r e, v + 1 ≤ r → ends c n r = some e → ∀ m, Seg m r →
          ∃ trace final, Recursive c (.visit r) m trace final ∧
            entered trace = List.range' r (e - r) ∧ Seg final e ∧ r < e := by
        intro r e hr her m' hs''
        have hrn : r < n := by
          by_contra hrn; rw [ends_none hrn] at her; cases her
        exact ihd (n - r) (by omega) r e rfl her m' hs''
      obtain ⟨t, f, hrec, hen, hf, hk⟩ := scan_recursive (n := n) H
        (c v) (v + 1) e v 0 (v :: m) (Nat.le_refl _) hs' he
      have hvm : v ∉ m := fun hm => by have := (hs v).mp hm; omega
      refine ⟨.enter v :: t, f, .fresh hvm hrec, ?_, hf, by omega⟩
      simp only [entered, hen]
      rw [show e - v = (e - (v + 1)) + 1 by omega, List.range'_succ]
    · rw [ends_none hv] at he; cases he

/-- The reverse-scan check accepts exactly the canonical numbering: the document's depth-first
traversal from node 0 enters every node, in id order. -/
theorem preorder_iff (c : Graph) (n : Nat) :
    ends c n 0 = some n ↔
      ∃ trace final, Recursive c (.visit 0) [] trace final ∧ entered trace = List.range n := by
  constructor
  · intro h
    obtain ⟨t, f, hrec, hen, _, _⟩ := ends_recursive (n - 0) 0 n rfl h [] (by simp [Seg])
    exact ⟨t, f, hrec, by simpa [List.range_eq_range'] using hen⟩
  · rintro ⟨t, f, hrec, hen⟩
    have hs : Seg [] 0 := by simp [Seg]
    obtain ⟨_, hv⟩ := recursive_ends (n := n) hrec 0 n hs
      (by simpa [List.range_eq_range'] using hen) (by omega)
    rcases hv with ⟨h, _⟩ | ⟨_, h⟩
    · omega
    · simpa using h

/-- The runtime's table after filling the last `d` nodes, from node `n - 1` down. -/
def table (c : Graph) (n : Nat) : Nat → Nat → Option Nat
  | 0 => fun _ => none
  | d + 1 => fun r =>
    if r = n - (d + 1) then scan (table c n d) (c r) (r + 1) else table c n d r

def check (c : Graph) (n : Nat) : Bool := table c n n 0 == some n

theorem table_ends {c : Graph} {n : Nat} :
    ∀ d, d ≤ n → ∀ r, n - d ≤ r → table c n d r = ends c n r := by
  intro d
  induction d with
  | zero => intro _ r hr; simp [table, ends_none (show ¬r < n by omega)]
  | succ d ih =>
    intro hd r hr
    simp only [table]
    split
    · rename_i hv
      subst hv
      exact memo_step (by omega) _ (fun x hx => ih (by omega) x (by omega))
    · exact ih (by omega) r (by omega)

/-- The runtime check is the proved characterization. -/
theorem check_iff (c : Graph) (n : Nat) :
    check c n = true ↔
      ∃ trace final, Recursive c (.visit 0) [] trace final ∧ entered trace = List.range n := by
  rw [← preorder_iff, check, table_ends n (Nat.le_refl n) 0 (by omega)]
  simp

/-! ## The encoder's numbering passes -/

def relabelFrame (σ : Nat → Nat) : Frame → Frame
  | .visit v => .visit (σ v)
  | .resume p i rs => .resume (σ p) i (rs.map σ)

def relabelEvent (σ : Nat → Nat) : Event → Event
  | .enter v => .enter (σ v)
  | .edge p i v => .edge (σ p) i (σ v)

theorem entered_relabel (σ : Nat → Nat) (trace : List Event) :
    entered (trace.map (relabelEvent σ)) = (entered trace).map σ := by
  induction trace with
  | nil => rfl
  | cons e es ih => cases e <;> simp [entered, relabelEvent, ih]

/-- Depth-first traversal commutes with an injective renaming of nodes. -/
theorem recursive_relabel {g c : Graph} (σ : Nat → Nat) (hσ : Function.Injective σ)
    (hc : ∀ x, c (σ x) = (g x).map σ) {fr : Frame} {m final : List Nat} {trace : List Event}
    (h : Recursive g fr m trace final) :
    Recursive c (relabelFrame σ fr) (m.map σ) (trace.map (relabelEvent σ)) (final.map σ) := by
  induction h with
  | seen hm => exact .seen (List.mem_map_of_mem hm)
  | @fresh node memo trace final hm _ ih =>
    refine .fresh (fun hmem => hm ?_) ?_
    · obtain ⟨y, hy, he⟩ := List.mem_map.mp hmem
      exact hσ he ▸ hy
    · simpa [relabelFrame, hc] using ih
  | empty => exact .empty
  | child _ _ ih1 ih2 =>
    simpa [relabelFrame, relabelEvent] using Recursive.child ih1 ih2

/-- The encoder numbers nodes injectively in entry order, so its document passes the check.
`hc` says the document's reference slots are the source's children, renamed. -/
theorem encoder_canonical {g c : Graph} {n root : Nat} (σ : Nat → Nat)
    (hσ : Function.Injective σ) (hc : ∀ x, c (σ x) = (g x).map σ) {trace : List Event}
    {final : List Nat} (h : Recursive g (.visit root) [] trace final) (hroot : σ root = 0)
    (hn : (entered trace).map σ = List.range n) : check c n = true := by
  rw [check_iff]
  refine ⟨trace.map (relabelEvent σ), final.map σ, ?_, by rw [entered_relabel, hn]⟩
  simpa [relabelFrame, hroot] using recursive_relabel σ hσ hc h

-- A cycle back to the root, a shared child, an unreachable node and an out-of-order child.
def cycle : Graph := fun v => if v = 0 then [1, 0] else if v = 1 then [2, 0] else []
example : check cycle 3 = true := by decide
example : check (fun v => if v = 0 then [1, 1] else []) 2 = true := by decide
example : check (fun v => if v = 0 then [1] else []) 3 = false := by decide
example : check (fun v => if v = 0 then [2, 1] else []) 3 = false := by decide

end SerializationPreorder
