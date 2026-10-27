import Spec.Reconcile

/-!
# Discovery from capture's alignment

`Spec.Reconcile.discover` makes two walks: `visitStep`, capture's walk, aligns each node on its
first visit, and `candidateStep` gathers every candidate through every position. When no
reference of an aligned node offers, at its position, a current object of the child's kind other
than the one the child is aligned with (`OffersAligned`), each node's candidates are its alignment
and nothing else (`candidates_eq_aligned`). `candidates` in `src/publication/candidates.ts` then
takes capture's alignment without walking. The proof follows `candidateStep` pair by pair
alongside `visitStep`, whose fuel suffices because each step consumes a pending pair or a node's
references. `offersAligned_needed` shows the premise is needed: one `next` object at two keys has
two candidates.
-/

namespace Reconcile.Spec.Reconcile

open Reconcile.Spec

/-- Whether every reference of a node aligned with `p` offers, at its position, no current object
of the child's kind or the object the child is aligned with. -/
def OffersAligned (cur next : Graph) (first : Array (Option Nat)) : Prop :=
  ∀ j p, first[j]? = some (some p) → ∀ pos c, (pos, Val.ref c) ∈ (next.node j).slots →
    ∀ q, (((cur.node p).occupant pos).bind Val.refId).filter
        (fun q => (cur.node q).kind == (next.node c).kind) = some q →
      first[c]? = some (some q)

/-- The pending pairs `visitStep` pushes for a node aligned with `aligned`. -/
def visitChildren (cur : Graph) (node : Obj) (aligned : Option Nat) : List (Nat × Option Nat) :=
  node.slots.filterMap fun (pos, v) =>
    match v with
    | .ref c => some (c, if pos.property then
        aligned.bind fun p => ((cur.node p).occupant pos).bind Val.refId else none)
    | .prim _ => none

/-- The pending pairs `candidateStep` pushes for a node walked with candidate `p`. -/
def candidateChildren (cur : Graph) (node : Obj) (p : Nat) : List (Nat × Option Nat) :=
  node.slots.filterMap fun (pos, v) =>
    match v with
    | .ref c => some (c, ((cur.node p).occupant pos).bind Val.refId)
    | .prim _ => none

theorem visitStep_cons (cur next : Graph) (fuel j : Nat) (pinning : Option Nat)
    (rest : List (Nat × Option Nat)) (visited : Array Bool) (first : Array (Option Nat))
    (order : List Nat) :
    visitStep cur next (fuel + 1) ((j, pinning) :: rest) visited first order =
      if visited[j]?.getD true then visitStep cur next fuel rest visited first order
      else
        let aligned := pinning.filter fun p => (cur.node p).kind == (next.node j).kind
        visitStep cur next fuel (visitChildren cur (next.node j) aligned ++ rest)
          (visited.setIfInBounds j true) (first.setIfInBounds j aligned) (j :: order) := by
  rfl

theorem candidateStep_cons (cur next : Graph) (fuel j : Nat) (candidate : Option Nat)
    (rest : List (Nat × Option Nat)) (candidates : Array (List Nat)) :
    candidateStep cur next (fuel + 1) ((j, candidate) :: rest) candidates =
      match candidate.filter fun p => (cur.node p).kind == (next.node j).kind with
      | none => candidateStep cur next fuel rest candidates
      | some p =>
        if (candidates[j]?.getD []).contains p then candidateStep cur next fuel rest candidates
        else
          candidateStep cur next fuel (candidateChildren cur (next.node j) p ++ rest)
            (candidates.setIfInBounds j ((candidates[j]?.getD []) ++ [p])) := by
  rfl

theorem candidateStep_nil (cur next : Graph) (fuel : Nat) (candidates : Array (List Nat)) :
    candidateStep cur next fuel [] candidates = candidates := by
  cases fuel <;> rfl

/-! ## The two walks' pending pairs -/

/-- `visitStep`'s pending pairs against `candidateStep`'s: the same nodes in the same order, each
offering nothing or the same object, apart from pairs that offer nothing and that `candidateStep`
never pushed. -/
inductive Pending : List (Nat × Option Nat) → List (Nat × Option Nat) → Prop
  | nil : Pending [] []
  | both {j : Nat} {x y : Option Nat} {wv wc : List (Nat × Option Nat)} :
      (x = none ∨ x = y) → Pending wv wc → Pending ((j, x) :: wv) ((j, y) :: wc)
  | dead {j : Nat} {wv wc : List (Nat × Option Nat)} :
      Pending wv wc → Pending ((j, none) :: wv) wc

theorem Pending.nil_left {wc : List (Nat × Option Nat)} (h : Pending [] wc) : wc = [] := by
  cases h; rfl

theorem pending_children (cur : Graph) (node : Obj) (p : Nat)
    {wv wc : List (Nat × Option Nat)} (h : Pending wv wc) :
    Pending (visitChildren cur node (some p) ++ wv) (candidateChildren cur node p ++ wc) := by
  unfold visitChildren candidateChildren
  induction node.slots with
  | nil => simpa using h
  | cons s ss ih =>
    obtain ⟨pos, v⟩ := s
    cases v with
    | prim _ => simpa using ih
    | ref c =>
      simp only [List.filterMap_cons, List.cons_append]
      exact Pending.both (by cases pos.property <;> simp) ih

theorem pending_dead (cur : Graph) (node : Obj) {wv wc : List (Nat × Option Nat)}
    (h : Pending wv wc) : Pending (visitChildren cur node none ++ wv) wc := by
  unfold visitChildren
  induction node.slots with
  | nil => simpa using h
  | cons s ss ih =>
    obtain ⟨pos, v⟩ := s
    cases v with
    | prim _ => simpa using ih
    | ref c =>
      simp only [List.filterMap_cons, List.cons_append]
      have hnone : (if pos.property = true then (none : Option Nat).bind
          (fun p => ((cur.node p).occupant pos).bind Val.refId) else none) = none := by
        split <;> rfl
      rw [hnone]
      exact Pending.dead ih

theorem mem_candidateChildren {cur : Graph} {node : Obj} {p c : Nat} {y : Option Nat}
    (h : (c, y) ∈ candidateChildren cur node p) :
    ∃ pos, (pos, Val.ref c) ∈ node.slots ∧ y = ((cur.node p).occupant pos).bind Val.refId := by
  unfold candidateChildren at h
  rw [List.mem_filterMap] at h
  obtain ⟨⟨pos, v⟩, hmem, hv⟩ := h
  cases v with
  | prim _ => simp at hv
  | ref c' =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    exact ⟨pos, hmem, rfl⟩

/-! ## `visitStep` -/

theorem visitStep_size (cur next : Graph) : ∀ fuel wv visited (first : Array (Option Nat)) order,
    (visitStep cur next fuel wv visited first order).2.size = first.size
  | 0, _, _, _, _ => rfl
  | _ + 1, [], _, _, _ => rfl
  | fuel + 1, (j, pinning) :: rest, visited, first, order => by
    rw [visitStep_cons]
    split
    · exact visitStep_size cur next fuel rest visited first order
    · simp only [visitStep_size, Array.size_setIfInBounds]

/-- `visitStep` never changes the alignment of a node it has visited. -/
theorem visitStep_keep (cur next : Graph) (k : Nat) : ∀ fuel wv (visited : Array Bool)
    (first : Array (Option Nat)) order, visited[k]? = some true →
    (visitStep cur next fuel wv visited first order).2[k]? = first[k]?
  | 0, _, _, _, _, _ => rfl
  | _ + 1, [], _, _, _, _ => rfl
  | fuel + 1, (j, pinning) :: rest, visited, first, order, hk => by
    rw [visitStep_cons]
    split
    · exact visitStep_keep cur next k fuel rest visited first order hk
    · rename_i hj
      have hne : j ≠ k := by
        rintro rfl
        simp [hk] at hj
      simp only
      rw [visitStep_keep cur next k fuel _ _ _ _ (by simp [hne, hk])]
      simp [hne]

/-! ## Fuel -/

theorem filterMap_zipIdx_fst {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (n : Nat), (l.zipIdx n).filterMap (fun x => f x.1) = l.filterMap f
  | [], _ => rfl
  | a :: l, n => by
    simp only [List.zipIdx_cons, List.filterMap_cons]
    cases f a <;> simp [filterMap_zipIdx_fst f l]

theorem flatMap_zipIdx_fst {α β : Type} (f : α → List β) :
    ∀ (l : List α) (n : Nat), (l.zipIdx n).flatMap (fun x => f x.1) = l.flatMap f
  | [], _ => rfl
  | a :: l, n => by
    simp only [List.zipIdx_cons, List.flatMap_cons]
    rw [flatMap_zipIdx_fst f l]

/-- The references a node holds are its slots' references. -/
theorem slots_refs (o : Obj) : o.slots.filterMap (fun s => s.2.refId) = o.refs := by
  cases o with
  | object proto fields extensible =>
    simp only [Obj.slots, Obj.refs, List.filterMap_map]
    rfl
  | array entries ext =>
    simp only [Obj.slots, Obj.refs, List.filterMap_filterMap]
    rw [← filterMap_zipIdx_fst _ entries 0]
    congr 1
    funext x
    obtain ⟨e, i⟩ := x
    rcases e with _ | _ | _ <;> rfl
  | map entries =>
    simp only [Obj.slots, Obj.refs, List.filterMap_flatMap]
    rw [← flatMap_zipIdx_fst _ entries 0]
    congr 1
    funext x
    obtain ⟨⟨k, v⟩, i⟩ := x
    cases k <;> cases v <;> rfl
  | set members =>
    simp only [Obj.slots, Obj.refs, List.filterMap_map]
    rw [← filterMap_zipIdx_fst _ members 0]
    congr 1
  | date ms => rfl
  | buffer bytes max => rfl
  | view ctor storage offset length =>
    cases storage <;> rfl

theorem length_visitChildren (cur : Graph) (o : Obj) (aligned : Option Nat) :
    (visitChildren cur o aligned).length = o.refs.length := by
  rw [← slots_refs, ← List.length_map (f := Prod.fst), visitChildren, List.map_filterMap]
  congr 1
  congr 1
  funext s
  obtain ⟨pos, v⟩ := s
  cases v <;> rfl

/-- The references of the nodes `visitStep` has not visited. -/
def unvisitedRefs (next : Graph) (visited : Array Bool) : Nat :=
  ((List.range visited.size).map fun i =>
    if visited[i]?.getD true then 0 else (next.node i).refs.length).sum

theorem sum_update {l : List Nat} (hl : l.Nodup) {j : Nat} (hj : j ∈ l) (f g : Nat → Nat)
    (hg : ∀ i, i ≠ j → g i = f i) (hgj : g j = 0) : (l.map g).sum + f j = (l.map f).sum := by
  induction l with
  | nil => simp at hj
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.sum_cons]
    by_cases ha : a = j
    · subst ha
      have : l.map g = l.map f :=
        List.map_congr_left fun i hi => hg i fun h => hl.1 (h ▸ hi)
      rw [this, hgj]
      omega
    · have hj' : j ∈ l := by
        rcases List.mem_cons.1 hj with h | h
        · exact absurd h.symm ha
        · exact h
      rw [hg a ha]
      have := ih hl.2 hj'
      omega

theorem unvisitedRefs_visit (next : Graph) (visited : Array Bool) (j : Nat)
    (hj : visited[j]? = some false) :
    unvisitedRefs next (visited.setIfInBounds j true) + (next.node j).refs.length =
      unvisitedRefs next visited := by
  have hlt : j < visited.size := by
    rcases Nat.lt_or_ge j visited.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hj
      cases hj
  unfold unvisitedRefs
  rw [Array.size_setIfInBounds]
  have hfj : (if visited[j]?.getD true then 0 else (next.node j).refs.length) =
      (next.node j).refs.length := by simp [hj]
  conv => lhs; rw [← hfj]
  apply sum_update List.nodup_range (List.mem_range.2 hlt)
  · intro i hi
    simp [Ne.symm hi]
  · simp [hlt]

theorem unvisitedRefs_start (next : Graph) :
    unvisitedRefs next (Array.replicate next.nodes.size false) =
      (next.nodes.toList.map (·.refs.length)).sum := by
  unfold unvisitedRefs
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp at h1
    simp [Graph.node, Array.getElem?_replicate, h1]

/-! ## The simulation -/

/-- When `visitStep` has finished, the candidates are each visited node's alignment. -/
theorem finish_eq {visited : Array Bool} {first : Array (Option Nat)} {C : Array (List Nat)}
    (hfs : first.size = visited.size) (hcs : C.size = visited.size)
    (hI1 : ∀ k : Nat, visited[k]? = some true → C[k]? = (first[k]?).map Option.toList)
    (hI2 : ∀ k : Nat, visited[k]? = some false → C[k]? = some [] ∧ first[k]? = some none) :
    C = first.map Option.toList := by
  apply Array.ext_getElem?
  intro k
  rw [Array.getElem?_map]
  rcases h : visited[k]? with _ | b
  · rw [Array.getElem?_eq_none_iff] at h
    rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]
    rfl
  · cases b
    · obtain ⟨h1, h2⟩ := hI2 k h
      rw [h1, h2]
      rfl
    · exact hI1 k h

/-- The invariants after `visitStep` visits `j` with alignment `a`, where the candidates of `j`
become `a`'s. -/
theorem visit_invariants {visited : Array Bool} {first : Array (Option Nat)}
    {C C' : Array (List Nat)} {j : Nat} {a : Option Nat} (hjlt : j < visited.size)
    (hfs : first.size = visited.size)
    (hI1 : ∀ k : Nat, visited[k]? = some true → C[k]? = (first[k]?).map Option.toList)
    (hI2 : ∀ k : Nat, visited[k]? = some false → C[k]? = some [] ∧ first[k]? = some none)
    (hCj : C'[j]? = some a.toList) (hCk : ∀ k : Nat, k ≠ j → C'[k]? = C[k]?) :
    (∀ k : Nat, (visited.setIfInBounds j true)[k]? = some true →
      C'[k]? = ((first.setIfInBounds j a)[k]?).map Option.toList) ∧
    (∀ k : Nat, (visited.setIfInBounds j true)[k]? = some false →
      C'[k]? = some [] ∧ (first.setIfInBounds j a)[k]? = some none) := by
  constructor
  · intro k hk
    by_cases hkj : k = j
    · subst hkj
      rw [hCj]
      simp [hfs, hjlt]
    · rw [hCk k hkj]
      simp only [Array.getElem?_setIfInBounds, Ne.symm hkj, if_false] at hk ⊢
      exact hI1 k hk
  · intro k hk
    by_cases hkj : k = j
    · subst hkj
      simp [hjlt] at hk
    · rw [hCk k hkj]
      simp only [Array.getElem?_setIfInBounds, Ne.symm hkj, if_false] at hk ⊢
      exact hI2 k hk

/-- `candidateStep` follows `visitStep` pair by pair: a pair `visitStep` skips, `candidateStep`
skips or never pushed, and a node `visitStep` aligns with `p` is the one node `candidateStep`
walks with `p`. -/
theorem simulate (cur next : Graph) (F : Array (Option Nat)) (hF : OffersAligned cur next F) :
    ∀ (fv fc : Nat) (wv wc : List (Nat × Option Nat)) (visited : Array Bool)
      (first : Array (Option Nat)) (C : Array (List Nat)) (order : List Nat),
    first.size = visited.size → C.size = visited.size →
    (visitStep cur next fv wv visited first order).2 = F →
    wv.length + unvisitedRefs next visited ≤ fv → fv ≤ fc → Pending wv wc →
    (∀ e ∈ wc, ∀ q, e.2.filter (fun q => (cur.node q).kind == (next.node e.1).kind) = some q →
      F[e.1]? = some (some q)) →
    (∀ k : Nat, visited[k]? = some true → C[k]? = (first[k]?).map Option.toList) →
    (∀ k : Nat, visited[k]? = some false → C[k]? = some [] ∧ first[k]? = some none) →
    candidateStep cur next fc wc C = F.map Option.toList := by
  intro fv
  induction fv with
  | zero =>
    intro fc wv wc visited first C order hfs hcs hrun hΦ _ hp _ hI1 hI2
    have hwv : wv = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hwv
    rw [Pending.nil_left hp, candidateStep_nil]
    have hF' : F = first := by rw [← hrun]; rfl
    subst hF'
    exact finish_eq hfs hcs hI1 hI2
  | succ fv ih =>
    intro fc wv wc visited first C order hfs hcs hrun hΦ hfc hp hI4 hI1 hI2
    cases wv with
    | nil =>
      rw [Pending.nil_left hp, candidateStep_nil]
      have hF' : F = first := by rw [← hrun]; rfl
      subst hF'
      exact finish_eq hfs hcs hI1 hI2
    | cons e rest =>
      obtain ⟨j, x⟩ := e
      rw [visitStep_cons] at hrun
      simp only [List.length_cons] at hΦ
      obtain ⟨m, rfl⟩ : ∃ m, fc = m + 1 := ⟨fc - 1, by omega⟩
      have hFsize : F.size = visited.size := by
        rw [← hrun]
        split <;> simp [visitStep_size, hfs]
      cases hv : visited[j]?.getD true with
      | true =>
        rw [if_pos hv] at hrun
        cases hp with
        | dead hp' =>
          exact ih (m + 1) rest wc visited first C order hfs hcs hrun (by omega) (by omega) hp'
            hI4 hI1 hI2
        | both hxy hp' =>
          rename_i y restc
          rw [candidateStep_cons]
          cases hq : y.filter (fun p => (cur.node p).kind == (next.node j).kind) with
          | none =>
            exact ih m rest restc visited first C order hfs hcs hrun (by omega) (by omega) hp'
              (fun e he => hI4 e (List.mem_cons_of_mem _ he)) hI1 hI2
          | some q =>
            have hFj := hI4 (j, y) List.mem_cons_self q hq
            have hjlt : j < visited.size := by
              rw [← hFsize]
              exact (Array.getElem?_eq_some_iff.1 hFj).1
            have hvj : visited[j]? = some true := by
              rw [Array.getElem?_eq_getElem hjlt] at hv ⊢
              simpa using hv
            have hkeep := visitStep_keep cur next j fv rest visited first order hvj
            rw [hrun, hFj] at hkeep
            have hcontains : (C[j]?.getD []).contains q = true := by
              rw [hI1 j hvj, ← hkeep]
              simp
            simp only [hcontains, if_true]
            exact ih m rest restc visited first C order hfs hcs hrun (by omega) (by omega) hp'
              (fun e he => hI4 e (List.mem_cons_of_mem _ he)) hI1 hI2
      | false =>
        rw [if_neg (by simp [hv])] at hrun
        dsimp only at hrun
        generalize hadef : x.filter (fun p => (cur.node p).kind == (next.node j).kind) = a at hrun
        have hvj : visited[j]? = some false := by
          cases h : visited[j]? with
          | none => rw [h] at hv; simp at hv
          | some b => rw [h] at hv; simp at hv; rw [hv]
        have hjlt : j < visited.size := (Array.getElem?_eq_some_iff.1 hvj).1
        obtain ⟨hCj, hfj⟩ := hI2 j hvj
        have hvis : (visited.setIfInBounds j true)[j]? = some true := by simp [hjlt]
        have hweight := unvisitedRefs_visit next visited j hvj
        have hFj : F[j]? = some a := by
          have := visitStep_keep cur next j fv (visitChildren cur (next.node j) a ++ rest)
            (visited.setIfInBounds j true) (first.setIfInBounds j a) (j :: order) hvis
          rw [hrun] at this
          rw [this]
          simp [hfs, hjlt]
        have hΦ' : (visitChildren cur (next.node j) a ++ rest).length +
            unvisitedRefs next (visited.setIfInBounds j true) ≤ fv := by
          rw [List.length_append, length_visitChildren]
          omega
        cases hp with
        | dead hp' =>
          simp only [Option.filter_none] at hadef
          subst hadef
          have hinv := visit_invariants (C' := C) (a := none) hjlt hfs hI1 hI2 (by simpa using hCj)
            (fun _ _ => rfl)
          exact ih (m + 1) _ wc _ _ C _ (by simp [hfs]) (by simp [hcs]) hrun hΦ' (by omega)
            (pending_dead cur _ hp') hI4 hinv.1 hinv.2
        | both hxy hp' =>
          rename_i y restc
          rw [candidateStep_cons]
          cases a with
          | none =>
            have hy : y.filter (fun p => (cur.node p).kind == (next.node j).kind) = none := by
              rcases hxy with hx | hx
              · cases hq : y.filter (fun p => (cur.node p).kind == (next.node j).kind) with
                | none => rfl
                | some q =>
                  have := hI4 (j, y) List.mem_cons_self q hq
                  rw [hFj] at this
                  cases this
              · rw [← hx, hadef]
            rw [hy]
            have hinv := visit_invariants (C' := C) (a := none) hjlt hfs hI1 hI2
              (by simpa using hCj) (fun _ _ => rfl)
            exact ih m _ restc _ _ C _ (by simp [hfs]) (by simp [hcs]) hrun hΦ' (by omega)
              (pending_dead cur _ hp') (fun e he => hI4 e (List.mem_cons_of_mem _ he))
              hinv.1 hinv.2
          | some p =>
            have hx : x = y := by
              rcases hxy with hx | hx
              · subst hx
                simp at hadef
              · exact hx
            subst hx
            rw [hadef]
            simp only [hCj, Option.getD_some, List.contains_nil, Bool.false_eq_true, if_false,
              List.nil_append]
            have hinv := visit_invariants (C' := C.setIfInBounds j [p]) (a := some p) hjlt hfs
              hI1 hI2 (by simp [hcs, hjlt]) (fun k hk => by simp [Ne.symm hk])
            refine ih m _ _ _ _ _ _ (by simp [hfs]) (by simp [hcs]) hrun hΦ' (by omega)
              (pending_children cur _ p hp') ?_ hinv.1 hinv.2
            intro e he q hq
            rcases List.mem_append.1 he with he | he
            · obtain ⟨c, y'⟩ := e
              obtain ⟨pos, hmem, rfl⟩ := mem_candidateChildren he
              exact hF j p hFj pos c hmem q hq
            · exact hI4 e (List.mem_cons_of_mem _ he) q hq

/-! ## Discovery -/

/-- From the root, `candidateStep` finds each node's alignment and nothing else when no reference
of an aligned node offers another object of the child's kind. -/
theorem candidateStep_eq_aligned (cur next : Graph) (r : Nat) (root : Option Nat)
    (hr : r < next.nodes.size) (fc : Nat) (hfc : next.budget ≤ fc)
    (h : OffersAligned cur next (visitStep cur next next.budget [(r, root)]
      (Array.replicate next.nodes.size false) (Array.replicate next.nodes.size none) []).2) :
    candidateStep cur next fc [(r, root)] (Array.replicate next.nodes.size []) =
      (visitStep cur next next.budget [(r, root)] (Array.replicate next.nodes.size false)
        (Array.replicate next.nodes.size none) []).2.map Option.toList := by
  refine simulate cur next _ h next.budget fc [(r, root)] [(r, root)] _ _ _ [] (by simp)
    (by simp) rfl ?_ hfc (Pending.both (Or.inr rfl) Pending.nil) ?_ ?_ ?_
  · rw [unvisitedRefs_start]
    simp [Graph.budget]
    omega
  · intro e he q hq
    simp only [List.mem_singleton] at he
    subst he
    obtain ⟨b, hb⟩ : ∃ b, next.budget = b + 1 := ⟨next.budget - 1, by simp [Graph.budget]⟩
    have hvis : ((Array.replicate next.nodes.size false).setIfInBounds r true)[r]? = some true := by
      simp [hr]
    have hkeep := visitStep_keep cur next r b
      (visitChildren cur (next.node r) (root.filter fun p => (cur.node p).kind == (next.node r).kind) ++ [])
      _ ((Array.replicate next.nodes.size none).setIfInBounds r
        (root.filter fun p => (cur.node p).kind == (next.node r).kind)) [r] hvis
    rw [hb, visitStep_cons, if_neg (by simp [hr])]
    dsimp only
    rw [hkeep]
    simp only at hq
    simp [hr, hq]
  · intro k hk
    simp [Array.getElem?_replicate] at hk
  · intro k hk
    have : k < next.nodes.size := by
      simp [Array.getElem?_replicate] at hk
      exact hk
    simp [this]

/-- `discover`'s candidates are the alignments of the nodes that are not pinned when no reference
of an aligned node offers, at its position, a current object of the child's kind other than the
one the child is aligned with. -/
theorem candidates_eq_aligned (input : Input) (hclosed : input.next.closed = true)
    (h : OffersAligned input.cur input.next (discover input).first) :
    (discover input).candidates = (discover input).first.mapIdx fun j a =>
      if (discover input).pinned[j]?.getD false then [] else a.toList := by
  unfold discover at h ⊢
  cases hroot : input.next.root with
  | prim p =>
    apply Array.ext_getElem?
    intro k
    simp [Array.getElem?_replicate]
  | ref r =>
    rw [hroot] at h
    have hr : r < input.next.nodes.size := by
      simp [Graph.closed, hroot] at hclosed
      exact hclosed.1
    simp only at h ⊢
    rw [candidateStep_eq_aligned _ _ r _ hr _ (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)) h]
    apply Array.ext_getElem?
    intro k
    simp [Array.getElem?_mapIdx, Array.getElem?_map, Function.comp_def]

/-- `next` holds one object at two keys where `current` holds two objects of its kind. -/
def offersOther : Input where
  cur := ⟨#[.object .object [("a", .data (.ref 1) Attrs.plain), ("b", .data (.ref 2) Attrs.plain)]
      true, .object .object [] true, .object .object [] true], .ref 0⟩
  next := ⟨#[.object .object [("a", .data (.ref 1) Attrs.plain), ("b", .data (.ref 1) Attrs.plain)]
      true, .object .object [] true], .ref 0⟩
  same := #[none, none]

/-- The premise is needed: in `offersOther`, the object at `b` is a second candidate of the node
aligned with the object at `a`. -/
theorem offersAligned_needed :
    (discover offersOther).first = #[some 0, some 1] ∧
    (discover offersOther).candidates = #[[0], [1, 2]] := by
  decide +kernel

end Reconcile.Spec.Reconcile
