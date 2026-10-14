import Immutable
import Mathlib.Data.List.FinRange
import RequirementAdmission

/-! Finite retained-bit representation. Native acquisition remains outside
this model. Reserved labels express private fresh identities/storage, not a claim
that equal native values have independent storage. -/
namespace Reconcile.CompactImmutable

open Policy

structure Row (size : Nat) where
  proposed : Nat
  storage : Nat
  eligible : Bool
  fixed : Bool
  children : List (Fin size)
  deriving Repr

structure Problem (size : Nat) where
  row : Fin size → Row size
  proposedReserved : ∀ i, size ≤ (row i).proposed
  storageReserved : ∀ i, size ≤ (row i).storage

abbrev Mask (size : Nat) := Fin size → Bool

def choice {size : Nat} (p : Problem size) (i : Fin size) (keep : Bool) : Choice :=
  if keep then
    { identity := (p.row i).proposed, storage := (p.row i).storage, retained := true,
      required := (p.row i).children.map fun child =>
        { node := child.val, identity := (p.row child).proposed } }
  else { identity := i.val, storage := i.val, retained := false, required := [] }

def plan {size : Nat} (p : Problem size) (keep : Mask size) : Plan :=
  (List.finRange size).map fun i => choice p i (keep i)

def Admissible {size : Nat} (p : Problem size) (keep : Mask size) : Prop :=
  (∀ i, keep i = true → (p.row i).eligible = true) ∧
  (∀ i, (p.row i).fixed = true → keep i = true)

def Closed {size : Nat} (p : Problem size) (keep : Mask size) : Prop :=
  ∀ i, keep i = true → ∀ child ∈ (p.row i).children, keep child = true

def Separated {size : Nat} (p : Problem size) (keep : Mask size) : Prop :=
  ∀ i j, keep i = true → keep j = true →
    (p.row i).storage = (p.row j).storage → i = j

@[simp] theorem choice_retained {size : Nat} (p : Problem size) (i : Fin size)
    (keep : Bool) : (choice p i keep).retained = keep := by
  cases keep <;> rfl

@[simp] theorem plan_length {size : Nat} (p : Problem size) (keep : Mask size) :
    (plan p keep).length = size := by simp [plan]

@[simp] theorem plan_at {size : Nat} (p : Problem size) (keep : Mask size)
    (i : Fin size) : (plan p keep)[i.val]? = some (choice p i (keep i)) := by
  simp [plan]

theorem identity_iff {size : Nat} (p : Problem size) (i : Fin size) (keep : Bool) :
    (choice p i keep).identity = (p.row i).proposed ↔ keep = true := by
  have bound := p.proposedReserved i
  have indexBound := i.isLt
  cases keep with
  | false => simp [choice]; omega
  | true => simp [choice]

theorem storage_injective_iff {size : Nat} (p : Problem size) (keep : Mask size) :
    Function.Injective (fun i => (choice p i (keep i)).storage) ↔ Separated p keep := by
  constructor
  · intro injective i j hi hj same
    apply injective
    simpa [choice, hi, hj] using same
  · intro separated i j same
    have bi := p.storageReserved i
    have bj := p.storageReserved j
    have li := i.isLt
    have lj := j.isLt
    cases hi : keep i <;> cases hj : keep j
    · apply Fin.ext
      simpa [choice, hi, hj] using same
    · simp [choice, hi, hj] at same
      omega
    · simp [choice, hi, hj] at same
      omega
    · exact separated i j hi hj (by simpa [choice, hi, hj] using same)

theorem storage_pairwise_iff {size : Nat} (p : Problem size) (keep : Mask size) :
    (plan p keep).Pairwise (fun a b => a.storage ≠ b.storage) ↔ Separated p keep := by
  rw [← storage_injective_iff]
  have h := List.nodup_map_iff_inj_on (List.nodup_finRange size)
    (f := fun i => (choice p i (keep i)).storage)
  simpa [plan, List.nodup_iff_pairwise_ne, List.pairwise_map,
    Function.Injective] using h

theorem requirements_iff {size : Nat} (p : Problem size) (keep : Mask size) :
    (∀ candidate ∈ plan p keep, ∀ edge ∈ candidate.required,
      ((plan p keep)[edge.node]?).map Choice.identity = some edge.identity) ↔
      Closed p keep := by
  constructor
  · intro valid i hi child hc
    have member : choice p i (keep i) ∈ plan p keep :=
      List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    have required : ({ node := child.val, identity := (p.row child).proposed } : Requirement)
        ∈ (choice p i (keep i)).required := by
      simp only [choice, hi, ↓reduceIte]
      exact List.mem_map.mpr ⟨child, hc, rfl⟩
    have h := valid _ member _ required
    simp only [plan_at, Option.map_some, Option.some.injEq] at h
    exact (identity_iff p child (keep child)).mp h
  · intro closed candidate member edge he
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
    cases hi : keep i
    · simp [choice, hi] at he
    · simp only [choice, hi, ↓reduceIte] at he
      obtain ⟨child, hc, rfl⟩ := List.mem_map.mp he
      simp only [plan_at, Option.map_some, Option.some.injEq]
      exact (identity_iff p child (keep child)).mpr (closed i hi child hc)

theorem feasible_iff {size : Nat} (p : Problem size) (keep : Mask size) :
    feasible (plan p keep) ↔ Separated p keep ∧ Closed p keep := by
  exact and_congr (storage_pairwise_iff p keep) (requirements_iff p keep)

def options {size : Nat} (row : Row size) : List Bool :=
  (if row.eligible then [true] else []) ++ (if row.fixed then [] else [false])

@[simp] theorem mem_options {size : Nat} (row : Row size) (keep : Bool) :
    keep ∈ options row ↔
      (keep = true → row.eligible = true) ∧ (row.fixed = true → keep = true) := by
  cases row with
  | mk proposed storage eligible fixed children =>
    cases eligible <;> cases fixed <;> cases keep <;> simp [options]

def domains {size : Nat} (p : Problem size) : Domains :=
  (List.finRange size).map fun i => (options (p.row i)).map (choice p i)

theorem allowed_map {A : Type} (indices : List A) (domain : A → List Choice)
    (chosen : A → Choice) :
    allowed (indices.map domain) (indices.map chosen) ↔
      ∀ i ∈ indices, chosen i ∈ domain i := by
  induction indices with
  | nil => simp [allowed]
  | cons i indices ih => simp [allowed, ih]

theorem choice_injective {size : Nat} (p : Problem size) (i : Fin size) :
    Function.Injective (choice p i) := by
  intro a b same
  simpa using congrArg Choice.retained same

theorem allowed_iff {size : Nat} (p : Problem size) (keep : Mask size) :
    allowed (domains p) (plan p keep) ↔ Admissible p keep := by
  simp only [domains, plan, allowed_map, List.mem_finRange, forall_const,
    List.mem_map_of_injective (choice_injective p _), mem_options]
  exact forall_and

theorem allowed_representation {size : Nat} (p : Problem size) (selected : Plan)
    (ha : allowed (domains p) selected) :
    ∃ keep : Mask size, Admissible p keep ∧ plan p keep = selected := by
  have length : selected.length = size := by
    simpa [domains] using allowed_length ha
  let keep : Mask size := fun i => (selected[i.val]'(by omega)).retained
  have equal : plan p keep = selected := by
    apply List.ext_getElem
    · simp [length]
    · intro index left right
      have bound : index < size := by simpa using left
      let i : Fin size := ⟨index, bound⟩
      obtain ⟨domain, hd, hm⟩ := allowed_at ha (List.getElem?_eq_getElem right)
      have domainAt : (domains p)[i.val]? =
          some ((options (p.row i)).map (choice p i)) := by simp [domains]
      have hd' : domain = (options (p.row i)).map (choice p i) :=
        Option.some.inj (hd.symm.trans domainAt)
      rw [hd'] at hm
      obtain ⟨bit, _, hb⟩ := List.mem_map.mp hm
      have retained : keep i = bit := by
        simpa [keep, i] using congrArg Choice.retained hb.symm
      have lookup : (plan p keep)[index]? = some (choice p i bit) := by
        simpa only [retained] using plan_at p keep i
      rw [List.getElem?_eq_getElem left] at lookup
      exact (Option.some.inj lookup).trans hb
  exact ⟨keep, (allowed_iff p keep).mp (equal ▸ ha), equal⟩

/-- Stable ordered enumeration uses bits rather than Choice objects. -/
def assignments {size : Nat} (p : Problem size) : List (Fin size) → List (List Bool)
  | [] => [[]]
  | i :: rest => (options (p.row i)).flatMap fun bit =>
      (assignments p rest).map (bit :: ·)

def decode {size : Nat} (p : Problem size) (indices : List (Fin size))
    (bits : List Bool) : Plan := List.zipWith (choice p) indices bits

theorem assignments_decode {size : Nat} (p : Problem size) (indices : List (Fin size)) :
    (assignments p indices).map (decode p indices) =
      Policy.assignments (indices.map fun i => (options (p.row i)).map (choice p i)) := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
    simp only [assignments, Policy.assignments, List.map_cons, List.map_flatMap,
      List.flatMap_map, List.map_map]
    congr 1
    funext bit
    rw [← ih, List.map_map]
    rfl

theorem assignments_length {size : Nat} (p : Problem size) (indices : List (Fin size))
    (bits : List Bool) (member : bits ∈ assignments p indices) :
    bits.length = indices.length := by
  induction indices generalizing bits with
  | nil => simpa [assignments] using member
  | cons i rest ih =>
    obtain ⟨bit, _, hm⟩ := List.mem_flatMap.mp member
    obtain ⟨tail, ht, rfl⟩ := List.mem_map.mp hm
    simpa using ih tail ht

def mask {size : Nat} (bits : List Bool) : Mask size :=
  fun i => bits[i.val]?.getD false

theorem decode_plan {size : Nat} (p : Problem size) (bits : List Bool)
    (length : bits.length = size) :
    decode p (List.finRange size) bits = plan p (mask bits) := by
  apply List.ext_getElem
  · simp [decode, length]
  · intro index left right
    have bound : index < bits.length := by simpa [decode, length] using left
    simp [decode, plan, mask, List.getElem?_eq_getElem bound]

instance {size : Nat} (p : Problem size) (keep : Mask size) : Decidable (Closed p keep) :=
  inferInstanceAs (Decidable (∀ i, keep i = true →
    ∀ child ∈ (p.row i).children, keep child = true))

instance {size : Nat} (p : Problem size) (keep : Mask size) : Decidable (Separated p keep) :=
  inferInstanceAs (Decidable (∀ i j, keep i = true → keep j = true →
    (p.row i).storage = (p.row j).storage → i = j))

def check {size : Nat} (p : Problem size) (bits : List Bool) : Bool :=
  decide (Separated p (mask bits) ∧ Closed p (mask bits))

theorem check_decode {size : Nat} (p : Problem size) (bits : List Bool)
    (length : bits.length = size) :
    check p bits = Policy.check (decode p (List.finRange size) bits) := by
  apply Bool.eq_iff_iff.mpr
  simp only [check, decide_eq_true_eq, Policy.check_iff_feasible,
    decode_plan p bits length, feasible_iff]

def candidates {size : Nat} (p : Problem size) : List (List Bool) :=
  (assignments p (List.finRange size)).filter (check p)

theorem candidates_decode {size : Nat} (p : Problem size) :
    (candidates p).map (decode p (List.finRange size)) = feasiblePlans (domains p) := by
  rw [feasiblePlans, domains, ← assignments_decode, List.filter_map]
  apply congrArg (List.map (decode p (List.finRange size)))
  apply List.filter_congr
  intro bits member
  exact check_decode p bits (by simpa using assignments_length p _ bits member)

theorem decode_retained {size : Nat} (p : Problem size) (indices : List (Fin size))
    (bits : List Bool) (length : bits.length = indices.length) :
    (decode p indices bits).map Choice.retained = bits := by
  induction indices generalizing bits with
  | nil => cases bits <;> simp_all [decode]
  | cons i rest ih => cases bits <;> simp_all [decode]

def score (bits : List Bool) : Nat :=
  (bits.map fun bit => if bit then 1 else 0).sum

theorem decode_score {size : Nat} (p : Problem size) (indices : List (Fin size))
    (bits : List Bool) (length : bits.length = indices.length) :
    Policy.score (decode p indices bits) = score bits := by
  have retained := decode_retained p indices bits length
  have mapped := congrArg (fun bs : List Bool => score bs) retained
  simpa [Policy.score, score, List.map_map] using mapped

def ranked {size : Nat} (p : Problem size) : List (List Bool) :=
  (List.range (size + 1)).reverse.flatMap fun goal =>
    (candidates p).filter fun bits => decide (score bits = goal)

theorem ranked_decode {size : Nat} (p : Problem size) :
    (ranked p).map (decode p (List.finRange size)) = rankedPlans (domains p) := by
  have length : (domains p).length = size := by simp [domains]
  simp only [ranked, rankedPlans, length, List.map_flatMap]
  congr 1
  funext goal
  rw [← candidates_decode p, List.filter_map]
  apply congrArg (List.map (decode p (List.finRange size)))
  apply List.filter_congr
  intro bits member
  have length := assignments_length p _ bits (List.mem_filter.mp member).1
  exact congrArg (fun value => decide (value = goal))
    (decode_score p _ bits length).symm

/-- Construction remains an independent finite check on the retained mask. -/
def constructible {size : Nat} (p : Problem size) (build : List Bool → Bool) :
    List (List Bool) := (ranked p).filter build

theorem constructible_decode {size : Nat} (p : Problem size) (build : List Bool → Bool) :
    (constructible p build).map (decode p (List.finRange size)) =
      (rankedPlans (domains p)).filter fun selected => build (selected.map Choice.retained) := by
  rw [← ranked_decode p, List.filter_map]
  apply congrArg (List.map (decode p (List.finRange size)))
  apply List.filter_congr
  intro bits member
  obtain ⟨goal, _, hc⟩ := List.mem_flatMap.mp member
  have original := (List.mem_filter.mp hc).1
  have length := assignments_length p _ bits (List.mem_filter.mp original).1
  exact congrArg build (decode_retained p _ bits length).symm

theorem selected_decode {size : Nat} (p : Problem size) (build : List Bool → Bool) :
    ((constructible p build).head?).map (decode p (List.finRange size)) =
      ((rankedPlans (domains p)).filter fun selected =>
        build (selected.map Choice.retained)).head? := by
  rw [← constructible_decode p build]
  simp

/-- Every admitted feasible bit completion inherits the existing prefix pruning law. -/
theorem prefix_survives {size : Nat} (p : Problem size) (keep : Mask size)
    (admitted : Admissible p keep) (separated : Separated p keep)
    (closed : Closed p keep) (count : Nat) :
    ((plan p keep).take count).Pairwise (fun a b => a.storage ≠ b.storage) ∧
    ∀ candidate ∈ (plan p keep).take count, ∀ edge ∈ candidate.required,
      if edge.node < count then
        (((plan p keep).take count)[edge.node]?).map Choice.identity = some edge.identity
      else ∃ domain candidate, (domains p)[edge.node]? = some domain ∧
        candidate ∈ domain ∧ candidate.identity = edge.identity :=
  completion_survives_prefix_pruning ((allowed_iff p keep).mpr admitted)
    ((feasible_iff p keep).mpr ⟨separated, closed⟩) count

/-- All incoming requirements for one immutable child demand its single proposal. -/
theorem incoming_bit_iff {size : Nat} (p : Problem size) (owners : List (Fin size))
    (node : Fin size) (bit : Bool) :
    (∀ owner ∈ owners, ∀ child ∈ (p.row owner).children, child = node →
      (choice p node bit).identity = (p.row child).proposed) ↔
      ((∃ owner ∈ owners, node ∈ (p.row owner).children) → bit = true) := by
  constructor
  · intro accepted ⟨owner, ho, hc⟩
    exact (identity_iff p node bit).mp (accepted owner ho node hc rfl)
  · intro accepted owner ho child hc same
    subst child
    exact (identity_iff p node bit).mpr (accepted ⟨owner, ho, hc⟩)

/-- A Boolean demand trail records only new bits; undo preserves every older demand. -/
theorem undo_admission (known : Finset Nat) (incoming : List Nat) :
    SDiff.sdiff (known ∪ incoming.toFinset) (RequirementAdmission.admit known incoming).toFinset =
      known := by
  ext node
  simp only [Finset.mem_sdiff, Finset.mem_union, List.mem_toFinset,
    RequirementAdmission.admit_mem]
  tauto

end Reconcile.CompactImmutable
