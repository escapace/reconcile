import Graph.Requirements

/-! Ordered admission for the positive closure worklist. This retains the first
occurrence, unlike a rightmost-deduplication specification. -/
namespace Reconcile.RequirementAdmission

def admit (known : Finset Nat) : List Nat → List Nat
  | [] => []
  | fact :: rest =>
    if fact ∈ known then admit known rest else fact :: admit (insert fact known) rest

theorem admit_mem (known : Finset Nat) (input : List Nat) (fact : Nat) :
    fact ∈ admit known input ↔ fact ∈ input ∧ fact ∉ known := by
  induction input generalizing known with
  | nil => simp [admit]
  | cons head rest ih =>
    by_cases hh : head ∈ known <;> by_cases hf : fact = head <;>
      simp_all [admit]

theorem admit_nodup (known : Finset Nat) (input : List Nat) : (admit known input).Nodup := by
  induction input generalizing known with
  | nil => simp [admit]
  | cons head rest ih =>
    by_cases hh : head ∈ known
    · simp [admit, hh, ih]
    · simp [admit, hh, List.nodup_cons, admit_mem, ih]

theorem admit_set (known : Finset Nat) (input : List Nat) :
    known ∪ (admit known input).toFinset = known ∪ input.toFinset := by
  ext fact
  simp only [Finset.mem_union, List.mem_toFinset, admit_mem]
  tauto

theorem admit_append (known : Finset Nat) (left right : List Nat) :
    admit known (left ++ right) =
      admit known left ++ admit (known ∪ left.toFinset) right := by
  induction left generalizing known with
  | nil => simp [admit]
  | cons head rest ih =>
    by_cases hh : head ∈ known
    · have he : known ∪ insert head rest.toFinset = known ∪ rest.toFinset := by
        ext fact
        simp only [Finset.mem_union, Finset.mem_insert]
        aesop
      simp [admit, hh, ih, he]
    · simp [admit, hh, ih, Finset.insert_union, Finset.union_insert]

theorem admission_bound (known vertices : Finset Nat) (input : List Nat)
    (bounded : ∀ fact ∈ input, fact ∈ vertices) :
    (admit known input).length ≤ vertices.card := by
  rw [← List.toFinset_card_of_nodup (admit_nodup known input)]
  apply Finset.card_le_card
  intro fact hf
  exact bounded fact ((admit_mem known input fact).mp (List.mem_toFinset.mp hf)).1

example : admit {3} [2, 1, 2, 3, 1, 4] = [2, 1, 4] := by decide

theorem admit_of_unique_fresh (known : Finset Nat) (input : List Nat)
    (unique : input.Nodup) (fresh : ∀ fact ∈ input, fact ∉ known) : admit known input = input := by
  induction input generalizing known with
  | nil => rfl
  | cons head rest ih =>
    rw [admit, if_neg (fresh head (by simp))]
    congr 1
    apply ih (insert head known) unique.tail
    intro fact hf
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun he => (List.nodup_cons.mp unique).1 (he ▸ hf), fresh fact (by simp [hf])⟩

theorem admit_idempotent (known : Finset Nat) (input : List Nat) :
    admit known (admit known input) = admit known input := by
  apply admit_of_unique_fresh known _ (admit_nodup known input)
  exact fun fact hf => ((admit_mem known input fact).mp hf).2

theorem admitted_queue_append (known : Finset Nat) (pending incoming : List Nat) :
    admit known (pending ++ incoming) =
      admit known pending ++ admit (known ∪ (admit known pending).toFinset) incoming := by
  rw [admit_append, admit_set]

/-- Once the old queue's unseen head is consumed, both strategies have this
same canonical pending sequence. The eager strategy already knows queued facts. -/
theorem queue_step (known : Finset Nat) (head : Nat) (rest incoming : List Nat)
    (fresh : head ∉ known) :
    admit (insert head known) (rest ++ incoming) =
      admit (insert head known) rest ++
        admit (known ∪ (admit known (head :: rest)).toFinset) incoming := by
  rw [admitted_queue_append]
  have he : known ∪ (admit known (head :: rest)).toFinset =
      insert head known ∪ (admit (insert head known) rest).toFinset := by
    simp [admit, fresh, Finset.union_insert, Finset.insert_union]
  rw [he]

end Reconcile.RequirementAdmission
