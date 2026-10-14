import CompactImmutable

/-! The distinct-owner bound removes only score tiers above the number
of eligible owning-storage identities. It adds no shape dispatch, SCC state or
exclusion propagation. Native owner observations still precede this pure bound. -/
namespace Reconcile.CompactOwners

open CompactImmutable

def retained {size : Nat} (bits : Mask size) : Finset (Fin size) :=
  Finset.univ.filter fun i => bits i

def owners {size : Nat} (p : Problem size) : Finset Nat :=
  (Finset.univ.filter fun i => (p.row i).eligible).image fun i => (p.row i).storage

theorem score_count (bits : List Bool) :
    CompactImmutable.score bits = (bits.filter id).length := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
    cases bit with
    | false => simp_all [CompactImmutable.score]
    | true => simp_all [CompactImmutable.score]; omega

theorem retained_card {size : Nat} (bits : Mask size) :
    CompactImmutable.score ((List.finRange size).map bits) = (retained bits).card := by
  have same : retained bits = ((List.finRange size).filter bits).toFinset := by
    ext i
    simp [retained]
  rw [same, List.toFinset_card_of_nodup ((List.nodup_finRange size).filter bits),
    score_count, List.filter_map, List.length_map]
  rfl

theorem owner_bound {size : Nat} (p : Problem size) (bits : Mask size)
    (admitted : Admissible p bits) (separated : Separated p bits) :
    CompactImmutable.score ((List.finRange size).map bits) ≤ (owners p).card := by
  rw [retained_card]
  have injective : Set.InjOn (fun i => (p.row i).storage) (retained bits) := by
    intro i hi j hj same
    have left : bits i = true := by simpa [retained] using hi
    have right : bits j = true := by simpa [retained] using hj
    exact separated i j left right same
  rw [← Finset.card_image_of_injOn injective]
  apply Finset.card_le_card
  apply Finset.image_mono
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, admitted.1 i (Finset.mem_filter.mp hi).2⟩

theorem owners_le_size {size : Nat} (p : Problem size) : (owners p).card ≤ size := by
  have bound := Finset.card_image_le
    (s := Finset.univ.filter fun i : Fin size => (p.row i).eligible)
    (f := fun i => (p.row i).storage)
  have filtered := Finset.card_le_card (Finset.filter_subset (fun i : Fin size => (p.row i).eligible) Finset.univ)
  simpa [owners] using Nat.le_trans bound filtered

def buckets (limit : Nat) (masks : List (List Bool)) : List (List Bool) :=
  (List.range (limit + 1)).reverse.flatMap fun goal =>
    masks.filter fun bits => decide (CompactImmutable.score bits = goal)

theorem cap_buckets (masks : List (List Bool)) (limit cap : Nat) (le : cap ≤ limit)
    (bounded : ∀ bits ∈ masks, CompactImmutable.score bits ≤ cap) :
    buckets limit masks = buckets cap masks := by
  induction limit with
  | zero => have equal : cap = 0 := by omega
            subst cap
            rfl
  | succ limit ih =>
    by_cases equal : cap = limit + 1
    · subst cap; rfl
    have lower : cap ≤ limit := by omega
    have empty : (masks.filter fun bits => decide (CompactImmutable.score bits = limit + 1)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro bits member
      have bound := bounded bits member
      simp only [decide_eq_true_eq]
      omega
    simp only [buckets, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, empty,
      List.nil_append]
    simpa only [buckets, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil] using ih lower

def ranked {size : Nat} (p : Problem size) : List (List Bool) :=
  buckets (owners p).card (candidates p)

theorem ranked_eq {size : Nat} (p : Problem size) :
    ranked p = CompactImmutable.ranked p := by
  apply (cap_buckets (candidates p) size (owners p).card (owners_le_size p) ?_).symm
  intro bits member
  have length : bits.length = size := by
    simpa using assignments_length p _ bits (List.mem_filter.mp member).1
  have decoded : decode p (List.finRange size) bits ∈ Policy.feasiblePlans (domains p) := by
    rw [← candidates_decode p]
    exact List.mem_map.mpr ⟨bits, member, rfl⟩
  have facts := (Policy.feasiblePlans_exact (domains p) _).mp decoded
  rw [decode_plan p bits length] at facts
  have bound := owner_bound p (mask bits) ((allowed_iff p _).mp facts.1)
    ((feasible_iff p _).mp facts.2).1
  have same := decode_retained p (List.finRange size) bits (by simpa using length)
  rw [decode_plan p bits length] at same
  have restored : (List.finRange size).map (mask bits) = bits := by
    simpa [plan, List.map_map, Function.comp_def] using same
  simpa [restored] using bound

theorem ranked_decode {size : Nat} (p : Problem size) :
    (ranked p).map (decode p (List.finRange size)) = Policy.rankedPlans (domains p) := by
  rw [ranked_eq, CompactImmutable.ranked_decode]

theorem selected_decode {size : Nat} (p : Problem size) (build : List Bool → Bool) :
    (((ranked p).filter build).head?).map (decode p (List.finRange size)) =
      ((Policy.rankedPlans (domains p)).filter fun selected =>
        build (selected.map Policy.Choice.retained)).head? := by
  rw [ranked_eq]
  exact CompactImmutable.selected_decode p build

end Reconcile.CompactOwners
