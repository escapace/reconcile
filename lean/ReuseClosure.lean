import Publication
import Mathlib.Data.Finset.Card

/-! Least rejection closure and publication under a selected identity image.
These shared lemmas do not choose ownership or rank retention plans. -/
namespace Reconcile

variable {I : Type} [DecidableEq I]

/-- `remaining` are proposed identities still eligible for reuse. Queue entries
    outside it are skipped; the algorithm never revisits an expanded record. -/
def reuseSurvivors (parents : I → List I) (pending : List I) (remaining : Finset I) : Finset I :=
  match pending with
  | [] => remaining
  | child :: rest =>
    if child ∈ remaining then
      reuseSurvivors parents (parents child ++ rest) (remaining.erase child)
    else reuseSurvivors parents rest remaining
  termination_by (remaining.card, pending.length)
  decreasing_by
    · exact Prod.Lex.left _ _ (Finset.card_erase_lt_of_mem (by assumption))
    · exact Prod.Lex.right _ (by simp)

/-- Rejection is monotone: no rejected identity can be restored by a later queue entry. -/
theorem reuseSurvivors_subset (parents : I → List I) (pending : List I) (remaining : Finset I) :
    reuseSurvivors parents pending remaining ⊆ remaining := by
  fun_induction reuseSurvivors with
  | case1 => exact Finset.Subset.refl _
  | case2 _ _ _ _ ih => exact ih.trans (Finset.erase_subset _ _)
  | case3 _ _ _ _ ih => exact ih

/-- A set of reusable proposals is safe when it depends only on reusable children. -/
def DependencyClosed (parents : I → List I) (safe : Finset I) : Prop :=
  ∀ child parent, parent ∈ parents child → parent ∈ safe → child ∈ safe

/-- The worklist never removes any dependency-closed set avoiding the initial
    rejections. This is the maximal-reuse half of least rejection closure. -/
theorem reuseSurvivors_greatest (parents : I → List I) (pending : List I)
    (remaining safe : Finset I) (hsub : safe ⊆ remaining)
    (hclosed : DependencyClosed parents safe) (hseed : ∀ i ∈ pending, i ∉ safe) :
    safe ⊆ reuseSurvivors parents pending remaining := by
  fun_induction reuseSurvivors parents pending remaining with
  | case1 => exact hsub
  | case2 remaining child rest hm ih =>
    apply ih
    · intro x hx
      exact Finset.mem_erase.mpr ⟨fun he => hseed child (by simp) (he ▸ hx), hsub hx⟩
    · intro x hx
      rcases List.mem_append.mp hx with hp | hr
      · intro hs
        exact hseed child (by simp) (hclosed child x hp hs)
      · exact hseed x (by simp [hr])
  | case3 remaining child rest hm ih =>
    exact ih hsub (fun i hi => hseed i (by simp [hi]))

/-- Every queued rejection is absent at completion, even if encountered repeatedly. -/
theorem reuseSurvivors_excludes (parents : I → List I) (pending : List I)
    (remaining : Finset I) : ∀ i ∈ pending, i ∉ reuseSurvivors parents pending remaining := by
  fun_induction reuseSurvivors with
  | case1 => simp
  | case2 remaining child rest hm ih =>
    intro i hi hs
    rcases List.mem_cons.mp hi with he | hr
    · subst i
      have := reuseSurvivors_subset parents (parents child ++ rest) (remaining.erase child) hs
      simp at this
    · exact ih i (List.mem_append_right _ hr) hs
  | case3 remaining child rest hm ih =>
    intro i hi hs
    rcases List.mem_cons.mp hi with he | hr
    · subst i; exact hm (reuseSurvivors_subset parents rest remaining hs)
    · exact ih i hr hs

/-- Every removed eligible child's parents are also absent at completion. -/
theorem reuseSurvivors_propagates (parents : I → List I) (pending : List I)
    (remaining : Finset I) :
    ∀ child ∈ remaining, child ∉ reuseSurvivors parents pending remaining →
      ∀ parent ∈ parents child, parent ∉ reuseSurvivors parents pending remaining := by
  fun_induction reuseSurvivors with
  | case1 => simp_all
  | case2 remaining c rest hm ih =>
    intro child hc hgone parent hp
    by_cases he : child = c
    · subst child
      exact reuseSurvivors_excludes parents (parents c ++ rest) (remaining.erase c)
        parent (List.mem_append_left _ hp)
    · exact ih child (Finset.mem_erase.mpr ⟨he, hc⟩) hgone parent hp
  | case3 remaining c rest hm ih => exact ih

/-- If all dependencies belong to the finite domain, survivors are closed. -/
theorem reuseSurvivors_closed (parents : I → List I) (seeds : List I) (domain : Finset I)
    (hdeps : ∀ child parent, parent ∈ parents child → parent ∈ domain → child ∈ domain) :
    DependencyClosed parents (reuseSurvivors parents seeds domain) := by
  intro child parent hp hs
  by_contra hn
  have hc := hdeps child parent hp (reuseSurvivors_subset parents seeds domain hs)
  exact reuseSurvivors_propagates parents seeds domain child hc hn parent hp hs

/-- Undo/no-op restoration: no rejected proposals means every identity survives,
    regardless of modification bits or cycles. -/
theorem reuseSurvivors_undo (parents : I → List I) (domain : Finset I) :
    reuseSurvivors parents [] domain = domain := by simp [reuseSurvivors]

/-- Identity proposals come from provenance-aware capture. A rejected proposal
    receives its reserved fresh shell; there is no search for equal authored nodes. -/
def reuseImage {J : Type} (survivors : Finset I) (proposed fresh : I → J) (i : I) : J :=
  if i ∈ survivors then proposed i else fresh i

/-- Only rejected records require payload writes. -/
def publishFresh {A J : Type} [DecidableEq J] (survivors : Finset I)
    (proposed fresh : I → J) (proto : I → ProtoLabel → ProtoLabel)
    (records : List (I × Node A I)) (before : Heap A J) : Heap A J :=
  publishRecords (reuseImage survivors proposed fresh) proto
    (records.filter fun entry => entry.1 ∉ survivors) before

/-- Fresh-only publication preserves every existing input node, provided reserved
    shells occupy storage outside the input heap. This is the immutable core's
    isolation theorem; recipe and capture isolation remain adapter obligations. -/
theorem publishFresh_frame {A J : Type} [DecidableEq J] (survivors : Finset I)
    (proposed fresh : I → J) (proto : I → ProtoLabel → ProtoLabel)
    (records : List (I × Node A I)) (before : Heap A J)
    (hfresh : ∀ i, fresh i ∉ before.keys) {r : J} (hr : r ∈ before.keys) :
    (publishFresh survivors proposed fresh proto records before).lookup r = before.lookup r := by
  apply publishRecords_frame
  intro entry he
  have hn : entry.1 ∉ survivors := of_decide_eq_true (List.mem_filter.mp he).2
  simp only [reuseImage, if_neg hn]
  intro heq
  exact hfresh entry.1 (heq ▸ hr)

/-- The immutable finalizer publishes a coherent graph once surviving local
    payloads have been certified. Both reused and fresh nodes share one image. -/
theorem publishFresh_published {A J : Type} [DecidableEq J]
    (source : Heap A I) (survivors : Finset I) (proposed fresh : I → J)
    (proto : I → ProtoLabel → ProtoLabel) (records : List (I × Node A I)) (before : Heap A J)
    (covers : ∀ i nd, source.lookup i = some nd → (i, nd) ∈ records)
    (unique : records.Pairwise (fun a b =>
      reuseImage survivors proposed fresh a.1 ≠ reuseImage survivors proposed fresh b.1))
    (hinj : Function.Injective (reuseImage survivors proposed fresh))
    (hbase : ∀ i nd, source.lookup i = some nd → i ∈ survivors →
      before.lookup (reuseImage survivors proposed fresh i) =
        some (nd.remap (reuseImage survivors proposed fresh) (proto i))) :
    Published source (publishFresh survivors proposed fresh proto records before)
      (reuseImage survivors proposed fresh) proto := by
  intro i nd hn
  by_cases hs : i ∈ survivors
  · rw [publishFresh, publishRecords_frame]
    · exact hbase i nd hn hs
    · intro entry he heq
      have heq' := hinj heq
      have hnot : entry.1 ∉ survivors := of_decide_eq_true (List.mem_filter.mp he).2
      exact hnot (heq' ▸ hs)
  · apply publishRecords_lookup
    · exact unique.sublist List.filter_sublist
    · exact List.mem_filter.mpr ⟨covers i nd hn, by simpa using hs⟩

end Reconcile
