import Graph.GraphPolicy
import Heap.ReuseClosure
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Fin

/-! The verified immutable publication core (`src/restore-identities.ts`): given a selected plan
and the native facts that `checkChoiceFacts` and `checkCompiled` check, publication writes only
fresh choices at the selected image, and selected identities and storage are injective. -/

namespace Reconcile.Immutable

open Policy

def chosen (plan : Plan) (i : Fin plan.length) : Choice := plan[i.val]
def image (plan : Plan) (i : Fin plan.length) : Nat := (chosen plan i).identity
def survivors (plan : Plan) : Finset (Fin plan.length) :=
  Finset.univ.filter fun i => (chosen plan i).retained

-- Native capture/allocation supply these finite labels and payloads. This is
-- not a model of recipes, getters, proxies, or JavaScript memory.
structure Input (A : Type) (plan : Plan) where
  source : Heap A (Fin plan.length)
  before : Heap A Nat
  proposed : Fin plan.length → Nat
  fresh : Fin plan.length → Nat
  storage : Nat → Nat
  proto : Fin plan.length → ProtoLabel → ProtoLabel
  records : List (Fin plan.length × Node A (Fin plan.length))

def ChoiceFacts {A : Type} {plan : Plan} (input : Input A plan)
    (i : Fin plan.length) (choice : Choice) : Prop :=
  choice.identity = (if choice.retained then input.proposed i else input.fresh i) ∧
  choice.storage = input.storage choice.identity ∧
  (choice.retained = true → ∀ nd, input.source.lookup i = some nd →
    input.before.lookup (input.proposed i) = some (nd.remap input.proposed (input.proto i)) ∧
    ∀ child ∈ nd.childRefs,
      { node := child.val, identity := input.proposed child } ∈ choice.required)

-- Local payload comparison is under proposed child identities. The compiler
-- must emit a Requires fact for each child; no final-image correctness is assumed.
def Compiled {A : Type} {plan : Plan} (input : Input A plan) (domains : Domains) : Prop :=
  ∀ i domain choice, domains[i.val]? = some domain → choice ∈ domain → ChoiceFacts input i choice

theorem chosen_mem (plan : Plan) (i : Fin plan.length) : chosen plan i ∈ plan :=
  List.getElem_mem i.isLt

theorem chosen_facts {A : Type} {plan : Plan} {domains : Domains} (input : Input A plan)
    (ha : allowed domains plan) (hc : Compiled input domains) (i : Fin plan.length) :
    ChoiceFacts input i (chosen plan i) := by
  obtain ⟨domain, hd, hm⟩ := allowed_at ha (List.getElem?_eq_getElem i.isLt)
  exact hc i domain (chosen plan i) hd hm

theorem image_eq_reuseImage {A : Type} {plan : Plan} {domains : Domains} (input : Input A plan)
    (ha : allowed domains plan) (hc : Compiled input domains) :
    image plan = reuseImage (survivors plan) input.proposed input.fresh := by
  funext i
  have hi := (chosen_facts input ha hc i).1
  simpa [image, reuseImage, survivors] using hi

theorem storage_injective {A : Type} {plan : Plan} {domains : Domains} (input : Input A plan)
    (ha : allowed domains plan) (hf : feasible plan) (hc : Compiled input domains) :
    Function.Injective (fun i => input.storage (image plan i)) := by
  have hnodup : (plan.map Choice.storage).Nodup := by
    simpa only [List.nodup_iff_pairwise_ne, List.pairwise_map] using hf.1
  intro i j hij
  apply Fin.ext
  have hi := (chosen_facts input ha hc i).2.1
  have hj := (chosen_facts input ha hc j).2.1
  have he : (plan.map Choice.storage)[i.val]'(by rw [List.length_map]; exact i.isLt) =
      (plan.map Choice.storage)[j.val]'(by rw [List.length_map]; exact j.isLt) := by
    simpa only [List.getElem_map, chosen] using hi.trans (hij.trans hj.symm)
  exact hnodup.getElem_inj_iff.mp he

theorem image_injective {A : Type} {plan : Plan} {domains : Domains} (input : Input A plan)
    (ha : allowed domains plan) (hf : feasible plan) (hc : Compiled input domains) :
    Function.Injective (image plan) := by
  intro i j hij
  exact storage_injective input ha hf hc (congrArg input.storage hij)

theorem retained_payload {A : Type} {plan : Plan} {domains : Domains} (input : Input A plan)
    (ha : allowed domains plan) (hf : feasible plan) (hc : Compiled input domains)
    {i : Fin plan.length} {nd : Node A (Fin plan.length)}
    (hn : input.source.lookup i = some nd) (hs : i ∈ survivors plan) :
    input.before.lookup (image plan i) = some (nd.remap (image plan) (input.proto i)) := by
  have hr : (chosen plan i).retained = true := by simpa [survivors] using hs
  have facts := chosen_facts input ha hc i
  obtain ⟨hlocal, hedges⟩ := facts.2.2 hr nd hn
  have hi : image plan i = input.proposed i := by simpa [image, hr] using facts.1
  rw [hi, hlocal]
  congr 1
  apply Node.remap_congr
  intro child hm
  have hrequired := hf.2 (chosen plan i) (chosen_mem plan i) _ (hedges child hm)
  have hchild : image plan child = input.proposed child := by
    simpa [image, chosen, List.getElem?_eq_getElem child.isLt] using hrequired
  exact hchild.symm

-- Publication uses exactly the selected image and writes only fresh choices.
def publish {A : Type} {plan : Plan} (input : Input A plan) : Heap A Nat :=
  publishRecords (image plan) input.proto
    (input.records.filter fun entry => entry.1 ∉ survivors plan) input.before

theorem publish_eq_fresh {A : Type} {plan : Plan} {domains : Domains} (input : Input A plan)
    (ha : allowed domains plan) (hc : Compiled input domains) :
    publish input = publishFresh (survivors plan) input.proposed input.fresh
      input.proto input.records input.before := by
  simp only [publish, publishFresh, image_eq_reuseImage input ha hc]

theorem selected_published {A : Type} {plan : Plan} {domains : Domains} (input : Input A plan)
    (selected : select domains = some plan) (hc : Compiled input domains)
    (covers : ∀ i nd, input.source.lookup i = some nd → (i, nd) ∈ input.records)
    (unique : input.records.Pairwise (fun a b => a.1 ≠ b.1)) :
    Published input.source (publish input) (image plan) input.proto := by
  obtain ⟨ha, hf⟩ := select_sound selected
  have hinj := image_injective input ha hf hc
  have heq := image_eq_reuseImage input ha hc
  rw [publish_eq_fresh input ha hc, heq]
  apply publishFresh_published input.source _ input.proposed input.fresh input.proto
    input.records input.before covers
  · rw [← heq]
    exact unique.imp (fun hne he => hne (hinj he))
  · rw [← heq]
    exact hinj
  · rw [← heq]
    intro i nd hn hs
    exact retained_payload input ha hf hc hn hs

-- Requiring fresh storage outside the input domain is stronger than merely
-- giving shells new visible labels. Native allocation must justify this premise.
theorem selected_frame {A : Type} {plan : Plan} {domains : Domains} (input : Input A plan)
    (selected : select domains = some plan) (hc : Compiled input domains)
    (freshStorage : ∀ i r, r ∈ input.before.keys →
      input.storage (input.fresh i) ≠ input.storage r)
    {r : Nat} (hr : r ∈ input.before.keys) :
    (publish input).lookup r = input.before.lookup r := by
  have ha := (select_sound selected).1
  rw [publish_eq_fresh input ha hc]
  apply publishFresh_frame _ input.proposed input.fresh input.proto input.records input.before _ hr
  intro i hi
  exact freshStorage i (input.fresh i) hi rfl

theorem selected_storage_distinct {A : Type} {plan : Plan} {domains : Domains}
    (input : Input A plan) (selected : select domains = some plan) (hc : Compiled input domains) :
    Function.Injective (fun i => input.storage (image plan i)) :=
  storage_injective input (select_sound selected).1 (select_sound selected).2 hc

-- Executable finite certificate checks let shared fixtures validate the exact
-- native-fact premises used above, rather than merely checking output examples.
def checkChoiceFacts {A : Type} [DecidableEq A] {plan : Plan} (input : Input A plan)
    (i : Fin plan.length) (choice : Choice) : Bool :=
  decide (choice.identity = (if choice.retained then input.proposed i else input.fresh i)) &&
  decide (choice.storage = input.storage choice.identity) &&
  (!choice.retained || match input.source.lookup i with
    | none => true
    | some nd =>
      decide (input.before.lookup (input.proposed i) = some (nd.remap input.proposed (input.proto i))) &&
      nd.childRefs.all fun child => choice.required.contains
        { node := child.val, identity := input.proposed child })

theorem checkChoiceFacts_iff {A : Type} [DecidableEq A] {plan : Plan} (input : Input A plan)
    (i : Fin plan.length) (choice : Choice) :
    checkChoiceFacts input i choice = true ↔ ChoiceFacts input i choice := by
  cases hr : choice.retained <;> cases hn : input.source.lookup i <;>
    simp [checkChoiceFacts, ChoiceFacts, hr, hn, List.all_eq_true, and_assoc]

def checkCompiled {A : Type} [DecidableEq A] {plan : Plan} (input : Input A plan)
    (domains : Domains) : Bool :=
  (List.finRange plan.length).all fun i =>
    ((domains[i.val]?).getD []).all (checkChoiceFacts input i)

theorem checkCompiled_iff {A : Type} [DecidableEq A] {plan : Plan} (input : Input A plan)
    (domains : Domains) : checkCompiled input domains = true ↔ Compiled input domains := by
  simp only [checkCompiled, List.all_eq_true, checkChoiceFacts_iff]
  constructor
  · intro h i domain choice hd hm
    have hi := h i (List.mem_finRange i)
    simpa [hd] using hi choice (by simpa [hd] using hm)
  · intro h i _ choice hm
    cases hd : domains[i.val]? with
    | none => simp [hd] at hm
    | some domain => exact h i domain choice hd (by simpa [hd] using hm)

-- Settled specials occupy a fixed prefix. Their payloads are supplied by native
-- finalization, while their ownership and buffer edges remain in the finite graph.
def fixedDomains (fixed : Plan) (domains : Domains) : Domains :=
  fixed.map (fun choice => [choice]) ++ domains

theorem allowed_fixed_prefix (fixed : Plan) (domains : Domains) (plan : Plan) :
    allowed (fixedDomains fixed domains) plan ↔
      ∃ rest, plan = fixed ++ rest ∧ allowed domains rest := by
  induction fixed generalizing plan with
  | nil => simp [fixedDomains]
  | cons head fixed ih =>
    cases plan with
    | nil => simp [fixedDomains, allowed]
    | cons choice plan =>
      simp only [fixedDomains, List.map_cons, List.cons_append, allowed,
        List.mem_singleton] at *
      constructor
      · rintro ⟨rfl, hp⟩
        obtain ⟨rest, rfl, hr⟩ := (ih plan).mp hp
        exact ⟨rest, rfl, hr⟩
      · rintro ⟨rest, he, hr⟩
        cases he
        exact ⟨rfl, (ih _).mpr ⟨rest, rfl, hr⟩⟩

-- The fixed score is constant: maximizing the whole graph still maximizes the
-- variable structural choices. No algorithm-created special earns a preference.
theorem selected_variable_optimal {fixed plan : Plan} {domains : Domains}
    (selected : select (fixedDomains fixed domains) = some plan) :
    ∃ rest, plan = fixed ++ rest ∧ allowed domains rest ∧
      ∀ other, allowed domains other → feasible (fixed ++ other) → score other ≤ score rest := by
  obtain ⟨rest, hp, hr⟩ := (allowed_fixed_prefix fixed domains plan).mp (select_sound selected).1
  refine ⟨rest, hp, hr, ?_⟩
  intro other ho hf
  have h := select_optimal selected
    ((allowed_fixed_prefix fixed domains (fixed ++ other)).mpr ⟨other, rfl, ho⟩) hf
  rw [hp, score_append, score_append] at h
  omega

-- A closed, storage-separated fixed subgraph plus private fresh structural
-- shells always supplies a feasible fallback. Buffer edges stay inside fixed.
theorem fixed_fresh_feasible (fixed : Plan) (rows : List (Nat × Option Choice))
    (hf : feasible fixed) (hu : (rows.map Prod.fst).Nodup)
    (hd : ∀ choice ∈ fixed, ∀ row ∈ rows, choice.storage ≠ row.1) :
    feasible (fixed ++ freshAssignment rows) := by
  constructor
  · apply List.pairwise_append.mpr
    refine ⟨hf.1, (freshAssignment_feasible rows hu).1, ?_⟩
    intro choice hc fresh hm
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hm
    exact hd choice hc row hr
  · intro choice hc edge he
    rcases List.mem_append.mp hc with hc | hc
    · have h := hf.2 choice hc edge he
      obtain ⟨target, ht, _⟩ := Option.map_eq_some_iff.mp h
      have hb := (List.getElem?_eq_some_iff.mp ht).1
      rw [List.getElem?_append_left hb]
      exact h
    · obtain ⟨row, _, rfl⟩ := List.mem_map.mp hc
      simp [freshChoice] at he

theorem fixed_fallback_select_exists (fixed : Plan) (rows : List (Nat × Option Choice))
    (hf : feasible fixed) (hu : (rows.map Prod.fst).Nodup)
    (hd : ∀ choice ∈ fixed, ∀ row ∈ rows, choice.storage ≠ row.1) :
    ∃ plan, select (fixedDomains fixed (fallbackDomains rows)) = some plan := by
  cases hs : select (fixedDomains fixed (fallbackDomains rows)) with
  | none =>
    apply False.elim
    apply (select_complete _).mp hs
    exact ⟨fixed ++ freshAssignment rows,
      (allowed_fixed_prefix _ _ _).mpr ⟨freshAssignment rows, rfl, freshAssignment_allowed rows⟩,
      fixed_fresh_feasible fixed rows hf hu hd⟩
  | some plan => exact ⟨plan, rfl⟩

end Reconcile.Immutable
