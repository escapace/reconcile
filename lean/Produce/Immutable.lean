import Graph.GraphPolicy
import Heap.Publication
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Fin

/-! The verified immutable publication core (`src/restore-identities.ts`). `publishFresh` keeps
each retained identity and writes only the fresh records, all through one image (`reuseImage`),
as the runtime's `publishFresh` does. For every plan of the ranked stream, which holds every mask
`publishFirst` may publish, and given the native facts that `checkChoiceFacts` and `checkCompiled`
check, the result reads back as its source (`selected_published`, `selected_surface`) and the
selected storage is injective (`selected_storage_distinct`). -/

namespace Reconcile.Immutable

open Policy

section Publication

variable {I : Type} [DecidableEq I]

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

end Publication

def chosen (plan : Plan) (i : Fin plan.length) : Choice := plan[i.val]
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

/-- The plan's identities are the runtime's image: the proposed identity of each retained record
and the fresh one of each other record. -/
theorem chosen_identity {A : Type} {plan : Plan} {domains : Domains} (input : Input A plan)
    (ha : allowed domains plan) (hc : Compiled input domains) (i : Fin plan.length) :
    (chosen plan i).identity = reuseImage (survivors plan) input.proposed input.fresh i := by
  simpa [reuseImage, survivors] using (chosen_facts input ha hc i).1

theorem storage_injective {A : Type} {plan : Plan} {domains : Domains} (input : Input A plan)
    (ha : allowed domains plan) (hf : feasible plan) (hc : Compiled input domains) :
    Function.Injective
      (fun i => input.storage (reuseImage (survivors plan) input.proposed input.fresh i)) := by
  have hnodup : (plan.map Choice.storage).Nodup := by
    simpa only [List.nodup_iff_pairwise_ne, List.pairwise_map] using hf.1
  intro i j hij
  dsimp only at hij
  rw [← chosen_identity input ha hc i, ← chosen_identity input ha hc j] at hij
  apply Fin.ext
  have hi := (chosen_facts input ha hc i).2.1
  have hj := (chosen_facts input ha hc j).2.1
  have he : (plan.map Choice.storage)[i.val]'(by rw [List.length_map]; exact i.isLt) =
      (plan.map Choice.storage)[j.val]'(by rw [List.length_map]; exact j.isLt) := by
    simpa only [List.getElem_map, chosen] using hi.trans (hij.trans hj.symm)
  exact hnodup.getElem_inj_iff.mp he

theorem image_injective {A : Type} {plan : Plan} {domains : Domains} (input : Input A plan)
    (ha : allowed domains plan) (hf : feasible plan) (hc : Compiled input domains) :
    Function.Injective (reuseImage (survivors plan) input.proposed input.fresh) := by
  intro i j hij
  exact storage_injective input ha hf hc (congrArg input.storage hij)

theorem retained_payload {A : Type} {plan : Plan} {domains : Domains} (input : Input A plan)
    (ha : allowed domains plan) (hf : feasible plan) (hc : Compiled input domains)
    {i : Fin plan.length} {nd : Node A (Fin plan.length)}
    (hn : input.source.lookup i = some nd) (hs : i ∈ survivors plan) :
    input.before.lookup (reuseImage (survivors plan) input.proposed input.fresh i) =
      some (nd.remap (reuseImage (survivors plan) input.proposed input.fresh) (input.proto i)) := by
  have hr : (chosen plan i).retained = true := by simpa [survivors] using hs
  obtain ⟨hlocal, hedges⟩ := (chosen_facts input ha hc i).2.2 hr nd hn
  rw [show reuseImage (survivors plan) input.proposed input.fresh i = input.proposed i by
    simp [reuseImage, hs], hlocal]
  congr 1
  apply Node.remap_congr
  intro child hm
  have hrequired := hf.2 (chosen plan i) (chosen_mem plan i) _ (hedges child hm)
  rw [← chosen_identity input ha hc child]
  simpa [chosen, List.getElem?_eq_getElem child.isLt] using hrequired.symm

/-- Publishing any plan of the ranked stream, as `publishFirst` may, keeps each retained record
and writes each fresh one at the selected image. -/
theorem selected_published {A : Type} {plan : Plan} {domains : Domains} (input : Input A plan)
    (ranked : plan ∈ rankedPlans domains) (hc : Compiled input domains)
    (covers : ∀ i nd, input.source.lookup i = some nd → (i, nd) ∈ input.records)
    (unique : input.records.Pairwise (fun a b => a.1 ≠ b.1)) :
    Published input.source
      (publishFresh (survivors plan) input.proposed input.fresh input.proto input.records
        input.before)
      (reuseImage (survivors plan) input.proposed input.fresh) input.proto := by
  obtain ⟨ha, hf⟩ := (rankedPlans_exact domains plan).mp ranked
  have hinj := image_injective input ha hf hc
  exact publishFresh_published input.source _ input.proposed input.fresh input.proto
    input.records input.before covers (unique.imp fun hne he => hne (hinj he)) hinj
    fun _ _ hn hs => retained_payload input ha hf hc hn hs

/-- The published result reads back as its source at every depth, so it keeps the source's
shared references and cycles (`Published.surface`; `Published.path` lifts each cycle). -/
theorem selected_surface {A : Type} [AtomEq A] {plan : Plan} {domains : Domains}
    (input : Input A plan) (ranked : plan ∈ rankedPlans domains) (hc : Compiled input domains)
    (covers : ∀ i nd, input.source.lookup i = some nd → (i, nd) ∈ input.records)
    (unique : input.records.Pairwise (fun a b => a.1 ≠ b.1)) (hw : HeapWF input.source)
    (v : Value A (Fin plan.length)) (hv : RootWF input.source v) :
    SurfaceEq input.source
      (publishFresh (survivors plan) input.proposed input.fresh input.proto input.records
        input.before)
      v (v.remap (reuseImage (survivors plan) input.proposed input.fresh)) :=
  (selected_published input ranked hc covers unique).surface hw v hv

theorem selected_storage_distinct {A : Type} {plan : Plan} {domains : Domains}
    (input : Input A plan) (ranked : plan ∈ rankedPlans domains) (hc : Compiled input domains) :
    Function.Injective
      (fun i => input.storage (reuseImage (survivors plan) input.proposed input.fresh i)) :=
  have h := (rankedPlans_exact domains plan).mp ranked
  storage_injective input h.1 h.2 hc

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

def checkCompiled {A : Type} [DecidableEq A] {plan : Plan} (input : Input A plan)
    (domains : Domains) : Bool :=
  (List.finRange plan.length).all fun i =>
    ((domains[i.val]?).getD []).all (checkChoiceFacts input i)

end Reconcile.Immutable
