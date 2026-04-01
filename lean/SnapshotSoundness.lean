/-
  Reconcile — snapshot soundness proofs (Iteration 4).

  Proves S1 (surface preservation) from the snapshot specification.
  S2–S4 are proved directly in SnapshotSpec.lean.
-/

import Defs
import WF
import SnapshotSpec

namespace Reconcile

/-! ## Helper: OptionRel lifting -/

private theorem optionRel_lift {α β : Type}
    {R S : α → β → Prop}
    (hRS : ∀ a b, R a b → S a b)
    {o₁ : Option α} {o₂ : Option β}
    (h : OptionRel R o₁ o₂) :
    OptionRel S o₁ o₂ := by
  cases o₁ <;> cases o₂
  · trivial
  · cases h
  · cases h
  · exact hRS _ _ h

/-! ## Node-level surface eq from SnapshotNodeSpec -/

private theorem snapshotNode_to_nodeSurfaceEq {A : Type} [AtomEq A] {ι : Type}
    [DecidableEq ι]
    {src resultHeap : Heap A ι}
    {memo : Finmap (fun _ : ι => ι)}
    {n : Nat}
    (ih : ∀ v rv, SnapshotValueSpec src resultHeap memo v rv →
      SurfaceEqBounded src resultHeap n v rv)
    {nd nd' : Node A ι}
    (hns : SnapshotNodeSpec src resultHeap memo nd nd') :
    SurfaceEqBounded.NodeSurfaceEqBounded src resultHeap n nd nd' := by
  cases hns with
  | plainObject _hnd1 _hnd2 hkeys hfields =>
    simp only [SurfaceEqBounded.NodeSurfaceEqBounded]
    exact ⟨hkeys, fun k v₁ v₂ h₁ h₂ => ih _ _ (hfields k v₁ v₂ h₁ h₂)⟩
  | array hlen hentries =>
    simp only [SurfaceEqBounded.NodeSurfaceEqBounded]
    exact ⟨hlen, fun i hi₁ hi₂ =>
      optionRel_lift (fun a b h => ih a b h) (hentries i hi₁ hi₂)⟩
  | date =>
    simp only [SurfaceEqBounded.NodeSurfaceEqBounded]
  | map hlen hentries =>
    simp only [SurfaceEqBounded.NodeSurfaceEqBounded]
    exact ⟨hlen, fun i hi₁ hi₂ =>
      let ⟨hk, hv⟩ := hentries i hi₁ hi₂
      ⟨ih _ _ hk, ih _ _ hv⟩⟩
  | set hlen hvalues =>
    simp only [SurfaceEqBounded.NodeSurfaceEqBounded]
    exact ⟨hlen, fun i hi₁ hi₂ => ih _ _ (hvalues i hi₁ hi₂)⟩
  | arrayBuffer =>
    simp only [SurfaceEqBounded.NodeSurfaceEqBounded]
  | dataView hbuf =>
    simp only [SurfaceEqBounded.NodeSurfaceEqBounded]
    exact ⟨trivial, trivial, ih _ _ hbuf⟩
  | typedArray hbuf hlen helems =>
    simp only [SurfaceEqBounded.NodeSurfaceEqBounded]
    exact ⟨trivial, trivial, trivial, ih _ _ hbuf, hlen, fun i hi₁ hi₂ => ih _ _ (helems i hi₁ hi₂)⟩

/-! ## Core lemma: SnapshotValueSpec implies SurfaceEqBounded at all depths -/

theorem snapshotValue_surfaceEq_bounded {A : Type} [AtomEq A] {ι : Type}
    [DecidableEq ι]
    (src resultHeap : Heap A ι)
    (memo : Finmap (fun _ : ι => ι))
    (hms : SnapshotMemoSpec src resultHeap memo) :
    ∀ n v rv, SnapshotValueSpec src resultHeap memo v rv →
      SurfaceEqBounded src resultHeap n v rv := by
  intro n
  induction n with
  | zero =>
    intro v rv hvs
    cases hvs with
    | atom a =>
      unfold SurfaceEqBounded
      exact AtomEq.eq_refl a
    | memoHit _ => unfold SurfaceEqBounded; trivial
  | succ n ih =>
    intro v rv hvs
    cases hvs with
    | atom a =>
      unfold SurfaceEqBounded
      exact AtomEq.eq_refl a
    | memoHit hmem =>
      -- Need to show SurfaceEqBounded src resultHeap (n+1) (.ref r) (.ref r')
      simp only [SurfaceEqBounded]
      -- Get source node
      obtain ⟨nd, hnd⟩ := hms.memoDom _ _ hmem
      -- Get result node and SnapshotNodeSpec
      obtain ⟨nd', hnd', hns⟩ := hms.nodeSpec _ _ hmem nd hnd
      rw [hnd, hnd']
      exact snapshotNode_to_nodeSurfaceEq ih hns

/-! ## Main S1 theorem -/

/-- S1 — Surface preservation: snapshot result is surface-equivalent to source. -/
theorem snapshot_surface_preservation' {A : Type} [AtomEq A] {ι : Type}
    [DecidableEq ι]
    {src : Heap A ι} {root : Value A ι}
    {resultHeap : Heap A ι} {resultRoot : Value A ι}
    (spec : SnapshotSpec src root resultHeap resultRoot)
    (_hwf : HeapWF src)
    (_hrwf : RootWF src root) :
    SurfaceEq src resultHeap root resultRoot := by
  obtain ⟨memo, hroot, hms⟩ := spec
  intro n
  exact snapshotValue_surfaceEq_bounded src resultHeap memo hms n root resultRoot hroot

/-! ## S5 — Cycle preservation -/

/-- Key lemma: SnapshotValueSpec maps refs through memo. -/
private theorem snapshotValueSpec_ref_memo {A : Type} {ι : Type} [DecidableEq ι]
    {src resultHeap : Heap A ι}
    {memo : Finmap (fun _ : ι => ι)}
    {v rv : Value A ι}
    (hvs : SnapshotValueSpec src resultHeap memo v rv) :
    ∀ s, v = .ref s → ∃ s', memo.lookup s = some s' ∧ rv = .ref s' := by
  intro s hs
  subst hs
  cases hvs with
  | memoHit hmem => exact ⟨_, hmem, rfl⟩

/-- Helper: if SnapshotValueSpec maps .ref b to rv, then b is memo’d
    and rv = .ref b’. -/
private theorem svs_ref {A : Type} {ι : Type} [DecidableEq ι]
    {src resultHeap : Heap A ι} {memo : Finmap (fun _ : ι => ι)}
    {b : ι} {rv : Value A ι}
    (hvs : SnapshotValueSpec src resultHeap memo (Value.ref b) rv) :
    ∃ b', memo.lookup b = some b' ∧ rv = Value.ref b' := by
  cases hvs with | memoHit hmem => exact ⟨_, hmem, rfl⟩

/-- Helper: given `b ∈ filterMap refExtract vs₁` and pointwise snapshot
    specs linking `vs₁[i]` to `vs₂[i]`, produce `b'` with `memo b = b'`
    and `b' ∈ filterMap refExtract vs₂`. Covers set and typedArray. -/
private theorem lift_filterMap_values {A : Type} {ι : Type} [DecidableEq ι]
    {src resultHeap : Heap A ι} {memo : Finmap (fun _ : ι => ι)}
    {vs₁ vs₂ : List (Value A ι)}
    (hlen : vs₁.length = vs₂.length)
    (hspec : ∀ i (h₁ : i < vs₁.length) (h₂ : i < vs₂.length),
        SnapshotValueSpec src resultHeap memo vs₁[i] vs₂[i])
    {b : ι}
    (hb : b ∈ vs₁.filterMap (fun x => match x with | .ref r => some r | .atom _ => none)) :
    ∃ b', memo.lookup b = some b' ∧
      b' ∈ vs₂.filterMap (fun x => match x with | .ref r => some r | .atom _ => none) := by
  rw [List.mem_filterMap] at hb
  obtain ⟨v, hmem, hfm⟩ := hb
  cases v with
  | atom => simp at hfm
  | ref r =>
    have hrb : r = b := by simpa using hfm
    rw [hrb] at hmem
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
    have hi2 : i < vs₂.length := hlen ▸ hi
    have hvs := hspec i hi hi2; rw [hget] at hvs
    obtain ⟨b', hm, hr⟩ := svs_ref hvs
    exact ⟨b', hm, List.mem_filterMap.mpr
      ⟨Value.ref b', by rw [← hr]; exact List.getElem_mem hi2, rfl⟩⟩

/-- Per-kind lemma: child refs in a snapshotted node lift through memo. -/
private theorem snapshot_nodeSpec_childRef_lift {A : Type} {ι : Type} [DecidableEq ι]
    {src resultHeap : Heap A ι}
    {memo : Finmap (fun _ : ι => ι)}
    {nd nd' : Node A ι}
    (hns : SnapshotNodeSpec src resultHeap memo nd nd')
    {b : ι} (hb : b ∈ nd.childRefs) :
    ∃ b', memo.lookup b = some b' ∧ b' ∈ nd'.childRefs := by
  cases hns with
  | date => simp [Node.childRefs] at hb
  | arrayBuffer => simp [Node.childRefs] at hb
  | dataView hbuf =>
    simp only [Node.childRefs, List.mem_singleton] at hb; subst hb
    obtain ⟨b', hm, hr⟩ := svs_ref hbuf
    exact ⟨b', hm, by simp [Node.childRefs, Value.ref.inj hr.symm]⟩
  | plainObject hnd1 _hnd2 hkeys hfields =>
    have hb' := List.mem_filterMap.mp hb
    obtain ⟨⟨k, v⟩, hmem_f1, hfm⟩ := hb'
    cases v with
    | atom => simp at hfm
    | ref r =>
      have hrb : r = b := by simpa using hfm
      rw [hrb] at hmem_f1
      have hdl1 := Option.mem_def.mp ((List.mem_dlookup_iff hnd1).mpr hmem_f1)
      have hk := List.mem_keys_of_mem hmem_f1; rw [hkeys] at hk
      obtain ⟨v₂, hv₂⟩ := Option.isSome_iff_exists.mp (List.dlookup_isSome.mpr hk)
      obtain ⟨b', hm, hr⟩ := svs_ref (hfields k (Value.ref b) v₂ hdl1 hv₂)
      refine ⟨b', hm, List.mem_filterMap.mpr ?_⟩
      rename_i f₂
      have hmem_f2 : (⟨k, v₂⟩ : (_ : PropertyKey) × Value A ι) ∈ f₂ :=
        List.of_mem_dlookup (Option.mem_def.mpr hv₂)
      rw [hr] at hmem_f2
      exact ⟨⟨k, Value.ref b'⟩, hmem_f2, rfl⟩
  | array hlen hentries =>
    have hb' := List.mem_filterMap.mp hb
    obtain ⟨entry, hmem, hfm⟩ := hb'
    cases entry with
    | none => simp at hfm
    | some v =>
      cases v with
      | atom => simp at hfm
      | ref r =>
        have hrb : r = b := by simpa using hfm
        rw [hrb] at hmem
        obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
        rename_i es₁ es₂
        have hi2 : i < es₂.length := hlen ▸ hi
        have hor := hentries i hi hi2; rw [hget] at hor
        cases h2 : es₂[i] with
        | none => rw [h2] at hor; exact absurd hor id
        | some v2 =>
          rw [h2] at hor
          obtain ⟨b', hm, hr⟩ := svs_ref hor
          refine ⟨b', hm, List.mem_filterMap.mpr ?_⟩
          rw [hr] at h2
          exact ⟨some (Value.ref b'), by rw [← h2]; exact List.getElem_mem hi2, rfl⟩
  | set hlen hentries =>
    exact lift_filterMap_values hlen hentries hb
  | map hlen hentries =>
    have hb' := List.mem_flatMap.mp hb
    obtain ⟨⟨kv, vv⟩, hmem, hb_in⟩ := hb'
    simp only [List.mem_append] at hb_in
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
    rename_i es₁ es₂
    have hi2 : i < es₂.length := hlen ▸ hi
    have ⟨hvsk, hvsv⟩ := hentries i hi hi2
    have hk_eq : (es₁[i]).1 = kv := by rw [hget]
    have hv_eq : (es₁[i]).2 = vv := by rw [hget]
    rcases hb_in with hb_k | hb_v
    · cases kv with
      | atom a =>
        have hb_k' := hb_k
        simp at hb_k'
      | ref r =>
        have hrb : b = r := by simpa using hb_k
        rw [hk_eq, ← hrb] at hvsk
        obtain ⟨b', hm, hr⟩ := svs_ref hvsk
        refine ⟨b', hm, List.mem_flatMap.mpr ?_⟩
        refine ⟨es₂[i], List.getElem_mem hi2, ?_⟩
        simp only [List.mem_append, List.get_eq_getElem]; left
        rw [hr]; simp
    · cases vv with
      | atom a =>
        have hb_v' := hb_v
        simp at hb_v'
      | ref r =>
        have hrb : b = r := by simpa using hb_v
        rw [hv_eq, ← hrb] at hvsv
        obtain ⟨b', hm, hr⟩ := svs_ref hvsv
        refine ⟨b', hm, List.mem_flatMap.mpr ?_⟩
        refine ⟨es₂[i], List.getElem_mem hi2, ?_⟩
        simp only [List.mem_append, List.get_eq_getElem]; right
        rw [hr]; simp
  | typedArray hbuf hlen helems =>
    simp only [Node.childRefs, List.mem_cons] at hb
    rcases hb with rfl | hb_el
    · obtain ⟨b', hm, hr⟩ := svs_ref hbuf
      refine ⟨b', hm, ?_⟩
      simp only [Node.childRefs, List.mem_cons]
      left; exact Value.ref.inj hr.symm
    · obtain ⟨b', hm, hmem⟩ := lift_filterMap_values hlen helems hb_el
      exact ⟨b', hm, by simp only [Node.childRefs, List.mem_cons]; right; exact hmem⟩

/-- Edge-lifting: a source edge through a memo’d node lifts to a result edge. -/
private theorem snapshot_edge_lift {A : Type} {ι : Type} [DecidableEq ι]
    {src resultHeap : Heap A ι}
    {memo : Finmap (fun _ : ι => ι)}
    (hms : SnapshotMemoSpec src resultHeap memo)
    {a a' b : ι}
    (ha : memo.lookup a = some a')
    (he : edge src a b) :
    ∃ b', memo.lookup b = some b' ∧ edge resultHeap a' b' := by
  obtain ⟨nd, hnd, hb⟩ := he
  obtain ⟨nd', hnd', hns⟩ := hms.nodeSpec a a' ha nd hnd
  obtain ⟨b', hb', hb'mem⟩ := snapshot_nodeSpec_childRef_lift hns hb
  exact ⟨b', hb', ⟨nd', hnd', hb'mem⟩⟩

/-- General TransGen lifting through memo: if `a →⁺ b` in source and
    `a` is memo'd, then `b` is memo'd and `memo(a) →⁺ memo(b)` in result. -/
private theorem snapshot_transGen_lift {A : Type} {ι : Type} [DecidableEq ι]
    {src resultHeap : Heap A ι}
    {memo : Finmap (fun _ : ι => ι)}
    (hms : SnapshotMemoSpec src resultHeap memo)
    {a b : ι}
    (htg : Relation.TransGen (edge src) a b)
    {a' : ι} (ha : memo.lookup a = some a') :
    ∃ b', memo.lookup b = some b' ∧
      Relation.TransGen (edge resultHeap) a' b' := by
  induction htg with
  | single he =>
    obtain ⟨b', hb', hedge'⟩ := snapshot_edge_lift hms ha he
    exact ⟨b', hb', Relation.TransGen.single hedge'⟩
  | @tail c d _ hcd ih =>
    obtain ⟨c', hc', htg'⟩ := ih
    obtain ⟨d', hd', hedge'⟩ := snapshot_edge_lift hms hc' hcd
    exact ⟨d', hd', Relation.TransGen.tail htg' hedge'⟩

/-- S5 — Cycle preservation: if a source ref is reachable from itself
    (i.e., lies on a cycle), then its memo image is also reachable from
    itself in the result heap. -/
theorem snapshot_cycle_preservation {A : Type} {ι : Type} [DecidableEq ι]
    {src resultHeap : Heap A ι}
    {memo : Finmap (fun _ : ι => ι)}
    (hms : SnapshotMemoSpec src resultHeap memo)
    {r r' : ι}
    (hmem : memo.lookup r = some r')
    (hcycle : Relation.TransGen (edge src) r r) :
    Relation.TransGen (edge resultHeap) r' r' := by
  obtain ⟨r'', hr'', htg'⟩ := snapshot_transGen_lift hms hcycle hmem
  have heq : r'' = r' := Option.some.inj (hr'' ▸ hmem)
  subst heq
  exact htg'

/-! ## Snapshot buffer/view alias preservation -/

/-- Buffer/view alias preservation: if two source views share the same
    source buffer ref, their snapshot images share the same result buffer
    ref.

    This follows from the memo being functional: both views' buffer refs
    are the same source ref `b`, so `memo(b)` is the single result buffer
    ref used by both result views. -/
theorem snapshot_buffer_alias {A : Type} {ι : Type} [DecidableEq ι]
    {src resultHeap : Heap A ι}
    {memo : Finmap (fun _ : ι => ι)}
    (_hms : SnapshotMemoSpec src resultHeap memo)
    {b b₁' b₂' : ι}
    (h₁ : memo.lookup b = some b₁')
    (h₂ : memo.lookup b = some b₂') :
    b₁' = b₂' := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

end Reconcile
