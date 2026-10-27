import Heap.WF

/-! Captured-graph publication core, without JavaScript execution semantics. A selected image
is installed before any edge is populated. `Published` is the local readback obligation for one
image; `Published.surface` lifts it to equality with the source at every depth, and
`Published.edge_lift` and `Published.path` carry every edge and cycle to the result. -/

namespace Reconcile

variable {A I J : Type}

/-- Project every occurrence of a reference through the selected image. -/
def Value.remap (image : I → J) : Value A I → Value A J
  | .atom a => .atom a
  | .ref i => .ref (image i)

/-- Preserve field order and absence while mapping present values. -/
def remapFields (image : I → J) (fields : ObjFields A I) : ObjFields A J :=
  fields.map fun ⟨k, v⟩ => ⟨k, v.remap image⟩

/-- Payload publication. Only retained plain-object prototypes may be overridden. -/
def Node.remap (image : I → J) (proto : ProtoLabel → ProtoLabel) : Node A I → Node A J
  | .plainObject p fs => .plainObject (proto p) (remapFields image fs)
  | .array es => .array (es.map (Option.map (Value.remap image)))
  | .date ms => .date ms
  | .map es => .map (es.map fun (k, v) => (k.remap image, v.remap image))
  | .set vs => .set (vs.map (Value.remap image))
  | .arrayBuffer bs => .arrayBuffer bs
  | .dataView b o l => .dataView (image b) o l
  | .typedArray t b o l es => .typedArray t (image b) o l (es.map (Value.remap image))

@[simp] theorem remapFields_keys (image : I → J) (fs : ObjFields A I) :
    (remapFields image fs).keys = fs.keys := by
  induction fs with
  | nil => rfl
  | cons kv fs ih => cases kv; simp_all [remapFields, List.keys]

@[simp] theorem remapFields_lookup (image : I → J) (fs : ObjFields A I) (k : PropertyKey) :
    List.dlookup k (remapFields image fs) = (List.dlookup k fs).map (Value.remap image) := by
  induction fs with
  | nil => rfl
  | cons kv fs ih =>
    rcases kv with ⟨key, v⟩
    by_cases h : k = key
    · subst key; simp [remapFields]
    · simp_all [remapFields]

@[simp] theorem Node.remap_childRefs (image : I → J) (proto) (nd : Node A I) :
    (nd.remap image proto).childRefs = nd.childRefs.map image := by
  cases nd with
  | plainObject p fs =>
    induction fs with
    | nil => rfl
    | cons kv fs ih => cases kv with | mk k v => cases v <;> simp_all [remap, remapFields, childRefs, Value.remap]
  | array es =>
    induction es with
    | nil => rfl
    | cons e es ih => cases e with
      | none => simp_all [remap, childRefs]
      | some v => cases v <;> simp_all [remap, childRefs, Value.remap]
  | map es =>
    induction es with
    | nil => rfl
    | cons e es ih => rcases e with ⟨k, v⟩; cases k <;> cases v <;> simp_all [remap, childRefs, Value.remap]
  | set vs =>
    induction vs with
    | nil => rfl
    | cons v vs ih => cases v <;> simp_all [remap, childRefs, Value.remap]
  | typedArray t b o l es =>
    suffices h : (es.map (Value.remap image)).filterMap (fun v => match v with | .ref r => some r | .atom _ => none) =
        (es.filterMap (fun v => match v with | .ref r => some r | .atom _ => none)).map image by
      simpa [remap, childRefs] using h
    induction es with
    | nil => rfl
    | cons v es ih => cases v <;> simp_all [Value.remap]
  | date => rfl
  | arrayBuffer => rfl
  | dataView => rfl

/-- Every value slot of a node: field values, present array entries, map keys and values, set
members, a view's buffer and a typed array's buffer and elements. -/
def Node.values : Node A I → List (Value A I)
  | .plainObject _ fs => fs.map (·.2)
  | .array es => es.filterMap id
  | .date _ => []
  | .map es => es.flatMap fun e => [e.1, e.2]
  | .set vs => vs
  | .arrayBuffer _ => []
  | .dataView b _ _ => [.ref b]
  | .typedArray _ b _ _ es => .ref b :: es

/-- A node's child references are the references among its values. -/
theorem Node.mem_childRefs {nd : Node A I} {r : I} :
    r ∈ nd.childRefs ↔ Value.ref r ∈ nd.values := by
  cases nd with
  | plainObject p fs =>
    simp only [Node.childRefs, Node.values, List.mem_filterMap, List.mem_map]
    constructor
    · rintro ⟨⟨k, v⟩, hm, hv⟩
      cases v with
      | atom => simp at hv
      | ref x => simp only [Option.some.injEq] at hv; subst hv; exact ⟨⟨k, .ref x⟩, hm, rfl⟩
    · rintro ⟨⟨k, v⟩, hm, rfl⟩; exact ⟨⟨k, .ref r⟩, hm, rfl⟩
  | array es =>
    simp only [Node.childRefs, Node.values, List.mem_filterMap, id]
    constructor
    · rintro ⟨e, hm, he⟩; rcases e with _ | (_ | _) <;> simp_all
    · rintro ⟨e, hm, rfl⟩; exact ⟨some (.ref r), hm, rfl⟩
  | map es =>
    simp only [Node.childRefs, Node.values, List.mem_flatMap]
    refine exists_congr fun ⟨k, v⟩ => and_congr_right fun _ => ?_
    cases k <;> cases v <;> simp
  | set vs =>
    simp only [Node.childRefs, Node.values, List.mem_filterMap]
    constructor
    · rintro ⟨v, hm, hv⟩; cases v <;> simp_all
    · intro hm; exact ⟨.ref r, hm, rfl⟩
  | typedArray t b o l es =>
    simp only [Node.childRefs, Node.values, List.mem_cons, List.mem_filterMap, Value.ref.injEq]
    constructor
    · rintro (h | ⟨v, hm, hv⟩)
      · exact Or.inl h
      · cases v <;> simp_all
    · rintro (h | hm)
      · exact Or.inl h
      · exact Or.inr ⟨.ref r, hm, rfl⟩
  | date => simp [Node.childRefs, Node.values]
  | arrayBuffer => simp [Node.childRefs, Node.values]
  | dataView => simp [Node.childRefs, Node.values]

/-- Payloads depend only on the image of their direct child references. -/
theorem Node.remap_congr (nd : Node A I) (f g : I → J) (proto)
    (h : ∀ r ∈ nd.childRefs, f r = g r) : nd.remap f proto = nd.remap g proto := by
  have hv : ∀ v ∈ nd.values, v.remap f = v.remap g := by
    rintro (_ | r) hm
    · rfl
    · simp [Value.remap, h r (Node.mem_childRefs.mpr hm)]
  cases nd with
  | plainObject p fs =>
    simp only [Node.remap, remapFields]
    congr 1
    apply List.map_congr_left
    rintro ⟨k, v⟩ hk
    simp [hv v (List.mem_map.mpr ⟨⟨k, v⟩, hk, rfl⟩)]
  | array es =>
    simp only [Node.remap]
    congr 1
    apply List.map_congr_left
    rintro (_ | v) he
    · rfl
    · simp [hv v (List.mem_filterMap.mpr ⟨some v, he, rfl⟩)]
  | map es =>
    simp only [Node.remap]
    congr 1
    apply List.map_congr_left
    intro e he
    have hm (v) (hv : v = e.1 ∨ v = e.2) : v ∈ (Node.map es).values :=
      List.mem_flatMap.mpr ⟨e, he, by rcases hv with rfl | rfl <;> simp⟩
    exact Prod.ext (hv _ (hm _ (Or.inl rfl))) (hv _ (hm _ (Or.inr rfl)))
  | set vs =>
    simp only [Node.remap]
    congr 1
    exact List.map_congr_left hv
  | dataView b o l =>
    have hb := hv (.ref b) (by simp [Node.values])
    simp only [Value.remap, Value.ref.injEq] at hb
    simp only [Node.remap, hb]
  | typedArray t b o l es =>
    have hb := hv (.ref b) (by simp [Node.values])
    simp only [Value.remap, Value.ref.injEq] at hb
    simp only [Node.remap, hb]
    congr 1
    exact List.map_congr_left fun v hm => hv v (List.mem_cons_of_mem _ hm)
  | date => rfl
  | arrayBuffer => rfl

/-- A local readback obligation for one fixed image. No global conclusion is assumed. -/
def Published [DecidableEq I] [DecidableEq J]
    (source : Heap A I) (result : Heap A J) (image : I → J)
    (proto : I → ProtoLabel → ProtoLabel) : Prop :=
  ∀ i nd, source.lookup i = some nd →
    result.lookup (image i) = some (nd.remap image (proto i))

/-- Coherent local payloads lift every edge, including buffer dependencies. -/
theorem Published.edge_lift [DecidableEq I] [DecidableEq J]
    {source : Heap A I} {result : Heap A J} {image : I → J} {proto}
    (h : Published source result image proto) {a b : I}
    (he : edge source a b) : edge result (image a) (image b) := by
  obtain ⟨nd, hn, hb⟩ := he
  exact ⟨nd.remap image (proto a), h a nd hn, by simpa using List.mem_map.mpr ⟨b, hb, rfl⟩⟩

/-- Nonempty cycles are derived by lifting their edges. -/
theorem Published.path [DecidableEq I] [DecidableEq J]
    {source : Heap A I} {result : Heap A J} {image : I → J} {proto}
    (h : Published source result image proto) {a b : I}
    (hp : Relation.TransGen (edge source) a b) :
    Relation.TransGen (edge result) (image a) (image b) := by
  induction hp with
  | single he => exact .single (h.edge_lift he)
  | tail _ he ih => exact .tail ih (h.edge_lift he)

private theorem remap_node_surface [AtomEq A] [DecidableEq I] [DecidableEq J]
    {source : Heap A I} {result : Heap A J} {image : I → J} {depth : Nat}
    (ih : ∀ v, RootWF source v → SurfaceEqBounded source result depth v (v.remap image))
    (nd : Node A I) (proto) (hw : NodeWF source nd) :
    SurfaceEqBounded.NodeSurfaceEqBounded source result depth nd (nd.remap image proto) := by
  have child : ∀ v ∈ nd.values, SurfaceEqBounded source result depth v (v.remap image) := by
    rintro (_ | r) hm
    · exact ih _ trivial
    · exact ih _ (hw r (Node.mem_childRefs.mpr hm))
  cases nd with
  | plainObject p fs =>
    simp only [Node.remap, SurfaceEqBounded.NodeSurfaceEqBounded, remapFields_keys]
    refine ⟨trivial, ?_⟩
    intro k v rv hv hrv
    rw [remapFields_lookup, hv] at hrv
    cases hrv
    exact child v (List.mem_map.mpr ⟨⟨k, v⟩, List.of_mem_dlookup hv, rfl⟩)
  | array es =>
    simp only [Node.remap, SurfaceEqBounded.NodeSurfaceEqBounded, List.length_map]
    refine ⟨trivial, ?_⟩
    intro i hi hj
    simp only [List.getElem_map]
    cases he : es[i] with
    | none => trivial
    | some v => exact child v (List.mem_filterMap.mpr ⟨some v, he ▸ List.getElem_mem hi, rfl⟩)
  | date => simp [Node.remap, SurfaceEqBounded.NodeSurfaceEqBounded]
  | arrayBuffer => simp [Node.remap, SurfaceEqBounded.NodeSurfaceEqBounded]
  | map es =>
    simp only [Node.remap, SurfaceEqBounded.NodeSurfaceEqBounded, List.length_map]
    refine ⟨trivial, ?_⟩
    intro i hi hj
    simp only [List.getElem_map]
    have hm : ∀ v, (v = es[i].1 ∨ v = es[i].2) → v ∈ (Node.map es).values := fun v hv =>
      List.mem_flatMap.mpr ⟨es[i], List.getElem_mem hi, by rcases hv with rfl | rfl <;> simp⟩
    exact ⟨child _ (hm _ (Or.inl rfl)), child _ (hm _ (Or.inr rfl))⟩
  | set vs =>
    simp only [Node.remap, SurfaceEqBounded.NodeSurfaceEqBounded, List.length_map]
    refine ⟨trivial, ?_⟩
    intro i hi hj
    simp only [List.getElem_map]
    exact child _ (List.getElem_mem hi)
  | dataView b o l =>
    simp only [Node.remap, SurfaceEqBounded.NodeSurfaceEqBounded]
    exact ⟨trivial, trivial, child (.ref b) (by simp [Node.values])⟩
  | typedArray t b o l es =>
    simp only [Node.remap, SurfaceEqBounded.NodeSurfaceEqBounded, List.length_map]
    refine ⟨trivial, trivial, trivial, child (.ref b) (by simp [Node.values]), trivial, ?_⟩
    intro i hi hj
    simp only [List.getElem_map]
    exact child _ (List.mem_cons_of_mem _ (List.getElem_mem hi))

/-- Global observable correctness follows from local payload correspondence. -/
theorem Published.surface [AtomEq A] [DecidableEq I] [DecidableEq J]
    {source : Heap A I} {result : Heap A J} {image : I → J} {proto}
    (h : Published source result image proto) (hw : HeapWF source)
    (v : Value A I) (hv : RootWF source v) :
    SurfaceEq source result v (v.remap image) := by
  intro depth
  induction depth generalizing v with
  | zero => cases v <;> simp [SurfaceEqBounded, Value.remap, AtomEq.eq_refl]
  | succ depth ih =>
    cases v with
    | atom a => simpa [SurfaceEqBounded, Value.remap] using AtomEq.eq_refl a
    | ref r =>
      obtain ⟨nd, hn⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp hv)
      simp only [Value.remap, SurfaceEqBounded, hn, h r nd hn]
      exact remap_node_surface ih nd (proto r) (hw r hv nd hn)

/-- Populate captured records through an already-selected image. `before` is the
    retained heap; all nonselected identities remain unchanged. -/
def publishRecords [DecidableEq J] (image : I → J) (proto : I → ProtoLabel → ProtoLabel)
    (records : List (I × Node A I)) (before : Heap A J) : Heap A J :=
  match records with
  | [] => before
  | (i, nd) :: rest =>
    (publishRecords image proto rest before).insert (image i) (nd.remap image (proto i))

/-- Unique selected identities prevent a later payload from overwriting another. -/
theorem publishRecords_lookup [DecidableEq J] (image : I → J) (proto)
    (records : List (I × Node A I)) (before : Heap A J)
    (unique : records.Pairwise (fun a b => image a.1 ≠ image b.1))
    {i : I} {nd : Node A I} (hm : (i, nd) ∈ records) :
    (publishRecords image proto records before).lookup (image i) =
      some (nd.remap image (proto i)) := by
  induction records with
  | nil => cases hm
  | cons entry rest ih =>
    rcases entry with ⟨j, node⟩
    rcases List.pairwise_cons.mp unique with ⟨hne, ht⟩
    rcases List.mem_cons.mp hm with he | hm
    · cases he; simp [publishRecords]
    · simp only [publishRecords]
      rw [Finmap.lookup_insert_of_ne _ (Ne.symm (hne _ hm))]
      exact ih ht hm

/-- The pure publisher establishes the local obligations from captured records. -/
theorem publishRecords_published [DecidableEq I] [DecidableEq J]
    (source : Heap A I) (image : I → J) (proto)
    (records : List (I × Node A I)) (before : Heap A J)
    (covers : ∀ i nd, source.lookup i = some nd → (i, nd) ∈ records)
    (unique : records.Pairwise (fun a b => image a.1 ≠ image b.1)) :
    Published source (publishRecords image proto records before) image proto := by
  intro i nd hn
  exact publishRecords_lookup image proto records before unique (covers i nd hn)

/-- A frame property concerns identities, not paths that may alias a selected node. -/
theorem publishRecords_frame [DecidableEq J] (image : I → J) (proto)
    (records : List (I × Node A I)) (before : Heap A J) (r : J)
    (outside : ∀ entry ∈ records, image entry.1 ≠ r) :
    (publishRecords image proto records before).lookup r = before.lookup r := by
  induction records with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨i, nd⟩
    simp only [publishRecords]
    rw [Finmap.lookup_insert_of_ne _ (Ne.symm (outside (i, nd) (by simp)))]
    exact ih (fun entry hm => outside entry (by simp [hm]))

/-- Finite stable readback check; the image is fixed throughout this observation. -/
def checkPublication [DecidableEq A] [DecidableEq J] (image : I → J) (proto : I → ProtoLabel → ProtoLabel)
    (records : List (I × Node A I)) (observed : Heap A J) : Bool :=
  records.all fun (i, nd) => decide (observed.lookup (image i) = some (nd.remap image (proto i)))

/-- Successful local readback establishes the same obligations as pure publication. -/
theorem checkPublication_sound [DecidableEq A] [DecidableEq I] [DecidableEq J]
    (source : Heap A I) (image : I → J) (proto : I → ProtoLabel → ProtoLabel)
    (records : List (I × Node A I)) (observed : Heap A J)
    (covers : ∀ i nd, source.lookup i = some nd → (i, nd) ∈ records)
    (accepted : checkPublication image proto records observed = true) :
    Published source observed image proto := by
  intro i nd hn
  have h := List.all_eq_true.mp accepted (i, nd) (covers i nd hn)
  exact of_decide_eq_true h

end Reconcile
