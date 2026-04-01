/-
  Reconcile — executable reference algorithm (Iteration 7).

  Defines executable snapshot and reconcile algorithms with explicit
  state threading. These are reference implementations close to the
  TypeScript runtime, designed for refinement proofs.

  Strategy:
    - Named state records with transparent fields
    - Fuel (Nat) parameter to sidestep termination on cyclic graphs
    - List-based data structures (proof-friendly)
    - Explicit state passing, no monads
    - Non-mutual structure: execSnapshotNode is inlined via
      a single recursive function over a sum type to avoid
      mutual termination difficulties.
-/

import Defs
import WF

namespace Reconcile

/-! ## Association list lookup -/

/-- Lookup in a list-based association map. -/
def assocLookup {α β : Type} [DecidableEq α] (m : List (α × β)) (k : α) : Option β :=
  match m with
  | [] => none
  | (k', v) :: rest => if k' == k then some v else assocLookup rest k

/-! ## Executable snapshot -/

/-- State for the executable snapshot algorithm. -/
structure ExecSnapshotState (A : Type) (ι : Type) where
  memo : List (ι × ι)
  result : List (ι × Node A ι)
  nextFresh : Nat

/-- Work items for the snapshot worklist. Each item is either a single
    value to snapshot, or a list of sigma entries, option values, values,
    or pairs to process. The worklist avoids mutual recursion. -/
inductive SnapWork (A : Type) (ι : Type) where
  | val : Value A ι → SnapWork A ι
  | sigmaList : List (Sigma (fun _ : PropertyKey => Value A ι)) → SnapWork A ι
  | valList : List (Value A ι) → SnapWork A ι
  | optList : List (Option (Value A ι)) → SnapWork A ι
  | pairList : List (Value A ι × Value A ι) → SnapWork A ι

/-- Result of processing a SnapWork item. -/
inductive SnapResult (A : Type) (ι : Type) where
  | val : Value A ι → SnapResult A ι
  | sigmaList : List (Sigma (fun _ : PropertyKey => Value A ι)) → SnapResult A ι
  | valList : List (Value A ι) → SnapResult A ι
  | optList : List (Option (Value A ι)) → SnapResult A ι
  | pairList : List (Value A ι × Value A ι) → SnapResult A ι

-- Actually, the worklist approach is over-engineering this. Let me use
-- a simpler strategy: make ALL child processing go through a single
-- function by converting node children to a flat value list and back.

-- Simplest approach: non-recursive node snapshot (children already processed).

/-- Process all child values in a node, returning the node with
    snapshotted children. Takes a value-snapshot function as parameter
    to avoid mutual recursion. -/
def snapshotNodeChildren {A : Type} {ι : Type}
    (snapVal : Value A ι → ExecSnapshotState A ι →
      Value A ι × ExecSnapshotState A ι)
    (st : ExecSnapshotState A ι)
    (nd : Node A ι) : Node A ι × ExecSnapshotState A ι :=
  match nd with
  | .plainObject proto fields =>
    let (fields', st') := snapSigmaList snapVal st fields
    (.plainObject proto fields', st')
  | .array entries =>
    let (entries', st') := snapOptList snapVal st entries
    (.array entries', st')
  | .date ms => (.date ms, st)
  | .map entries =>
    let (entries', st') := snapPairList snapVal st entries
    (.map entries', st')
  | .set values =>
    let (values', st') := snapValList snapVal st values
    (.set values', st')
  | .arrayBuffer bytes => (.arrayBuffer bytes, st)
  | .dataView bufRef off len =>
    let (bufVal, st') := snapVal (.ref bufRef) st
    match bufVal with
    | .ref r' => (.dataView r' off len, st')
    | _ => (.dataView bufRef off len, st')
  | .typedArray tag bufRef off len elems =>
    let (bufVal, st') := snapVal (.ref bufRef) st
    let (elems', st'') := snapValList snapVal st' elems
    match bufVal with
    | .ref r' => (.typedArray tag r' off len elems', st'')
    | _ => (.typedArray tag bufRef off len elems', st'')
where
  snapSigmaList {A : Type} {ι : Type}
      (snapVal : Value A ι → ExecSnapshotState A ι →
        Value A ι × ExecSnapshotState A ι)
      (st : ExecSnapshotState A ι) :
      List (Sigma (fun _ : PropertyKey => Value A ι)) →
        List (Sigma (fun _ : PropertyKey => Value A ι)) × ExecSnapshotState A ι
    | [] => ([], st)
    | ⟨k, v⟩ :: rest =>
      let (v', st') := snapVal v st
      let (rest', st'') := snapSigmaList snapVal st' rest
      (⟨k, v'⟩ :: rest', st'')
  snapValList {A : Type} {ι : Type}
      (snapVal : Value A ι → ExecSnapshotState A ι →
        Value A ι × ExecSnapshotState A ι)
      (st : ExecSnapshotState A ι) :
      List (Value A ι) → List (Value A ι) × ExecSnapshotState A ι
    | [] => ([], st)
    | v :: vs =>
      let (v', st') := snapVal v st
      let (vs', st'') := snapValList snapVal st' vs
      (v' :: vs', st'')
  snapOptList {A : Type} {ι : Type}
      (snapVal : Value A ι → ExecSnapshotState A ι →
        Value A ι × ExecSnapshotState A ι)
      (st : ExecSnapshotState A ι) :
      List (Option (Value A ι)) →
        List (Option (Value A ι)) × ExecSnapshotState A ι
    | [] => ([], st)
    | none :: rest =>
      let (rest', st') := snapOptList snapVal st rest
      (none :: rest', st')
    | some v :: rest =>
      let (v', st') := snapVal v st
      let (rest', st'') := snapOptList snapVal st' rest
      (some v' :: rest', st'')
  snapPairList {A : Type} {ι : Type}
      (snapVal : Value A ι → ExecSnapshotState A ι →
        Value A ι × ExecSnapshotState A ι)
      (st : ExecSnapshotState A ι) :
      List (Value A ι × Value A ι) →
        List (Value A ι × Value A ι) × ExecSnapshotState A ι
    | [] => ([], st)
    | (k, v) :: rest =>
      let (k', st') := snapVal k st
      let (v', st'') := snapVal v st'
      let (rest', st''') := snapPairList snapVal st'' rest
      ((k', v') :: rest', st''')

/-- The main executable snapshot function. Uses fuel for ref-depth bound.
    Node children are processed via snapshotNodeChildren which takes
    a curried self-reference, avoiding mutual recursion. -/
def execSnapshotValue {A : Type} {ι : Type} [DecidableEq ι]
    (mkId : Nat → ι)
    (src : List (ι × Node A ι))
    (fuel : Nat)
    (st : ExecSnapshotState A ι)
    (v : Value A ι) : Value A ι × ExecSnapshotState A ι :=
  match v with
  | .atom a => (.atom a, st)
  | .ref r =>
    match assocLookup st.memo r with
    | some r' => (.ref r', st)
    | none =>
      match fuel with
      | 0 => (.ref r, st)
      | fuel' + 1 =>
        let r' := mkId st.nextFresh
        let st' : ExecSnapshotState A ι := {
          memo := (r, r') :: st.memo
          result := st.result
          nextFresh := st.nextFresh + 1 }
        match assocLookup src r with
        | none => (.ref r', st')
        | some nd =>
          let snapChild := fun v st => execSnapshotValue mkId src fuel' st v
          let (nd', st'') := snapshotNodeChildren snapChild st' nd
          (.ref r', { st'' with result := (r', nd') :: st''.result })

/-- Top-level executable snapshot. -/
def execSnapshot {A : Type} {ι : Type} [DecidableEq ι]
    (mkId : Nat → ι)
    (src : List (ι × Node A ι))
    (fuel : Nat)
    (root : Value A ι) : Value A ι × ExecSnapshotState A ι :=
  execSnapshotValue mkId src fuel
    { memo := [], result := [], nextFresh := 0 } root

/-! ## Executable reconcile -/

/-- State for the executable reconcile algorithm. -/
structure ExecReconcileState (A : Type) where
  reuse : List (CurId × NextId)
  image : List (NextId × ResId)
  nextFresh : Nat

/-- The executable root reconcile rule (§5.2). -/
def execReconcileRoot {A : Type} [DecidableEq A]
    (curHeap : List (CurId × Node A CurId))
    (nextHeap : List (NextId × Node A NextId))
    (current : Value A CurId)
    (next : Value A NextId) : Value A ResId :=
  match current, next with
  | .atom a₁, .atom a₂ =>
    if a₁ == a₂ then .atom a₁ else .atom a₂
  | .atom _, .ref nr => .ref (.inr ⟨nr.val⟩)
  | .ref _, .atom a => .atom a
  | .ref cr, .ref nr =>
    match assocLookup curHeap cr, assocLookup nextHeap nr with
    | some cn, some nn =>
      if cn.kind == nn.kind then .ref (.inl cr)
      else .ref (.inr ⟨nr.val⟩)
    | _, _ => .ref (.inr ⟨nr.val⟩)

/-- The executable recursive reconcile value rule (§5.3). -/
def execReconcileValue {A : Type} [DecidableEq A]
    (curHeap : List (CurId × Node A CurId))
    (nextHeap : List (NextId × Node A NextId))
    (fuel : Nat)
    (st : ExecReconcileState A)
    (current : Value A CurId)
    (next : Value A NextId) : Value A ResId × ExecReconcileState A :=
  match next with
  | .atom a => (.atom a, st)
  | .ref nr =>
    match assocLookup st.image nr with
    | some ri => (.ref ri, st)
    | none =>
      match current with
      | .atom _ =>
        let f := FreshId.mk st.nextFresh
        (.ref (.inr f), { st with nextFresh := st.nextFresh + 1 })
      | .ref cr =>
        match assocLookup st.reuse cr with
        | some _ =>
          let f := FreshId.mk st.nextFresh
          (.ref (.inr f), { st with nextFresh := st.nextFresh + 1 })
        | none =>
          match assocLookup curHeap cr, assocLookup nextHeap nr with
          | some cn, some nn =>
            if cn.kind == nn.kind then
              match fuel with
              | 0 => (.ref (.inl cr), st)
              | _ + 1 =>
                let st' : ExecReconcileState A := {
                  reuse := (cr, nr) :: st.reuse
                  image := (nr, .inl cr) :: st.image
                  nextFresh := st.nextFresh }
                (.ref (.inl cr), st')
            else
              let f := FreshId.mk st.nextFresh
              (.ref (.inr f), { st with nextFresh := st.nextFresh + 1 })
          | _, _ =>
            let f := FreshId.mk st.nextFresh
            (.ref (.inr f), { st with nextFresh := st.nextFresh + 1 })

/-- The shared-object fast path (§5.4). -/
def execSharedObject {A : Type}
    (st : ExecReconcileState A)
    (cr : CurId) (nr : NextId) : ResId × ExecReconcileState A :=
  match assocLookup st.image nr with
  | some ri => (ri, st)
  | none =>
    match assocLookup st.reuse cr with
    | some _ =>
      let f := FreshId.mk st.nextFresh
      (.inr f, { st with nextFresh := st.nextFresh + 1 })
    | none =>
      let st' : ExecReconcileState A := {
        reuse := (cr, nr) :: st.reuse
        image := (nr, .inl cr) :: st.image
        nextFresh := st.nextFresh }
      (.inl cr, st')

/-! ## Kind-specific node reconciliation (§6.1–6.8) -/

/-- Reconcile aligned field lists (plain objects §6.8).
    Iterates next fields in order, reconciling each against the current
    field with the same key (if present). When current lacks a key,
    `freshVal` produces a snapshot-equivalent fresh result. -/
def reconcileFields {A : Type} [DecidableEq A]
    (reconcileEntry : Value A CurId → Value A NextId →
      ExecReconcileState A → Value A ResId × ExecReconcileState A)
    (freshVal : Value A NextId → ExecReconcileState A →
      Value A ResId × ExecReconcileState A)
    (curFields : ObjFields A CurId)
    (nextFields : ObjFields A NextId)
    (st : ExecReconcileState A) :
    ObjFields A ResId × ExecReconcileState A :=
  match nextFields with
  | [] => ([], st)
  | ⟨k, nv⟩ :: rest =>
    let (rv, st') := match List.dlookup k curFields with
      | some cv => reconcileEntry cv nv st
      | none => freshVal nv st
    let (rest', st'') := reconcileFields reconcileEntry freshVal
      curFields rest st'
    (⟨k, rv⟩ :: rest', st'')

/-- Reconcile aligned array entries (§6.1). Index-aligned. -/
def reconcileArrayEntries {A : Type} [DecidableEq A]
    (reconcileEntry : Value A CurId → Value A NextId →
      ExecReconcileState A → Value A ResId × ExecReconcileState A)
    (freshVal : Value A NextId → ExecReconcileState A →
      Value A ResId × ExecReconcileState A)
    (curEntries : List (Option (Value A CurId)))
    (nextEntries : List (Option (Value A NextId)))
    (st : ExecReconcileState A) :
    List (Option (Value A ResId)) × ExecReconcileState A :=
  match nextEntries with
  | [] => ([], st)
  | none :: nrest =>
    let (rest', st') := reconcileArrayEntries reconcileEntry freshVal
      (curEntries.drop 1) nrest st
    (none :: rest', st')
  | some nv :: nrest =>
    let (rv, st') := match curEntries with
      | (some cv) :: _ => reconcileEntry cv nv st
      | _ => freshVal nv st  -- hole or missing current
    let (rest', st'') := reconcileArrayEntries reconcileEntry freshVal
      (curEntries.drop 1) nrest st'
    (some rv :: rest', st'')

/-- Reconcile aligned map entry sequences (§6.3). Ordinal-aligned. -/
def reconcileMapEntries {A : Type} [DecidableEq A]
    (reconcileEntry : Value A CurId → Value A NextId →
      ExecReconcileState A → Value A ResId × ExecReconcileState A)
    (freshVal : Value A NextId → ExecReconcileState A →
      Value A ResId × ExecReconcileState A)
    (curEntries : List (Value A CurId × Value A CurId))
    (nextEntries : List (Value A NextId × Value A NextId))
    (st : ExecReconcileState A) :
    List (Value A ResId × Value A ResId) × ExecReconcileState A :=
  match nextEntries with
  | [] => ([], st)
  | (nk, nv) :: nrest =>
    let (rk, rv, st') := match curEntries with
      | (ck, cv) :: _ =>
        let (rk, st') := reconcileEntry ck nk st
        let (rv, st'') := reconcileEntry cv nv st'
        (rk, rv, st'')
      | [] =>
        let (rk, st') := freshVal nk st
        let (rv, st'') := freshVal nv st'
        (rk, rv, st'')
    let (rest', st'') := reconcileMapEntries reconcileEntry freshVal
      (curEntries.drop 1) nrest st'
    ((rk, rv) :: rest', st'')

/-- Reconcile aligned set value sequences (§6.4). Ordinal-aligned. -/
def reconcileSetValues {A : Type} [DecidableEq A]
    (reconcileEntry : Value A CurId → Value A NextId →
      ExecReconcileState A → Value A ResId × ExecReconcileState A)
    (freshVal : Value A NextId → ExecReconcileState A →
      Value A ResId × ExecReconcileState A)
    (curValues : List (Value A CurId))
    (nextValues : List (Value A NextId))
    (st : ExecReconcileState A) :
    List (Value A ResId) × ExecReconcileState A :=
  match nextValues with
  | [] => ([], st)
  | nv :: nrest =>
    let (rv, st') := match curValues with
      | cv :: _ => reconcileEntry cv nv st
      | [] => freshVal nv st
    let (rest', st'') := reconcileSetValues reconcileEntry freshVal
      (curValues.drop 1) nrest st'
    (rv :: rest', st'')

/-- Reconcile two nodes of the same kind (§6). Returns the result node
    and updated state. Uses reconcileEntry callback for child values. -/
def execReconcileNodeByKind {A : Type} [DecidableEq A]
    (reconcileEntry : Value A CurId → Value A NextId →
      ExecReconcileState A → Value A ResId × ExecReconcileState A)
    (freshVal : Value A NextId → ExecReconcileState A →
      Value A ResId × ExecReconcileState A)
    (st : ExecReconcileState A)
    (cnd : Node A CurId) (nnd : Node A NextId) :
    Node A ResId × ExecReconcileState A :=
  match cnd, nnd with
  -- §6.8 Plain objects
  | .plainObject cProto cFields, .plainObject _ nFields =>
    let (rFields, st') := reconcileFields reconcileEntry freshVal
      cFields nFields st
    (.plainObject cProto rFields, st')
  -- §6.1 Arrays
  | .array cEntries, .array nEntries =>
    let (rEntries, st') := reconcileArrayEntries reconcileEntry freshVal
      cEntries nEntries st
    (.array rEntries, st')
  -- §6.2 Date
  | .date _, .date nMs => (.date nMs, st)
  -- §6.3 Map
  | .map cEntries, .map nEntries =>
    let (rEntries, st') := reconcileMapEntries reconcileEntry freshVal
      cEntries nEntries st
    (.map rEntries, st')
  -- §6.4 Set
  | .set cValues, .set nValues =>
    let (rValues, st') := reconcileSetValues reconcileEntry freshVal
      cValues nValues st
    (.set rValues, st')
  -- §6.5 ArrayBuffer
  | .arrayBuffer _, .arrayBuffer nBytes =>
    (.arrayBuffer nBytes, st)
  -- §6.6 DataView: reconcile backing buffer, check metadata
  | .dataView cBuf cOff cLen, .dataView nBuf nOff nLen =>
    let (rBuf, st') := reconcileEntry (.ref cBuf) (.ref nBuf) st
    let rb := match rBuf with | .ref r => r | _ => .inr ⟨st'.nextFresh⟩
    if cOff == nOff && cLen == nLen then
      (.dataView rb cOff cLen, st')
    else
      (.dataView rb nOff nLen, st')
  -- §6.7 TypedArray: reconcile buffer + elements, check metadata
  | .typedArray cTag cBuf cOff cLen cElems,
    .typedArray nTag nBuf nOff nLen nElems =>
    let (rBuf, st') := reconcileEntry (.ref cBuf) (.ref nBuf) st
    let (rElems, st'') := reconcileSetValues reconcileEntry freshVal
      cElems nElems st'
    let rb := match rBuf with | .ref r => r | _ => .inr ⟨st''.nextFresh⟩
    if cTag == nTag && cOff == nOff && cLen == nLen then
      (.typedArray cTag rb cOff cLen rElems, st'')
    else
      (.typedArray nTag rb nOff nLen rElems, st'')
  -- Kind mismatch (shouldn't reach here; caller checks kind)
  | _, _ => (.date 0, st)

/-- The entry reconcile rule (§5.5). -/
def execReconcileEntry {A : Type} [DecidableEq A]
    (curHeap : List (CurId × Node A CurId))
    (nextHeap : List (NextId × Node A NextId))
    (fuel : Nat)
    (st : ExecReconcileState A)
    (curEntry : Value A CurId)
    (nextEntry : Value A NextId) : Value A ResId × ExecReconcileState A :=
  match curEntry, nextEntry with
  | .atom a₁, .atom a₂ =>
    if a₁ == a₂ then (.atom a₁, st)
    else execReconcileValue curHeap nextHeap fuel st curEntry nextEntry
  | .ref cr, .ref nr =>
    if cr.val == nr.val then
      let (ri, st') := execSharedObject st cr nr
      (.ref ri, st')
    else
      execReconcileValue curHeap nextHeap fuel st curEntry nextEntry
  | _, _ => execReconcileValue curHeap nextHeap fuel st curEntry nextEntry

end Reconcile
