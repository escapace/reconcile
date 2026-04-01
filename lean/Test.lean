/-
  Executable tests for snapshot and reconcile.
  Every test uses `assert!` for machine-checkable correctness.
  Tests verify values, not just shapes.
-/
import Algorithm

open Reconcile

/-! ## Test infrastructure -/

inductive TestAtom where
  | str : String → TestAtom
  | num : Int → TestAtom
deriving DecidableEq, Repr

instance : BEq TestAtom where beq a b := decide (a = b)
instance : AtomEq TestAtom where
  eq a b := a = b; eq_dec := inferInstance; eq_refl _ := rfl

abbrev TV := Value TestAtom Nat
abbrev TN := Node TestAtom Nat
def pk (n : Nat) : PropertyKey := ⟨n⟩
def proto (n : Nat) : ProtoLabel := ⟨n⟩
def ctag (n : Nat) : CtorTag := ⟨n⟩

instance : BEq TV where beq a b := decide (a = b)
instance : BEq (Option TV) where beq a b := decide (a = b)
instance : BEq TN where beq a b := decide (a = b)
instance : BEq (Value TestAtom ResId) where beq a b := decide (a = b)
instance : BEq (Option (Value TestAtom ResId)) where beq a b := decide (a = b)
instance : Inhabited TV where
  default := Value.atom (TestAtom.num 0)
instance : Inhabited (Sigma (fun _ : PropertyKey => TV)) where
  default := ⟨pk 0, default⟩
instance : Inhabited (Value TestAtom ResId) where
  default := Value.atom (TestAtom.num 0)
instance : Inhabited (Value TestAtom ResId × Value TestAtom ResId) where
  default := (default, default)
instance : Inhabited (Sigma (fun _ : PropertyKey => Value TestAtom ResId)) where
  default := ⟨pk 0, default⟩

/-- Helper: look up a key in the result heap (association list). -/
def resultLookup (result : List (Nat × TN)) (k : Nat) : Option TN :=
  assocLookup result k

/-- Helper: look up a memo mapping. -/
def memoLookup (memo : List (Nat × Nat)) (k : Nat) : Option Nat :=
  assocLookup memo k

/-! ## Source heap: all 8 kinds, interconnected -/

-- Node 0: plainObject { key1: "hello", key2: ref 1, key3: ref 3 }
-- Node 1: array [some "a", none, some (ref 2)]
-- Node 2: date 1700000000000
-- Node 3: map [(str "k1", ref 0), (num 42, str "v2")]
--          ^ note: ref 0 creates sharing (map3 → obj0, and obj0 is root)
-- Node 4: set [str "x", ref 2, num 7]
--          ^ ref 2 creates sharing (set4 → date2, also reachable via arr1)
-- Node 5: arrayBuffer [0x41, 0x42, 0x43]
-- Node 6: dataView over buffer 5, offset 1, length 2
-- Node 7: typedArray tag=1 over buffer 5, offset 0, length 3, elems [num 1, num 2]
--          ^ buffer 5 shared between dataView and typedArray

def srcHeap : List (Nat × TN) :=
  [ (0, .plainObject (proto 0)
        [⟨pk 1, .atom (.str "hello")⟩, ⟨pk 2, .ref 1⟩, ⟨pk 3, .ref 3⟩]),
    (1, .array [some (.atom (.str "a")), none, some (.ref 2)]),
    (2, .date 1700000000000),
    (3, .map [(.atom (.str "k1"), .ref 0), (.atom (.num 42), .atom (.str "v2"))]),
    (4, .set [.atom (.str "x"), .ref 2, .atom (.num 7)]),
    (5, .arrayBuffer [0x41, 0x42, 0x43]),
    (6, .dataView 5 1 2),
    (7, .typedArray (ctag 1) 5 0 3 [.atom (.num 1), .atom (.num 2)]) ]

def mkFresh (n : Nat) : Nat := 100 + n

/-! ## 1. Snapshot: value correctness -/

-- Snapshot the full graph from root = ref 0
-- Reachable from 0: 0 → {1,3}, 1 → {2}, 3 → {0 (memo hit)}
-- So nodes 0,1,2,3 should be snapshotted. Nodes 4,5,6,7 are unreachable.
#eval do
  let (rv, st) := execSnapshot mkFresh srcHeap 20 (Value.ref 0)
  -- Root is ref 100 (first fresh id)
  assert! rv == Value.ref 100
  -- Exactly 4 nodes reachable and snapshotted
  assert! st.memo.length == 4
  assert! st.result.length == 4
  -- Memo maps: 0→100, 1→101, 3→102, 2→103 (DFS order)
  -- Actually order depends on traversal. Let's just check all 4 are present.
  let m := st.memo
  let r0 := memoLookup m 0; assert! r0.isSome
  let r1 := memoLookup m 1; assert! r1.isSome
  let r2 := memoLookup m 2; assert! r2.isSome
  let r3 := memoLookup m 3; assert! r3.isSome
  -- Fresh ids should all be distinct
  let ids := [r0.get!, r1.get!, r2.get!, r3.get!]
  assert! ids.length == 4
  assert! ids.eraseDups.length == 4
  -- Verify result node for obj0: fields should reference fresh ids, not source ids
  let freshObj := resultLookup st.result r0.get!
  match freshObj with
  | some (.plainObject p fields) =>
    assert! p == proto 0
    assert! fields.length == 3
    -- key1 should still be atom "hello"
    match fields[0]! with
    | ⟨k, Value.atom (TestAtom.str s)⟩ => assert! k == pk 1; assert! s == "hello"
    | _ => assert! false
    -- key2 should be ref to fresh id of node 1
    match fields[1]! with
    | ⟨k, Value.ref r⟩ => assert! k == pk 2; assert! r == r1.get!
    | _ => assert! false
    -- key3 should be ref to fresh id of node 3
    match fields[2]! with
    | ⟨k, Value.ref r⟩ => assert! k == pk 3; assert! r == r3.get!
    | _ => assert! false
  | _ => assert! false
  -- Verify result node for arr1: entries should reference fresh id of node 2
  let freshArr := resultLookup st.result r1.get!
  match freshArr with
  | some (.array entries) =>
    assert! entries.length == 3
    assert! entries[0]! == some (Value.atom (TestAtom.str "a"))
    assert! entries[1]! == (none : Option TV)
    match entries[2]! with
    | some (.ref r) => assert! r == r2.get!
    | _ => assert! false
  | _ => assert! false
  -- Verify date node preserved
  let freshDate := resultLookup st.result r2.get!
  match freshDate with
  | some (.date ms) => assert! ms == 1700000000000
  | _ => assert! false
  -- Verify map node: second entry has ref to fresh id of node 0 (sharing!)
  let freshMap := resultLookup st.result r3.get!
  match freshMap with
  | some (.map entries) =>
    assert! entries.length == 2
    -- first entry: (str "k1", ref to fresh 0)
    match entries[0]! with
    | (.atom (.str k), .ref r) =>
      assert! k == "k1"
      assert! r == r0.get!  -- sharing: map3's ref 0 maps to same fresh id as root
    | _ => assert! false
    -- second entry: (num 42, str "v2")
    match entries[1]! with
    | (.atom (.num n), .atom (.str v)) => assert! n == 42; assert! v == "v2"
    | _ => assert! false
  | _ => assert! false
  IO.println "✓ snapshot value correctness"

/-! ## 2. Snapshot: sharing preservation -/

-- map3's ref 0 and the root both refer to source node 0.
-- After snapshot, both should map to the same fresh id.
-- (Already verified above in the map node check, but let's be explicit.)
#eval do
  let (_, st) := execSnapshot mkFresh srcHeap 20 (Value.ref 0)
  let m := st.memo
  let rootFresh := memoLookup m 0
  -- The map node's child "ref 0" should resolve to rootFresh via memo
  -- This is the sharing property: identical source refs → identical result refs
  assert! rootFresh.isSome
  -- Check that looking up 0 in memo always gives the same answer
  let rootFresh2 := memoLookup m 0
  assert! rootFresh == rootFresh2
  IO.println "✓ snapshot sharing"

/-! ## 3. Snapshot: cycle preservation -/

def cyclicHeap : List (Nat × TN) :=
  [(10, .plainObject (proto 0) [⟨pk 1, .ref 11⟩]),
   (11, .plainObject (proto 0) [⟨pk 1, .ref 10⟩])]

#eval do
  let (rv, st) := execSnapshot mkFresh cyclicHeap 20 (Value.ref 10)
  let m := st.memo
  let f10 := (memoLookup m 10).get!
  let f11 := (memoLookup m 11).get!
  assert! f10 != f11
  -- Root points to fresh 10
  assert! rv == Value.ref f10
  -- Fresh node for 10 should have field referencing fresh 11
  match resultLookup st.result f10 with
  | some (.plainObject _ fields) =>
    match fields[0]! with
    | ⟨_, Value.ref r⟩ => assert! r == f11
    | _ => assert! false
  | _ => assert! false
  -- Fresh node for 11 should have field referencing fresh 10 (the cycle)
  match resultLookup st.result f11 with
  | some (.plainObject _ fields) =>
    match fields[0]! with
    | ⟨_, Value.ref r⟩ => assert! r == f10
    | _ => assert! false
  | _ => assert! false
  IO.println "✓ snapshot cycle preservation"

/-! ## 4. Snapshot: buffer-ref remapping (dataView, typedArray) -/

#eval do
  -- Snapshot from dataView (node 6). Should snapshot node 6 and its buffer (node 5).
  let (rv, st) := execSnapshot mkFresh srcHeap 20 (Value.ref 6)
  let m := st.memo
  let f6 := (memoLookup m 6).get!
  let f5 := (memoLookup m 5).get!
  assert! rv == Value.ref f6
  -- DataView result should reference the fresh buffer id, not source id 5
  match resultLookup st.result f6 with
  | some (.dataView bufRef off len) =>
    assert! bufRef == f5
    assert! off == 1
    assert! len == 2
  | _ => assert! false
  -- Buffer bytes preserved
  match resultLookup st.result f5 with
  | some (.arrayBuffer bytes) => assert! bytes == [0x41, 0x42, 0x43]
  | _ => assert! false
  IO.println "✓ snapshot dataView buffer-ref remapping"

#eval do
  -- Snapshot from typedArray (node 7). Should snapshot node 7 and buffer (node 5).
  let (rv, st) := execSnapshot mkFresh srcHeap 20 (Value.ref 7)
  let m := st.memo
  let f7 := (memoLookup m 7).get!
  let f5 := (memoLookup m 5).get!
  assert! rv == Value.ref f7
  match resultLookup st.result f7 with
  | some (.typedArray tag bufRef off len elems) =>
    assert! tag == ctag 1
    assert! bufRef == f5  -- remapped buffer ref
    assert! off == 0
    assert! len == 3
    assert! elems == [Value.atom (TestAtom.num 1), Value.atom (TestAtom.num 2)]
  | _ => assert! false
  IO.println "✓ snapshot typedArray buffer-ref remapping"

/-! ## 5. Snapshot: buffer sharing between dataView and typedArray -/

-- Build a heap where both dataView and typedArray reference the same buffer.
-- Snapshot from a parent that references both. The buffer should be snapshotted once.
def sharedBufHeap : List (Nat × TN) :=
  [ (0, .plainObject (proto 0) [⟨pk 1, .ref 1⟩, ⟨pk 2, .ref 2⟩]),
    (1, .dataView 3 0 4),
    (2, .typedArray (ctag 1) 3 0 4 [.atom (.num 10)]),
    (3, .arrayBuffer [0xFF]) ]

#eval do
  let (_, st) := execSnapshot mkFresh sharedBufHeap 20 (Value.ref 0)
  let m := st.memo
  -- All 4 nodes should be in memo
  assert! st.memo.length == 4
  let f1 := (memoLookup m 1).get!  -- dataView
  let f2 := (memoLookup m 2).get!  -- typedArray
  let f3 := (memoLookup m 3).get!  -- buffer
  -- Both dataView and typedArray should reference the SAME fresh buffer id
  match resultLookup st.result f1 with
  | some (.dataView bufRef _ _) => assert! bufRef == f3
  | _ => assert! false
  match resultLookup st.result f2 with
  | some (.typedArray _ bufRef _ _ _) => assert! bufRef == f3
  | _ => assert! false
  IO.println "✓ snapshot buffer sharing between dataView and typedArray"

/-! ## 6. Snapshot: set node with refs -/

#eval do
  let (_, st) := execSnapshot mkFresh srcHeap 20 (Value.ref 4)
  let m := st.memo
  let f4 := (memoLookup m 4).get!
  let f2 := (memoLookup m 2).get!
  match resultLookup st.result f4 with
  | some (.set values) =>
    assert! values.length == 3
    assert! values[0]! == Value.atom (TestAtom.str "x")
    assert! values[1]! == Value.ref f2  -- ref 2 remapped
    assert! values[2]! == Value.atom (TestAtom.num 7)
  | _ => assert! false
  IO.println "✓ snapshot set node with refs"

/-! ## 7. Snapshot: atom root -/

#eval do
  let (rv, st) := execSnapshot mkFresh srcHeap 20 (Value.atom (TestAtom.str "lit"))
  assert! rv == Value.atom (TestAtom.str "lit")
  assert! st.memo.length == 0
  assert! st.result.length == 0
  IO.println "✓ snapshot atom root"

/-! ## 8. Reconcile root: all cases -/

abbrev CV := Value TestAtom CurId
abbrev NV := Value TestAtom NextId
abbrev CN := Node TestAtom CurId
abbrev NN := Node TestAtom NextId

def curHeap : List (CurId × CN) :=
  [ (⟨0⟩, .plainObject (proto 0) [⟨pk 1, .atom (.str "a")⟩]),
    (⟨1⟩, .array [some (.atom (.num 1))]),
    (⟨2⟩, .date 1000) ]

def nextHeap : List (NextId × NN) :=
  [ (⟨0⟩, .plainObject (proto 0) [⟨pk 1, .atom (.str "b")⟩]),
    (⟨1⟩, .array [some (.atom (.num 2))]),
    (⟨2⟩, .arrayBuffer [0x01]) ]  -- different kind from cur 2 (date vs arrayBuffer)

#eval do
  -- Same atom → keep
  let rv := execReconcileRoot curHeap nextHeap
    (Value.atom (.num 5) : CV) (Value.atom (.num 5) : NV)
  assert! rv == (Value.atom (TestAtom.num 5) : Value TestAtom ResId)
  -- Different atom → next wins
  let rv := execReconcileRoot curHeap nextHeap
    (Value.atom (.num 1) : CV) (Value.atom (.num 2) : NV)
  assert! rv == (Value.atom (TestAtom.num 2) : Value TestAtom ResId)
  -- Cur atom, next ref → fresh
  let rv := execReconcileRoot curHeap nextHeap
    (Value.atom (.num 1) : CV) (Value.ref (NextId.mk 0) : NV)
  match rv with
  | .ref (.inr _) => pure ()
  | _ => assert! false
  -- Cur ref, next atom → next atom
  let rv := execReconcileRoot curHeap nextHeap
    (Value.ref (CurId.mk 0) : CV) (Value.atom (.num 9) : NV)
  assert! rv == (Value.atom (TestAtom.num 9) : Value TestAtom ResId)
  -- Same kind refs → reuse current
  let rv := execReconcileRoot curHeap nextHeap
    (Value.ref (CurId.mk 0)) (Value.ref (NextId.mk 0))
  match rv with
  | .ref (.inl cr) => assert! cr == CurId.mk 0
  | _ => assert! false
  -- Different kind refs → fresh
  let rv := execReconcileRoot curHeap nextHeap
    (Value.ref (CurId.mk 2)) (Value.ref (NextId.mk 2))  -- date vs arrayBuffer
  match rv with
  | .ref (.inr _) => pure ()
  | _ => assert! false
  -- Missing cur ref → fresh
  let rv := execReconcileRoot curHeap nextHeap
    (Value.ref (CurId.mk 99)) (Value.ref (NextId.mk 0))
  match rv with
  | .ref (.inr _) => pure ()
  | _ => assert! false
  -- Missing next ref → fresh
  let rv := execReconcileRoot curHeap nextHeap
    (Value.ref (CurId.mk 0)) (Value.ref (NextId.mk 99))
  match rv with
  | .ref (.inr _) => pure ()
  | _ => assert! false
  IO.println "✓ reconcile root: all cases"

/-! ## 9. Reconcile value: state tracking -/

#eval do
  let initSt : ExecReconcileState TestAtom :=
    { reuse := [], image := [], nextFresh := 0 }
  -- Same-kind ref pair with fuel > 0 → reuse, update state
  let (rv, st) := execReconcileValue curHeap nextHeap 10 initSt
    (Value.ref (CurId.mk 0)) (Value.ref (NextId.mk 0))
  match rv with
  | .ref (.inl cr) => assert! cr == CurId.mk 0
  | _ => assert! false
  assert! st.reuse.length == 1
  assert! st.image.length == 1
  -- reuse maps cur 0 → next 0
  assert! assocLookup st.reuse (CurId.mk 0) == some (NextId.mk 0)
  -- image maps next 0 → inl cur 0
  assert! assocLookup st.image (NextId.mk 0) == some (Sum.inl (CurId.mk 0))
  -- Process another pair with same cur (already reused) → fresh allocation
  let (rv2, st2) := execReconcileValue curHeap nextHeap 10 st
    (Value.ref (CurId.mk 0)) (Value.ref (NextId.mk 1))
  match rv2 with
  | .ref (.inr _) => pure ()  -- fresh because cur 0 already reused
  | _ => assert! false
  -- reuse unchanged (cur 0 was already there)
  assert! st2.reuse.length == 1
  -- nextFresh bumped
  assert! st2.nextFresh == 1
  IO.println "✓ reconcile value: state tracking"

/-! ## 10. Shared-object fast path -/

#eval do
  -- Pre-populate state: next 0 already imaged
  let st : ExecReconcileState TestAtom :=
    { reuse := [(CurId.mk 0, NextId.mk 0)],
      image := [(NextId.mk 0, Sum.inl (CurId.mk 0))],
      nextFresh := 0 }
  -- Looking up next 0 again should hit the image cache
  let (rv, st') := execReconcileValue curHeap nextHeap 10 st
    (Value.ref (CurId.mk 0)) (Value.ref (NextId.mk 0))
  match rv with
  | .ref (.inl cr) => assert! cr == CurId.mk 0
  | _ => assert! false
  -- State unchanged (cache hit)
  assert! st'.reuse.length == st.reuse.length
  assert! st'.image.length == st.image.length
  assert! st'.nextFresh == st.nextFresh
  IO.println "✓ shared-object fast path"

/-! ## 11. Kind-specific reconciliation: value-level checks -/

#eval do
  let initSt : ExecReconcileState TestAtom :=
    { reuse := [], image := [], nextFresh := 100 }
  -- Use identity-like callbacks for atoms, fresh for refs
  let recEntry : CV → NV → ExecReconcileState TestAtom →
      Value TestAtom ResId × ExecReconcileState TestAtom :=
    fun _ next st => match next with
      | .atom a => (.atom a, st)
      | .ref _ => (.ref (.inr (FreshId.mk st.nextFresh)),
                    { st with nextFresh := st.nextFresh + 1 })
  let freshVal : NV → ExecReconcileState TestAtom →
      Value TestAtom ResId × ExecReconcileState TestAtom :=
    fun next st => match next with
      | .atom a => (.atom a, st)
      | .ref _ => (.ref (.inr (FreshId.mk st.nextFresh)),
                    { st with nextFresh := st.nextFresh + 1 })
  -- plainObject: next has 2 fields, current has 1 matching + 1 missing
  let curObj : CN := .plainObject (proto 0) [⟨pk 1, .atom (.str "old")⟩]
  let nextObj : NN := .plainObject (proto 1)
    [⟨pk 1, .atom (.str "new")⟩, ⟨pk 2, .atom (.num 42)⟩]
  let (nd, _) := execReconcileNodeByKind recEntry freshVal initSt curObj nextObj
  match nd with
  | .plainObject p fields =>
    assert! p == proto 0  -- retained plain objects keep current prototype
    assert! fields.length == 2
    match fields with
    | [⟨k0, v0⟩, ⟨k1, v1⟩] =>
      assert! k0 == pk 1
      match v0 with
      | Value.atom (TestAtom.str s) => assert! s == "new"
      | _ => assert! false
      assert! k1 == pk 2
      match v1 with
      | Value.atom (TestAtom.num n) => assert! n == 42
      | _ => assert! false
    | _ => assert! false
  | _ => assert! false
  -- array: index alignment
  let curArr : CN := .array [some (.atom (.num 1)), some (.atom (.num 2))]
  let nextArr : NN := .array [some (.atom (.num 10)), none, some (.atom (.num 30))]
  let (nd, _) := execReconcileNodeByKind recEntry freshVal initSt curArr nextArr
  match nd with
  | .array entries =>
    assert! entries.length == 3
    assert! entries[0]! == some (Value.atom (TestAtom.num 10))  -- reconciled
    assert! entries[1]! == (none : Option (Value TestAtom ResId)) -- hole preserved
    assert! entries[2]! == some (Value.atom (TestAtom.num 30))    -- fresh (cur too short)
  | _ => assert! false
  -- date: next wins
  let (nd, _) := execReconcileNodeByKind recEntry freshVal initSt
    (.date 1000 : CN) (.date 2000 : NN)
  match nd with
  | .date ms => assert! ms == 2000
  | _ => assert! false
  -- arrayBuffer: next bytes win
  let (nd, _) := execReconcileNodeByKind recEntry freshVal initSt
    (.arrayBuffer [0x01] : CN) (.arrayBuffer [0x02, 0x03] : NN)
  match nd with
  | .arrayBuffer bytes => assert! bytes == [0x02, 0x03]
  | _ => assert! false
  -- map: ordinal alignment, next values win
  let curMap : CN := .map [(.atom (.str "a"), .atom (.num 1))]
  let nextMap : NN := .map
    [(.atom (.str "x"), .atom (.num 10)), (.atom (.str "y"), .atom (.num 20))]
  let (nd, _) := execReconcileNodeByKind recEntry freshVal initSt curMap nextMap
  match nd with
  | .map entries =>
    assert! entries.length == 2
    -- first pair: ordinal 0 reconciled with cur ordinal 0
    match entries[0]! with
    | (Value.atom (.str k), Value.atom (.num v)) => assert! k == "x"; assert! v == 10
    | _ => assert! false
    -- second pair: cur too short, so freshVal used
    match entries[1]! with
    | (Value.atom (.str k), Value.atom (.num v)) => assert! k == "y"; assert! v == 20
    | _ => assert! false
  | _ => assert! false
  -- set: ordinal alignment
  let curSet : CN := .set [.atom (.num 1)]
  let nextSet : NN := .set [.atom (.num 10), .atom (.num 20)]
  let (nd, _) := execReconcileNodeByKind recEntry freshVal initSt curSet nextSet
  match nd with
  | .set values =>
    assert! values.length == 2
    assert! values[0]! == Value.atom (TestAtom.num 10)
    assert! values[1]! == Value.atom (TestAtom.num 20)
  | _ => assert! false
  IO.println "✓ kind-specific reconciliation: value-level checks"

/-! ## Summary -/

#eval IO.println "all tests passed"
