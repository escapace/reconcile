import Spec.Graph

/-!
# `reconcile`: the reference model

The executable reference that `reconcile(current, next)` must agree with, over `Spec.Graph`
graphs, in three phases that mirror the runtime's design:

1. **Read.** A depth-first walk of `next` from its root, children in slot order, aligns each
   `next` node on its first visit with the `current` object at the same position (key, index or
   entry position) of its parent's aligned object, when that object has the same kind. A `next`
   node that is a `current` object at its own position, whose subtree reaches neither root, is
   *pinned*: kept as it is, together with everything inside it, which no other position may keep.
2. **Decide.** In visit order, a node is kept as its aligned object when the object is not
   protected or already kept, has the same kind and admits `next`'s contents statically: its
   descriptors and extensibility allow the writes, no key it lacks reaches a getter or setter on
   its class prototype, and every key that cannot move lies in the retained prefix of the key
   order (`retainPrefix`). A buffer is kept only with `next`'s length and maximum, and a view only
   with `next`'s constructor, offset and length; a view's buffer, which cannot change, is held
   like a fixed slot. Nothing is written before this phase ends; a root that cannot be kept
   rejects the call.
3. **Write.** Kept nodes take `next`'s contents, writing only what differs; fresh nodes are
   copies. A kept object whose write reaches a setter that drops its value is *blocked*: it is
   demoted to a fresh copy, and the pass repeats for the nodes that change as a consequence,
   until no node is blocked. A blocked root rejects the call.

The result is one node per `next` node, with the `current` object it keeps, if any, and the
observation counts of the trace model.
-/

namespace Reconcile.Spec

/-- A position inside a node, by which `next` slots align with `current` slots. -/
inductive Pos where
  | key (k : String)
  | index (i : Nat)
  | mapKey (p : Nat)
  | mapValue (p : Nat)
  | member (p : Nat)
  /-- A view's buffer. -/
  | buffer
  deriving DecidableEq, Repr

/-- Whether a position is a property or an array element: an object already in place is kept only
at such a position, never as a `Map` or `Set` entry or a view's buffer. -/
def Pos.property : Pos → Bool
  | .key _ | .index _ => true
  | _ => false

/-- The slots of a node in traversal order, with their positions. -/
def Obj.slots : Obj → List (Pos × Val)
  | .object _ fields _ => fields.map fun (k, s) => (.key k, s.value)
  | .array entries _ => entries.zipIdx.filterMap fun (e, i) => e.map fun v => (.index i, v)
  | .map entries => entries.zipIdx.flatMap fun ((k, v), p) => [(.mapKey p, k), (.mapValue p, v)]
  | .set members => members.zipIdx.map fun (v, p) => (.member p, v)
  | .date _ => []
  | .buffer .. => []
  | .view _ storage _ _ => [(.buffer, storage)]

/-- The value a node holds at a position, if any. -/
def Obj.occupant (o : Obj) (pos : Pos) : Option Val :=
  match o, pos with
  | .object _ fields _, .key k => (fields.lookup k).map Slot.value
  | .array entries _, .index i => entries[i]?.bind id
  | .map entries, .mapKey p => entries[p]?.map Prod.fst
  | .map entries, .mapValue p => entries[p]?.map Prod.snd
  | .set members, .member p => members[p]?
  | .view _ storage _ _, .buffer => some storage
  | _, _ => none

def Val.refId : Val → Option Nat
  | .ref id => some id
  | .prim _ => none

/-- The traversal budget of a graph: one step per node and per reference. -/
def Graph.budget (g : Graph) : Nat :=
  g.nodes.size + (g.nodes.toList.map (·.refs.length)).sum + 1

end Reconcile.Spec

namespace Reconcile.Spec.Reconcile

open Reconcile.Spec

/-- The input: the current graph, the next graph, for each next node the current node that is
the same object, if any, and the own slots of each class prototype, which an object labelled
`cls id` inherits. `Object.prototype` and `null` carry no slots in the model. -/
structure Input where
  cur : Graph
  next : Graph
  same : Array (Option Nat)
  classes : Array (List (String × Slot)) := #[]

/-- Whether `l` is a subsequence of `m`. -/
def isSubseq {K : Type} [DecidableEq K] : List K → List K → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then isSubseq as bs else isSubseq (a :: as) bs

/-- The length of the longest prefix of `next` of length at most `k` that is a subsequence of
`cur`. -/
def retainLength {K : Type} [DecidableEq K] (cur next : List K) : Nat → Nat
  | 0 => 0
  | k + 1 => if isSubseq (next.take (k + 1)) cur then k + 1 else retainLength cur next k

/-- The longest prefix of `next` that is a subsequence of `cur`: the keys or entries that keep
their place when `cur`'s order becomes `next`'s. Deleting and adding a key or entry appends it, so
the untouched ones precede every re-added one and keep their relative order. -/
def retainPrefix {K : Type} [DecidableEq K] (cur next : List K) : List K :=
  next.take (retainLength cur next next.length)

/-! ## Read -/

/-- Discovery: the next nodes in first-visit order, the current object each is aligned with for
pinning, and per next node the current objects that are candidates for it, in discovery order.

Two walks flow from the roots. The first is the depth-first walk of `next` that capture makes,
children in slot order, each node visited once; it fixes the visit order and the *pinning*
alignment, which follows property and array-element edges only, through parents aligned the same
way with an object of their kind: it is what "the object at the same position" means for an
object already in place, and a `Map` or `Set` entry or a view's buffer breaks it. The second walk
is over pairs of a next node and a candidate, each walked once: a *candidate* of node `j` is the
object at the same position, of `j`'s kind, inside any candidate of any parent of `j`, through
every position. A pinned node has no candidate. -/
structure Discovery where
  order : List Nat
  first : Array (Option Nat)
  pinned : Array Bool
  candidates : Array (List Nat)

/-- The depth-first walk of `next`: per pending node the pinning alignment its edge offers. Returns
the nodes in visit order and the alignment of each. -/
private def visitStep (cur next : Graph) :
    Nat → List (Nat × Option Nat) → Array Bool → Array (Option Nat) → List Nat →
      List Nat × Array (Option Nat)
  | 0, _, _, first, order => (order.reverse, first)
  | _ + 1, [], _, first, order => (order.reverse, first)
  | fuel + 1, (j, pinning) :: rest, visited, first, order =>
    if visited[j]?.getD true then visitStep cur next fuel rest visited first order
    else
      let node := next.node j
      let aligned := pinning.filter fun p => (cur.node p).kind == node.kind
      let children := node.slots.filterMap fun (pos, v) =>
        match v with
        | .ref c => some (c, if pos.property then
            aligned.bind fun p => ((cur.node p).occupant pos).bind Val.refId else none)
        | .prim _ => none
      visitStep cur next fuel (children ++ rest) (visited.setIfInBounds j true)
        (first.setIfInBounds j aligned) (j :: order)

/-- The walk over pairs of a next node and the candidate a walked parent offers. -/
private def candidateStep (cur next : Graph) :
    Nat → List (Nat × Option Nat) → Array (List Nat) → Array (List Nat)
  | 0, _, candidates => candidates
  | _ + 1, [], candidates => candidates
  | fuel + 1, (j, candidate) :: rest, candidates =>
    let node := next.node j
    -- A path without a candidate parent offers no candidate below.
    match candidate.filter fun p => (cur.node p).kind == node.kind with
    | none => candidateStep cur next fuel rest candidates
    | some p =>
      if (candidates[j]?.getD []).contains p then candidateStep cur next fuel rest candidates
      else
        let children := node.slots.filterMap fun (pos, v) =>
          match v with
          | .ref c => some (c, ((cur.node p).occupant pos).bind Val.refId)
          | .prim _ => none
        candidateStep cur next fuel (children ++ rest)
          (candidates.setIfInBounds j ((candidates[j]?.getD []) ++ [p]))

/-- The nodes reachable from `start` in `g`, `start` included. -/
def reach (g : Graph) (start : Nat) : List Nat :=
  go g.budget [start] []
where
  go : Nat → List Nat → List Nat → List Nat
    | 0, _, seen => seen
    | _ + 1, [], seen => seen
    | fuel + 1, id :: rest, seen =>
      if seen.contains id then go fuel rest seen
      else go fuel ((g.node id).refs ++ rest) (id :: seen)

/-- Whether a node of this kind can be kept as it is: a buffer, which supplies its views'
construction, and a view, which its buffer constructs, cannot. -/
def keepable : Kind → Bool
  | .buffer | .typedArray | .dataView => false
  | _ => true

/-- Whether next node `j` is pinned: the current object at its own position, of a kind that can be
kept as it is, whose subtree reaches neither root. The current root is never pinned. -/
def pinnedAt (input : Input) (first : Array (Option Nat)) (j : Nat) : Bool :=
  match input.same[j]?.bind id, first[j]?.bind id with
  | some i, some i' =>
    let reached := reach input.cur i
    let nextRootCur := input.next.root.refId.bind fun r => input.same[r]?.bind id
    i = i' && keepable (input.next.node j).kind && input.cur.root.refId != some i &&
      !(reached.contains (input.cur.root.refId.getD i)) &&
      !(match nextRootCur with
        | some rootCur => reached.contains rootCur
        | none => false)
  | _, _ => false

/-- The pinned next nodes, from the visit order and the pinning alignments: those pinned at their
position and everything inside them, plus every next node that is a current object inside a pinned
subtree. -/
def pinned (input : Input) (order : List Nat) (first : Array (Option Nat)) : Array Bool :=
  let roots := order.filter (pinnedAt input first)
  let inside := roots.flatMap (reach input.next)
  let protectedCur := inside.filterMap fun j => input.same[j]?.bind id
  (Array.range input.next.nodes.size).map fun j =>
    inside.contains j ||
      match input.same[j]?.bind id with
      | some i => protectedCur.contains i
      | none => false

/-- Discovers the visit order, the pinning alignments, the pinned nodes and the candidates of every
next node from the roots. A pinned node, which capture keeps as it is, has no candidate. -/
def discover (input : Input) : Discovery :=
  let n := input.next.nodes.size
  match input.next.root with
  | .prim _ => ⟨[], Array.replicate n none, Array.replicate n false, Array.replicate n []⟩
  | .ref r =>
    let root := input.cur.root.refId
    let (order, first) := visitStep input.cur input.next input.next.budget [(r, root)]
      (Array.replicate n false) (Array.replicate n none) []
    let pin := pinned input order first
    let found := candidateStep input.cur input.next
      (input.next.budget * (input.cur.nodes.size + 1)) [(r, root)] (Array.replicate n [])
    ⟨order, first, pin, found.mapIdx fun j cs => if pin[j]?.getD false then [] else cs⟩

/-! ## Decide -/

def keysOf : Obj → List String
  | .object _ fields _ => fields.map Prod.fst
  | _ => []

/-- Whether a slot's value cannot be written: a non-writable, non-configurable data property or an
accessor without a setter. -/
def _root_.Reconcile.Spec.Slot.fixed : Slot → Bool
  | .data _ a => !a.writable && !a.configurable
  | .accessor _ none _ _ => true
  | .accessor _ (some _) _ _ => false

/-- The own slots of the class prototype an object labelled `proto` inherits. -/
def classSlots (classes : Array (List (String × Slot))) : Proto → List (String × Slot)
  | .cls id => classes[id]?.getD []
  | _ => []

/-- Whether assigning `k` to an object that lacks it would reach an inherited getter or setter,
which is never written or overridden: such an object cannot take the key in place. -/
def reachesInheritedAccessor (inherited : List (String × Slot)) (k : String) : Bool :=
  match inherited.lookup k with
  | some (.accessor ..) => true
  | _ => false

/-- Whether a kept object can take `next`'s contents apart from the values of its fixed slots:
keys `next` lacks are deletable, the object can grow when `next` adds keys, no added key reaches
an inherited accessor, and every key that cannot move lies in the retained prefix. -/
def objectAdmits (cFields : List (String × Slot)) (extensible : Bool)
    (nFields : List (String × Slot)) (inherited : List (String × Slot)) : Bool :=
  let nKeys := nFields.map Prod.fst
  let cKeys := cFields.map Prod.fst
  let retained := retainPrefix cKeys nKeys
  -- A key that is absent or moves is added by assignment, which a non-extensible object refuses.
  nFields.all (fun (k, _) => extensible || retained.contains k) &&
  nFields.all (fun (k, _) => cKeys.contains k || !reachesInheritedAccessor inherited k) &&
  cFields.all (fun (k, cs) => nKeys.contains k || cs.configurable) &&
  cFields.all (fun (k, cs) =>
    let immovable := match cs with
      | .data _ a => !a.configurable
      | .accessor .. => true
    !immovable || !nKeys.contains k || retained.contains k)

/-- Whether a kept array can take `next`'s entries under its extensibility level, apart from the
values of a frozen array's entries: a non-extensible array gains no element, a sealed one also
loses none, and a frozen one changes nothing. -/
def arrayAdmits (cEntries : List (Option Val)) (ext : Ext) (nEntries : List (Option Val)) :
    Bool :=
  let present (entries : List (Option Val)) (i : Nat) : Bool := (entries[i]?.bind id).isSome
  let noneAdded := nEntries.zipIdx.all fun (n, i) => !n.isSome || present cEntries i
  let noneLost := cEntries.zipIdx.all fun (c, i) => !c.isSome || present nEntries i
  match ext with
  | .extensible => true
  | .nonExtensible => noneAdded
  | .sealed => noneAdded && noneLost
  | .frozen => noneAdded && noneLost && cEntries.length = nEntries.length

/-- Whether current object `c` can be kept with next contents `n`, apart from its fixed slots. -/
def admitsStatic (classes : Array (List (String × Slot))) (c n : Obj) : Bool :=
  match c, n with
  | .object p cf ext, .object _ nf _ => objectAdmits cf ext nf (classSlots classes p)
  | .array ce ext, .array ne _ => arrayAdmits ce ext ne
  | .map _, .map _ => true
  | .set _, .set _ => true
  | .date _, .date _ => true
  | .buffer cb cm, .buffer nb nm => cb.length == nb.length && cm == nm
  | .view cc _ co cl, .view nc _ no nl => cc == nc && co == no && cl == nl
  | _, _ => false

/-- The fixed slots of a kept object as pairs of the current value and the next value at the
same position: every entry of a frozen array, every fixed key of an object, and a view's
buffer. -/
def fixedPairs (c n : Obj) : List (Val × Val) :=
  match c, n with
  | .object _ cf _, .object _ nf _ =>
    cf.filterMap fun (k, cs) =>
      if cs.fixed then (nf.lookup k).map fun ns => (cs.value, ns.value) else none
  | .array ce .frozen, .array ne _ =>
    (ce.zip ne).filterMap fun
      | (some cv, some nv) => some (cv, nv)
      | _ => none
  | .view _ cb _ _, .view _ nb _ _ => [(cb, nb)]
  | _, _ => []

/-- A requirement: next node `c` keeps current object `x`. -/
abbrev Requirement := Nat × Nat

/-- Whether current object `x` passes the preflight for next node `c`: its static checks pass,
every fixed slot holding a primitive holds the value `next` has there, and the fixed slots holding
objects require each node to keep one object, a pinned node the object it is. -/
def admitted (input : Input) (pin : Array Bool) (c x : Nat) : Bool :=
  let cur := input.cur.node x
  let nxt := input.next.node c
  let pairs := fixedPairs cur nxt
  admitsStatic input.classes cur nxt && pairs.all fun
    | (.prim p, .prim q) => p == q
    | (.ref x', .ref c') =>
      (!(pin[c']?.getD false) || input.same[c']?.bind id == some x') &&
        pairs.all fun
          | (.ref y, .ref d) => d != c' || y == x'
          | _ => true
    | _ => false

/-- The requirements the admitted candidates of every node make: that the node at each fixed slot
holding an object keeps that object. A candidate whose fixed slots require two objects at one node,
or another object at a pinned node, is not admitted, and a demand that would have the candidate's
own node keep another object is left out: the candidate could never be kept with them, so they must
not reorder a node. -/
def demands (input : Input) (al : Discovery) : List Requirement :=
  (List.range input.next.nodes.size).flatMap fun c =>
    (al.candidates[c]?.getD []).flatMap fun x =>
      if admitted input al.pinned c x then
        (fixedPairs (input.cur.node x) (input.next.node c)).filterMap fun
          | (.ref x', .ref c') => if c' = c && x' != x then none else some (c', x')
          | _ => none
      else []

/-- The candidates of next node `j` in decision order: those some admitted candidate requires
there first, then the rest, each in discovery order. Keeping what a fixed slot holds lets the
decision keep the slot's owner too. -/
def orderedCandidates (input : Input) (al : Discovery) (j : Nat) : List Nat :=
  let found := al.candidates[j]?.getD []
  let wanted := (demands input al).filterMap fun (c, x) => if c = j then some x else none
  found.filter wanted.contains ++ found.filter (fun x => !wanted.contains x)

/-- Establishes that next node `c` can keep current object `x`: `x` is a candidate of `c`, not
blocked by an earlier pass, not reserved for another node, its static checks pass, and every
fixed slot holds its value, a fixed slot holding an object requiring the next node at that
position to keep that object. Nodes already decided, and nodes an earlier decision requires an
object at, must agree; pairs being established may repeat. An object is reserved for another node
when an earlier decision of this pass kept it, or an earlier pass wrote it at another node
(`written`). Returns the requirements to reserve, `c` keeping `x` first. -/
def establish (input : Input) (candidatesOf : Nat → List Nat) (forbidden : List Nat)
    (written : List Requirement) (kept : Array (Option Nat)) (decided : Array Bool)
    (required : Array (Option Nat)) (used : List Nat) :
    Nat → List Requirement → Nat → Nat → Option (List Requirement)
  | 0, _, _, _ => none
  | fuel + 1, chain, c, x =>
    if chain.contains (c, x) then some chain
    else if chain.any (fun (c', x') => c' = c || x' = x) then none
    else if decided[c]?.getD false then
      if kept[c]?.bind id = some x then some chain else none
    else if (required[c]?.bind id).isSome then
      if required[c]?.bind id = some x then some chain else none
    else if forbidden.contains x || (used.contains x && !written.contains (c, x)) ||
        !(candidatesOf c).contains x then
      none
    else
      let cur := input.cur.node x
      let nxt := input.next.node c
      if !admitsStatic input.classes cur nxt then none
      else
        (fixedPairs cur nxt).foldl (fun acc (cv, nv) =>
          acc.bind fun chain =>
            match cv, nv with
            | .prim p, .prim q => if p = q then some chain else none
            | .ref x', .ref c' =>
              establish input candidatesOf forbidden written kept decided required used fuel chain
                c' x'
            | _, _ => none) (some ((c, x) :: chain))

/-- The decision state: the object kept per next node, the current objects reserved, the nodes
decided, and the object a decided parent requires at a node not yet visited. -/
structure Decision where
  kept : Array (Option Nat)
  used : List Nat
  decided : Array Bool
  required : Array (Option Nat)

/-- Decides which next nodes keep a current object, in visit order: a pinned node keeps the
object it is; a node a decided parent requires keeps that object; another node keeps the object
an earlier pass wrote there when it still can, else its first candidate that can be established,
reserving the objects its fixed slots require. An object a write phase found blocked is
`forbidden`, and one an earlier pass wrote is `written` at its node: it stays there or is dropped,
so no object holds another node's writes. -/
def decide (input : Input) (al : Discovery) (pin : Array Bool) (forbidden : List Nat)
    (written : List Requirement) : Array (Option Nat) :=
  let n := input.next.nodes.size
  let fuel := input.cur.nodes.size + 1
  -- The root's only candidate is `current` itself; a cycle back to the root offers no other. The
  -- object an earlier pass wrote at a node comes first.
  let candidatesOf (j : Nat) : List Nat :=
    if input.next.root.refId = some j then input.cur.root.refId.toList
    else
      let found := orderedCandidates input al j
      match written.lookup j with
      | some y => if found.contains y then y :: found.filter (· != y) else found
      | none => found
  let start : Decision :=
    { kept := (Array.range n).map (fun j =>
        if pin[j]?.getD false then input.same[j]?.bind id else none),
      used := (List.range n).filterMap (fun j =>
        if pin[j]?.getD false then input.same[j]?.bind id else none) ++ written.map Prod.snd,
      decided := pin,
      required := Array.replicate n none }
  (al.order.foldl (fun (d : Decision) j =>
    if d.decided[j]?.getD false then d
    else
      let decided := d.decided.setIfInBounds j true
      match d.required[j]?.bind id with
      | some x => { d with kept := d.kept.setIfInBounds j (some x), decided }
      | none =>
        match (candidatesOf j).findSome? fun x =>
            establish input candidatesOf forbidden written d.kept d.decided d.required d.used fuel
              [] j x
          with
        | none => { d with decided }
        | some pairs =>
          pairs.foldl (fun (d : Decision) (c, x) =>
            if c = j then { d with kept := d.kept.setIfInBounds j (some x), used := x :: d.used }
            else { d with required := d.required.setIfInBounds c (some x), used := x :: d.used })
            { d with decided }) start).kept

/-! ## Write -/

/-- Whether writing `next` value `nv` into a slot holding current value `cv` changes it: a
primitive differs by value, a reference by the identity its node resolves to; a fresh node always
differs. -/
def differs (identity : Nat → Option Nat) (cv nv : Val) : Bool :=
  match nv with
  | .prim p => cv != .prim p
  | .ref c =>
    match identity c with
    | some x => cv != .ref x
    | none => true

/-- The slot a kept key becomes: its own slot holding the next value. -/
def slotWith : Slot → Val → Slot
  | .data _ a, v => .data v a
  | .accessor _ s e c, v => .accessor v s e c

def attrsOf : Slot → Attrs
  | .data _ a => a
  | .accessor _ _ e c => ⟨true, e, c⟩

/-- A kept object with `next`'s contents: keys in `next`'s order; a key in the retained prefix
keeps its own slot with the new value, a moved key keeps its attributes, an added key is
writable and configurable with `next`'s enumerability; prototype and extensibility stay. -/
def keptObject (proto : Proto) (cFields : List (String × Slot)) (extensible : Bool)
    (nFields : List (String × Slot)) : Obj :=
  let retained := retainPrefix (cFields.map Prod.fst) (nFields.map Prod.fst)
  .object proto (nFields.map fun (k, ns) =>
    (k, match cFields.lookup k with
      | some cs => if retained.contains k then slotWith cs ns.value else .data ns.value (attrsOf cs)
      | none => .data ns.value ⟨true, ns.enumerable, true⟩)) extensible

/-- A fresh copy of a `next` node: data properties, writable and configurable with the source's
enumerability, the source's prototype, extensible. -/
def freshCopy : Obj → Obj
  | .object proto fields _ =>
    .object proto (fields.map fun (k, s) => (k, .data s.value ⟨true, s.enumerable, true⟩)) true
  | .array entries _ => .array entries .extensible
  | o => o

/-- The result contents of a kept node. -/
def keptObj (c n : Obj) : Obj :=
  match c, n with
  | .object proto cf ext, .object _ nf _ => keptObject proto cf ext nf
  | .array _ ext, .array ne _ => .array ne (observedExt ne ext)
  | _, _ => n

/-- The writes a kept object needs, as `(key, kind)` with kind `set` or `delete`, and whether one
of them reaches a setter that drops its value. -/
def objectWrites (identity : Nat → Option Nat) (cFields nFields : List (String × Slot)) :
    List (String × String) × Bool :=
  let nKeys := nFields.map Prod.fst
  let retained := retainPrefix (cFields.map Prod.fst) nKeys
  let deletes := cFields.filterMap fun (k, _) =>
    if nKeys.contains k && retained.contains k then none else some (k, "delete")
  let sets := nFields.filterMap fun (k, ns) =>
    match cFields.lookup k with
    | some cs =>
      if retained.contains k then
        if differs identity cs.value ns.value then some (k, "set") else none
      else some (k, "set")
    | none => some (k, "set")
  -- A write that reaches a setter that drops its value, or a fixed slot, cannot take effect.
  let blocked := nFields.any fun (k, ns) =>
    match cFields.lookup k with
    | some (.accessor v (some false) _ _) =>
      retained.contains k && differs identity v ns.value
    | some cs => cs.fixed && retained.contains k && differs identity cs.value ns.value
    | none => false
  (deletes ++ sets, blocked)

/-- The writes a kept array needs. -/
def arrayWrites (identity : Nat → Option Nat) (ce ne : List (Option Val)) :
    List (String × String) :=
  let length := if ce.length = ne.length then [] else [("length", "set")]
  let indices := (List.range (max ce.length ne.length)).filterMap fun i =>
    match ce[i]?.bind id, ne[i]?.bind id with
    | some cv, some nv => if differs identity cv nv then some (toString i, "set") else none
    | none, some _ => some (toString i, "set")
    | some _, none => if i < ne.length then some (toString i, "delete") else none
    | none, none => none
  length ++ indices

/-- The writes a kept map or set needs under the retained prefix of its entries. A key of `next`
that is a node stands for the object that node keeps; a fresh node's object is no current key. -/
def collectionWrites (identity : Nat → Option Nat) (cKeys nKeys : List Val)
    (cValue nValue : Val → Option Val) : List (String × String) :=
  let resolve : Val → Option Val
    | .prim p => some (.prim p)
    | .ref c => (identity c).map Val.ref
  let resolved := nKeys.map resolve
  let retained := retainPrefix (cKeys.map some) resolved
  let label : Val → String
    | .prim .undef => "undefined"
    | .prim .null => "null"
    | .prim (.bool b) => toString b
    | .prim (.num n) => toString n
    | .prim (.str t) => t
    | .prim (.atom id) => s!"atom {id}"
    | .ref id => s!"ref {id}"
  let deletes := cKeys.filterMap fun k =>
    if resolved.contains (some k) && retained.contains (some k) then none
    else some (label k, "delete")
  let sets := nKeys.filterMap fun k =>
    match resolve k with
    | some ck =>
      if retained.contains (some ck) then
        match cValue ck, nValue k with
        | some cv, some nv => if differs identity cv nv then some (label ck, "set") else none
        | _, _ => none
      else some (label ck, "set")
    | none => some (label k, "set")
  deletes ++ sets

/-- The writes of keeping `c` with contents `n`, and whether they block. -/
def writesOf (identity : Nat → Option Nat) (c n : Obj) : List (String × String) × Bool :=
  match c, n with
  | .object _ cf _, .object _ nf _ => objectWrites identity cf nf
  | .array ce ext, .array ne _ =>
    let writes := arrayWrites identity ce ne
    (writes, ext = .frozen && !writes.isEmpty)
  | .map ce, .map ne =>
    (collectionWrites identity (ce.map Prod.fst) (ne.map Prod.fst) (ce.lookup ·) (ne.lookup ·),
      false)
  | .set cm, .set nm => (collectionWrites identity cm nm (fun _ => none) (fun _ => none), false)
  | .date cms, .date nms => (if cms = nms then [] else [("time", "set")], false)
  | .buffer cb _, .buffer nb _ => (if cb = nb then [] else [("bytes", "set")], false)
  | _, _ => ([], false)

/-- The identity a next node resolves to under a decision. -/
def identityOf (kept : Array (Option Nat)) (j : Nat) : Option Nat := kept[j]?.bind id

/-- The objects kept at unpinned nodes whose writes block. -/
def blockedObjects (input : Input) (pin : Array Bool) (kept : Array (Option Nat)) : List Nat :=
  (List.range input.next.nodes.size).filterMap fun j =>
    if pin[j]?.getD false then none
    else match kept[j]?.bind id with
      | some i =>
        if (writesOf (identityOf kept) (input.cur.node i) (input.next.node j)).2 then some i
        else none
      | none => none

/-- The objects a decision keeps at unpinned nodes, which its pass writes, with their nodes. -/
def writtenPairs (input : Input) (pin : Array Bool) (kept : Array (Option Nat)) :
    List Requirement :=
  (List.range input.next.nodes.size).filterMap fun j =>
    if pin[j]?.getD false then none
    else (kept[j]?.bind id).map fun i => (j, i)

/-- Decides, and while a kept object's writes block, forbids those objects and decides again with
the written objects at their nodes: the decision of each pass in order, the last one final. Each
pass forbids an object, so there are at most as many passes as objects, plus one. -/
def demote (input : Input) (al : Discovery) (pin : Array Bool) :
    Nat → List Nat → List Requirement → List (Array (Option Nat))
  | 0, forbidden, written => [decide input al pin forbidden written]
  | fuel + 1, forbidden, written =>
    let kept := decide input al pin forbidden written
    let blocked := blockedObjects input pin kept
    if blocked.isEmpty then [kept]
    else
      kept :: demote input al pin fuel (forbidden ++ blocked)
        (written ++ writtenPairs input pin kept)

/-! ## Outcome -/

/-- The result of the reference: whether the call succeeds, and per next node the current object
kept there and the contents; `root` is the result's root. The trace fields count observations:
`gets` per current object and key, `writes` per kept current object. -/
structure Outcome where
  ok : Bool
  origins : Array (Option Nat)
  nodes : Array Obj
  root : Val
  /-- The number of decision passes: one, plus one per demotion. -/
  passes : Nat
  gets : List (Nat × String × Nat)
  /-- The final decision's writes, as `(current object, key, kind)`. -/
  writes : List (Nat × String × String)
  /-- The writes of every pass, without duplicates: a pass writes what its decision needs, and a
  later pass writes a slot again when its decision keeps another object there. -/
  allWrites : List (Nat × String × String)
  deriving Lean.ToJson, Repr

/-- Whether current object `i` holds `k` as an accessor, whose getter a read of the key runs. -/
def accessorKey (input : Input) (i : Nat) (k : String) : Bool :=
  match input.cur.node i with
  | .object _ cf _ =>
    match cf.lookup k with
    | some (.accessor ..) => true
    | _ => false
  | _ => false

/-- The getters the read phase runs: each accessor of a candidate at a key of a next node it is a
candidate of, once per current object and key however many nodes share the candidate. -/
def capturedKeys (input : Input) (al : Discovery) : List (Nat × String) :=
  ((List.range input.next.nodes.size).flatMap fun j =>
    (al.candidates[j]?.getD []).flatMap fun i =>
      (keysOf (input.next.node j)).filterMap fun k =>
        if accessorKey input i k then some (i, k) else none).eraseDups

/-- The getters a pass's readback runs after its writes: each accessor of each current object the
pass keeps, unpinned, at a key of the next node kept as it, once per object and key. A write
anywhere can change any kept object, so every kept object is read back. -/
def readbackKeys (input : Input) (pin : Array Bool) (kept : Array (Option Nat)) :
    List (Nat × String) :=
  ((List.range input.next.nodes.size).flatMap fun j =>
    if pin[j]?.getD false then []
    else match kept[j]?.bind id with
      | some i => (keysOf (input.next.node j)).filterMap fun k =>
          if accessorKey input i k then some (i, k) else none
      | none => []).eraseDups

/-- The getter count per current object and key: one for its capture read and one per pass that
reads it back. -/
def getCounts (captured : List (Nat × String)) (readbacks : List (List (Nat × String))) :
    List (Nat × String × Nat) :=
  (captured ++ readbacks.flatten).eraseDups.map fun (i, k) =>
    (i, k, (if captured.contains (i, k) then 1 else 0) +
      (readbacks.filter (·.contains (i, k))).length)

/-- The writes of a decision: per kept, unpinned node, the writes its object needs. -/
def writesOfDecision (input : Input) (pin : Array Bool) (kept : Array (Option Nat)) :
    List (Nat × String × String) :=
  (List.range input.next.nodes.size).flatMap fun j =>
    match kept[j]?.bind id with
    | some i =>
      if pin[j]?.getD false then []
      else (writesOf (identityOf kept) (input.cur.node i) (input.next.node j)).1.map
        fun (k, w) => (i, k, w)
    | none => []

/-- The result of a successful final decision `kept` after the passes `rounds`: per next node the
kept object's contents or a fresh copy, the writes and the getter counts. A call whose passes write
nothing reads nothing back; otherwise each pass reads back the objects its decision keeps. -/
def publish (input : Input) (al : Discovery) (pin : Array Bool)
    (rounds : List (Array (Option Nat))) (kept : Array (Option Nat)) (r : Nat) : Outcome :=
  let n := input.next.nodes.size
  let nodes := (Array.range n).map fun j =>
    match kept[j]?.bind id with
    | some i => if pin[j]?.getD false then input.next.node j
      else keptObj (input.cur.node i) (input.next.node j)
    | none => freshCopy (input.next.node j)
  let writes := writesOfDecision input pin kept
  let allWrites := (rounds.map (writesOfDecision input pin)).flatten.eraseDups
  let readbacks := if allWrites.isEmpty then [] else rounds.map (readbackKeys input pin)
  { ok := true, origins := kept, nodes, root := .ref r, passes := rounds.length,
    gets := getCounts (capturedKeys input al) readbacks, writes, allWrites }

/-- The input with every array's extensibility as observed. -/
def normalized (raw : Input) : Input :=
  { raw with cur := raw.cur.normalize, next := raw.next.normalize }

/-- The demotion budget: one pass per pair of a next node and a current object, plus one. -/
def fuelOf (input : Input) : Nat := input.next.nodes.size * (input.cur.nodes.size + 1) + 1

/-- Runs the reference. -/
def run (raw : Input) : Outcome :=
  let input := normalized raw
  let n := input.next.nodes.size
  let asIs : Outcome :=
    { ok := true, origins := (Array.range n).map fun j => input.same[j]?.bind id,
      nodes := input.next.nodes, root := input.next.root, passes := 0, gets := [], writes := [],
      allWrites := [] }
  let rejected (passes : Nat) : Outcome :=
    { ok := false, origins := #[], nodes := #[], root := .prim .undef, passes, gets := [],
      writes := [], allWrites := [] }
  match input.cur.root, input.next.root with
  | .ref _, .ref r =>
    let al := discover input
    let pin := al.pinned
    let initial := decide input al pin [] []
    -- A root that cannot be kept rejects the call before any write.
    if (initial[r]?.bind id).isNone then rejected 0
    else
      let rounds := demote input al pin (fuelOf input) [] []
      let final := rounds.getLastD initial
      -- A root blocked by a write is rejected after the passes that found it.
      if (final[r]?.bind id).isNone then rejected rounds.length
      else publish input al pin rounds final r
  | _, _ => asIs

end Reconcile.Spec.Reconcile
