import Spec.Graph
import Property.Retain

/-!
# `reconcile`: the reference model

The executable reference that `reconcile(current, next)` must agree with, over `Spec.Graph`
graphs, in three phases that mirror the runtime's design:

1. **Read.** A depth-first walk of `next` from its root, children in slot order, aligns each
   `next` node on its first visit with the `current` object at the same key or index of its
   parent's aligned object, when that object has the same kind; a `Map` or `Set` entry or a view's
   buffer aligns nothing. A `next` node that is a `current` object at its own position, whose
   subtree reaches neither root, is *pinned*: kept as it is, together with everything inside it,
   which no other position may keep. Every other node's *candidates* are the objects of its kind
   at the same position, through every position, inside its parents' candidates.
2. **Decide.** In visit order, a node is kept as the first of its candidates
   (`orderedCandidates`) that is not protected or already kept, has the same kind and admits
   `next`'s contents statically: its descriptors and extensibility allow the writes, no key it
   lacks reaches a getter or setter on its class prototype, and every key that cannot move lies
   in the retained prefix of the key order (`retainPrefix`). A buffer is kept only with `next`'s
   length and maximum, and a view only with `next`'s constructor, offset and length; a view's
   buffer, which cannot change, is held like a fixed slot. Nothing is written before this phase
   ends; a root that cannot be kept rejects the call.
3. **Write.** Before a pass writes, its decision must keep `next` unchanged (`keepsNext`): no node
   keeps an object `next` holds at another node, and a node that keeps the very object it is, an
   *untouched* node, has only untouched nodes below it. A decision that fails rejects the call
   (`Outcome.changesNext`). Untouched nodes, like pinned ones, already hold their contents, so they
   are neither written nor read back. The other kept nodes take `next`'s contents, writing only
   what differs; fresh nodes are copies (`Obj.copy`). A kept object whose write reaches a fixed
   slot or a setter that drops its value is *blocked*: it is demoted to a fresh copy and never
   kept again, and the decision runs again, never moving an object a pass wrote to another node,
   until no node is blocked. A decision that keeps no root rejects the call, and the passes stop
   there.

The result is one node per `next` node, with the `current` object it keeps, if any, the number
of passes, and the trace model's observations: the getter runs of reading `next`, which capture
does in one walk that keeps each object already in place without visiting it (`captureReads`),
the getter runs of reading `current`, and the writes of every pass.
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
  | .object _ fields _, .key k => (fields.lookup k).map OwnProperty.value
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

/-- The longest prefix of `next` that is a subsequence of `cur`: the keys or entries that keep
their place when `cur`'s order becomes `next`'s. Deleting and adding a key or entry appends it, so
the untouched ones precede every re-added one and keep their relative order. It is the runtime's
greedy matching, `PropertyPlacement.matched`. -/
def retainPrefix {K : Type} [DecidableEq K] (cur next : List K) : List K :=
  PropertyPlacement.matched next cur

/-- The own properties of a plain object; none for another node. -/
def fieldsOf : Obj → List (String × Slot)
  | .object _ fields _ => fields
  | _ => []

/-- The own keys of a plain object, in order. -/
def keysOf (o : Obj) : List String := (fieldsOf o).map Prod.fst

/-- Whether a node holds `k` as an own accessor, whose getter a read of the key runs. -/
def getterAt (o : Obj) (k : String) : Bool :=
  match (fieldsOf o).lookup k with
  | some (.accessor ..) => true
  | _ => false

/-- The getters a read of every own property of a node runs, each key once: its own accessors, in
key order. -/
def getters (o : Obj) : List String := (keysOf o).eraseDups.filter (getterAt o)

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

/-- The pending pairs the depth-first walk pushes for a node aligned with `aligned`: per child, the
object at its key or index of the aligned object. -/
def visitChildren (cur : Graph) (node : Obj) (aligned : Option Nat) : List (Nat × Option Nat) :=
  node.slots.filterMap fun (pos, v) =>
    match v with
    | .ref c => some (c, if pos.property then
        aligned.bind fun p => ((cur.node p).occupant pos).bind Val.refId else none)
    | .prim _ => none

/-- The pending pairs the candidate walk pushes for a node walked with candidate `p`: per child,
the object at its position of `p`. -/
def candidateChildren (cur : Graph) (node : Obj) (p : Nat) : List (Nat × Option Nat) :=
  node.slots.filterMap fun (pos, v) =>
    match v with
    | .ref c => some (c, ((cur.node p).occupant pos).bind Val.refId)
    | .prim _ => none

/-- The depth-first walk of `next`: per pending node the pinning alignment its edge offers. Returns
the nodes in visit order and the alignment of each. -/
def visitStep (cur next : Graph) :
    Nat → List (Nat × Option Nat) → Array Bool → Array (Option Nat) → List Nat →
      List Nat × Array (Option Nat)
  | 0, _, _, first, order => (order.reverse, first)
  | _ + 1, [], _, first, order => (order.reverse, first)
  | fuel + 1, (j, pinning) :: rest, visited, first, order =>
    if visited[j]?.getD true then visitStep cur next fuel rest visited first order
    else
      let aligned := pinning.filter fun p => (cur.node p).kind == (next.node j).kind
      visitStep cur next fuel (visitChildren cur (next.node j) aligned ++ rest)
        (visited.setIfInBounds j true) (first.setIfInBounds j aligned) (j :: order)

/-- The walk over pairs of a next node and the candidate a walked parent offers. -/
def candidateStep (cur next : Graph) :
    Nat → List (Nat × Option Nat) → Array (List Nat) → Array (List Nat)
  | 0, _, candidates => candidates
  | _ + 1, [], candidates => candidates
  | fuel + 1, (j, candidate) :: rest, candidates =>
    -- A path without a candidate parent offers no candidate below.
    match candidate.filter fun p => (cur.node p).kind == (next.node j).kind with
    | none => candidateStep cur next fuel rest candidates
    | some p =>
      if (candidates[j]?.getD []).contains p then candidateStep cur next fuel rest candidates
      else
        candidateStep cur next fuel (candidateChildren cur (next.node j) p ++ rest)
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

/-! ## Reads of `next`

Capture reads `next` in one depth-first walk, as `visitStep` visits it, but keeps an object
already in place as it is instead of visiting it: when an aligned node's property or array element
holds the current object at that position, or an object inside a subtree kept earlier, a second
walk (`keepWalk`) reads that object's subtree in the current graph, and keeps it when the walk
meets neither root. A walk that meets a root has read what it passed and keeps nothing, and the
object is then visited. Every other node `next` reaches is read once when it is visited. A read
of an object runs each of its own getters once; the trace records each run with whose getter it
is and why it ran. These are the reads the getter counts of `current` leave out (`Outcome.gets`). -/

/-- Whose getter a read runs: current object `i`, or next node `j`, which no current object is. -/
inductive Owner where
  | cur (i : Nat)
  | next (j : Nat)
  deriving DecidableEq, Repr

/-- Why a getter runs while `next` is read: capture visits its node (`observe`), a walk keeps its
subtree in place (`keep`), or a walk reads it before it meets a root (`discard`). -/
inductive Reading where
  | observe
  | keep
  | discard
  deriving DecidableEq, Repr

/-- One getter run while `next` is read. -/
abbrev Read := Reading × Owner × String

/-- Whose getters a read of next node `j` runs: the current object it is, if any. -/
def ownerOf (input : Input) (j : Nat) : Owner :=
  match input.same[j]?.bind id with
  | some i => .cur i
  | none => .next j

/-- The walk that keeps a current object in place (`keep` in `capture.ts`): depth first over the
current graph from the objects on `stack`, with an explicit stack on which an object's children are
pushed in slot order, so the last one is walked first. An object of `closure`, which earlier walks
kept, or one this walk read already, is passed by; any other object is read, running each of its
getters. The walk stops at the first object `stop` names, a root. Returns the objects it read when
it met no root, `none` when it met one, and its reads, as `(owner, key)`. -/
def keepWalk (cur : Graph) (stop : Nat → Bool) (closure : List Nat) :
    Nat → List Nat → List Nat → List (Owner × String) →
      Option (List Nat) × List (Owner × String)
  | 0, _, walked, reads => (some walked, reads)
  | _ + 1, [], walked, reads => (some walked, reads)
  | fuel + 1, s :: stack, walked, reads =>
    if closure.contains s || walked.contains s then
      keepWalk cur stop closure fuel stack walked reads
    else if stop s then (none, reads)
    else
      keepWalk cur stop closure fuel ((cur.node s).refs.reverse ++ stack) (s :: walked)
        (reads ++ (getters (cur.node s)).map fun k => (.cur s, k))

/-- The pending children of a node that capture visits aligned with `aligned`: per reference, the
child, the object at its position of the aligned object, and whether the edge may keep the child
in place, which only a property or array element of an aligned node may. Without the last, this is
`visitChildren` (`captureChildren_map`). -/
def captureChildren (cur : Graph) (node : Obj) (aligned : Option Nat) :
    List (Nat × Option Nat × Bool) :=
  node.slots.filterMap fun (pos, v) =>
    match v with
    | .ref c => some (c,
        match aligned with
        | some p =>
          if pos.property then (((cur.node p).occupant pos).bind Val.refId, true) else (none, false)
        | none => (none, false))
    | .prim _ => none

/-- The keep walk capture makes at pending child `j` (`adopt` in `capture.ts`): one when the edge
may keep the child, the child is a current object of a kind that can be kept as it is, and it is
the object at its position or inside a subtree kept earlier (`closure`); otherwise `(none, [])`. -/
def keepAt (input : Input) (stop : Nat → Bool) (closure : List Nat) (j : Nat)
    (occupant : Option Nat) (keeps : Bool) : Option (List Nat) × List (Owner × String) :=
  match input.same[j]?.bind id with
  | some i =>
    if keeps && keepable (input.next.node j).kind && (occupant == some i || closure.contains i) then
      keepWalk input.cur stop closure input.cur.budget [i] [] []
    else (none, [])
  | none => (none, [])

/-- Capture's walk of `next` (`AlignedCapture` in `capture.ts`) and its reads. A pending child is
visited unless capture met it already (`known`). A keep walk at it (`keepAt`) that meets no root
keeps the child, adds what it read to `closure` and visits nothing below it; a walk that meets a
root is discarded. A child not kept is visited: read once, aligned with the object at its position
when that has its kind, and its children pushed. Returns the closure and the reads, in order. -/
def captureStep (input : Input) (stop : Nat → Bool) :
    Nat → List (Nat × Option Nat × Bool) → Array Bool → List Nat → List Read →
      List Nat × List Read
  | 0, _, _, closure, reads => (closure, reads)
  | _ + 1, [], _, closure, reads => (closure, reads)
  | fuel + 1, (j, occupant, keeps) :: rest, known, closure, reads =>
    if known[j]?.getD true then captureStep input stop fuel rest known closure reads
    else
      match keepAt input stop closure j occupant keeps with
      | (some walked, walkReads) =>
        captureStep input stop fuel rest (known.setIfInBounds j true) (walked ++ closure)
          (reads ++ walkReads.map fun e => (.keep, e))
      | (none, walkReads) =>
        let node := input.next.node j
        let aligned := occupant.filter fun p => (input.cur.node p).kind == node.kind
        captureStep input stop fuel (captureChildren input.cur node aligned ++ rest)
          (known.setIfInBounds j true) closure
          (reads ++ walkReads.map (fun e => (.discard, e)) ++
            (getters node).map fun k => (.observe, ownerOf input j, k))

/-- The roots a keep walk stops at: the current root, and the current object `next`'s root `r`
is, if any. -/
def rootStop (input : Input) (r : Nat) (s : Nat) : Bool :=
  input.cur.root.refId == some s || (input.same[r]?.bind id) == some s

/-- The getter runs of reading `next`, whose root is node `r`, in order. -/
def captureReads (input : Input) (r : Nat) : List Read :=
  (captureStep input (rootStop input r) input.next.budget [(r, input.cur.root.refId, false)]
    (Array.replicate input.next.nodes.size false) [] []).2

/-- Per owner and key, how many reads run its getter. -/
def readCounts (reads : List Read) : List (Owner × String × Nat) :=
  let runs := reads.map Prod.snd
  runs.eraseDups.map fun (o, k) => (o, k, runs.count (o, k))

/-- The read counts of current objects, by current index. -/
def curCounts (reads : List Read) : List (Nat × String × Nat) :=
  (readCounts reads).filterMap fun
    | (.cur i, k, n) => some (i, k, n)
    | (.next _, _, _) => none

/-- The read counts of the objects only `next` holds, by next index. -/
def freshCounts (reads : List Read) : List (Nat × String × Nat) :=
  (readCounts reads).filterMap fun
    | (.next j, k, n) => some (j, k, n)
    | (.cur _, _, _) => none

/-! ## Decide -/

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

/-- The requirements next node `c` keeping current object `x` makes: that the node at each fixed
slot of `x` holding an object keeps that object. -/
def fixedRequirements (input : Input) (c x : Nat) : List Requirement :=
  (fixedPairs (input.cur.node x) (input.next.node c)).filterMap fun
    | (.ref x', .ref c') => some (c', x')
    | _ => none

/-- The objects next node `c` can keep: at the root `current` itself, as every pass decides
(`passCandidates`), since a cycle back to the root offers it no other; elsewhere its candidates. -/
def keptCandidates (input : Input) (al : Discovery) (c : Nat) : List Nat :=
  if input.next.root.refId = some c then input.cur.root.refId.toList
  else al.candidates[c]?.getD []

/-- The requirements the admitted candidates of every node make (`fixedRequirements`), among the
objects each node can keep (`keptCandidates`). A candidate whose fixed slots require two objects at
one node, or another object at a pinned node, is not admitted, and a demand that would have the
candidate's own node keep another object is left out: the candidate could never be kept with them,
so they must not reorder a node. -/
def demands (input : Input) (al : Discovery) : List Requirement :=
  (List.range input.next.nodes.size).flatMap fun c =>
    (keptCandidates input al c).flatMap fun x =>
      if admitted input al.pinned c x then
        (fixedRequirements input c x).filter fun (c', x') => c' != c || x' == x
      else []

/-- The candidates of next node `j` in decision order: those some admitted candidate requires
there first, then the rest, each in discovery order. Keeping what a fixed slot holds lets the
decision keep the slot's owner too. -/
def orderedCandidates (input : Input) (al : Discovery) (j : Nat) : List Nat :=
  let found := al.candidates[j]?.getD []
  let wanted := (demands input al).filterMap fun (c, x) => if c = j then some x else none
  found.filter wanted.contains ++ found.filter (fun x => !wanted.contains x)

/-- The candidates of next node `j` in a pass's decision order. The root's only candidate is
`current` itself; a cycle back to the root offers no other. Another node's are its ordered
candidates, the object an earlier pass wrote there (`written`) first. -/
def passCandidates (input : Input) (al : Discovery) (written : List Requirement) (j : Nat) :
    List Nat :=
  if input.next.root.refId = some j then input.cur.root.refId.toList
  else
    let found := orderedCandidates input al j
    match written.lookup j with
    | some y => if found.contains y then y :: found.filter (· != y) else found
    | none => found

/-- The object next node `j` keeps when it is pinned: the object it is. -/
def pinnedObject (input : Input) (pin : Array Bool) (j : Nat) : Option Nat :=
  if pin[j]?.getD false then input.same[j]?.bind id else none

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
  let candidatesOf := passCandidates input al written
  let start : Decision :=
    { kept := (Array.range n).map (pinnedObject input pin),
      used := (List.range n).filterMap (pinnedObject input pin) ++ written.map Prod.snd,
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

/-- The attributes of a slot; an accessor, which has no `writable` attribute, counts as
writable. -/
def attrsOf : Slot → Attrs
  | .data _ a => a
  | .accessor _ _ e c => ⟨true, e, c⟩

/-- A kept object with `next`'s contents: keys in `next`'s order; a key in the retained prefix
keeps its own slot with the new value, a moved key, deleted and added again, keeps its attributes
as a data property, an added key is writable and configurable with `next`'s enumerability;
prototype and extensibility stay. -/
def keptObject (proto : Proto) (cFields : List (String × Slot)) (extensible : Bool)
    (nFields : List (String × Slot)) : Obj :=
  let retained := retainPrefix (cFields.map Prod.fst) (nFields.map Prod.fst)
  .object proto (nFields.map fun (k, ns) =>
    (k, match cFields.lookup k with
      | some cs => if retained.contains k then slotWith cs ns.value else .data ns.value (attrsOf cs)
      | none => .data ns.value (.copied ns.enumerable))) extensible

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

/-- A slot of a kept array that a write names: its length or an index. -/
inductive ArraySlot where
  | length
  | index (i : Nat)
  deriving DecidableEq, Repr

/-- The key a write to an array slot reports. -/
def ArraySlot.label : ArraySlot → String
  | .length => "length"
  | .index i => toString i

/-- The writes a kept array needs, by slot: a set at an index where `next` has an element that the
array lacks or holds differently, a deletion where `next` has a hole below its length and the
array an element, and the length when it differs. -/
def arraySlotWrites (identity : Nat → Option Nat) (ce ne : List (Option Val)) :
    List (ArraySlot × String) :=
  let length := if ce.length = ne.length then [] else [(ArraySlot.length, "set")]
  let indices := (List.range (max ce.length ne.length)).filterMap fun i =>
    match ce[i]?.bind id, ne[i]?.bind id with
    | some cv, some nv => if differs identity cv nv then some (.index i, "set") else none
    | none, some _ => some (.index i, "set")
    | some _, none => if i < ne.length then some (.index i, "delete") else none
    | none, none => none
  length ++ indices

/-- The writes a kept array needs, by the key each one reports. -/
def arrayWrites (identity : Nat → Option Nat) (ce ne : List (Option Val)) :
    List (String × String) :=
  (arraySlotWrites identity ce ne).map fun (s, w) => (s.label, w)

/-- The current key a key of `next` stands for: a primitive stands for itself and a node for the
object it keeps; a fresh node's object is no current key. -/
def resolveKey (identity : Nat → Option Nat) : Val → Option Val
  | .prim p => some (.prim p)
  | .ref c => (identity c).map Val.ref

/-- A key that a write to a kept map or set names: a current key, or a key of `next` that is a
fresh node, by its value in `next`. -/
inductive EntryKey where
  | current (k : Val)
  | fresh (k : Val)
  deriving DecidableEq, Repr

/-- The text a write reports for a map or set key. Distinct keys can share a text: the string
`"ref 3"` and a reference to node 3 both read `ref 3`, so theorems use `EntryKey`. -/
def keyLabel : Val → String
  | .prim .undef => "undefined"
  | .prim .null => "null"
  | .prim (.bool b) => toString b
  | .prim (.num n) => toString n
  | .prim (.str t) => t
  | .prim (.atom id) => s!"atom {id}"
  | .ref id => s!"ref {id}"

/-- The text a write reports for a key. -/
def EntryKey.label : EntryKey → String
  | .current k => keyLabel k
  | .fresh k => keyLabel k

/-- The writes a kept map or set needs under the retained prefix of its entries, by key. A key of
`next` that is a node stands for the object that node keeps (`resolveKey`). -/
def entryWrites (identity : Nat → Option Nat) (cKeys nKeys : List Val)
    (cValue nValue : Val → Option Val) : List (EntryKey × String) :=
  let resolved := nKeys.map (resolveKey identity)
  let retained := retainPrefix (cKeys.map some) resolved
  let deletes := cKeys.filterMap fun k =>
    if resolved.contains (some k) && retained.contains (some k) then none
    else some (EntryKey.current k, "delete")
  let sets := nKeys.filterMap fun k =>
    match resolveKey identity k with
    | some ck =>
      if retained.contains (some ck) then
        match cValue ck, nValue k with
        | some cv, some nv =>
          if differs identity cv nv then some (EntryKey.current ck, "set") else none
        | _, _ => none
      else some (EntryKey.current ck, "set")
    | none => some (EntryKey.fresh k, "set")
  deletes ++ sets

/-- The writes a kept map or set needs, by the text each one reports. -/
def collectionWrites (identity : Nat → Option Nat) (cKeys nKeys : List Val)
    (cValue nValue : Val → Option Val) : List (String × String) :=
  (entryWrites identity cKeys nKeys cValue nValue).map fun (k, w) => (k.label, w)

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

/-! ### Keeping `next` unchanged

A pass writes only into the objects its decision keeps and into new objects. It must write into no
object `next` holds, so before any write of a pass its decision is checked from the decision,
`same` and the references of `next` alone, without reading an object. -/

/-- The current objects `next` holds: those that are next nodes its root reaches, as capture
records them. -/
def heldObjects (input : Input) : List Nat :=
  match input.next.root with
  | .ref r => (reach input.next r).filterMap fun j => input.same[j]?.bind id
  | .prim _ => []

/-- Whether `next` holds current object `x` (`heldObjects`). -/
def nextHolds (input : Input) (x : Nat) : Bool := (heldObjects input).contains x

/-- Whether a decision keeps next node `j` *untouched*: it keeps there the current object the node
is, so the result holds `next`'s own object at that node. -/
def untouched (input : Input) (kept : Array (Option Nat)) (j : Nat) : Bool :=
  match input.same[j]?.bind id with
  | some c => kept[j]?.bind id == some c
  | none => false

/-- The check at node `j`: a node that keeps an object `next` holds keeps the object it is, and
every node an untouched node refers to is untouched. -/
def keepsNextAt (input : Input) (kept : Array (Option Nat)) (j : Nat) : Bool :=
  match kept[j]?.bind id with
  | none => true
  | some x =>
    if untouched input kept j then (input.next.node j).refs.all (untouched input kept)
    else !nextHolds input x

/-- Whether a decision keeps `next` unchanged (`keepsNextAt` at every node): publishing it writes
into no object `next` holds. One pass over the nodes, which reads the references of the untouched
ones; those are the nodes publication then skips. -/
def keepsNext (input : Input) (kept : Array (Option Nat)) : Bool :=
  (List.range input.next.nodes.size).all (keepsNextAt input kept)

/-- Whether a pass leaves node `j` alone: it is pinned, or the decision keeps it untouched. Neither
is published or read back. -/
def skipped (input : Input) (pin : Array Bool) (kept : Array (Option Nat)) (j : Nat) : Bool :=
  pin[j]?.getD false || untouched input kept j

/-- The objects kept at published nodes whose writes block. -/
def blockedObjects (input : Input) (pin : Array Bool) (kept : Array (Option Nat)) : List Nat :=
  (List.range input.next.nodes.size).filterMap fun j =>
    if skipped input pin kept j then none
    else match kept[j]?.bind id with
      | some i =>
        if (writesOf (identityOf kept) (input.cur.node i) (input.next.node j)).2 then some i
        else none
      | none => none

/-- The objects a decision keeps at unpinned nodes, with their nodes: a later pass keeps each at
its node or nowhere. -/
def writtenPairs (input : Input) (pin : Array Bool) (kept : Array (Option Nat)) :
    List Requirement :=
  (List.range input.next.nodes.size).filterMap fun j =>
    if pin[j]?.getD false then none
    else (kept[j]?.bind id).map fun i => (j, i)

/-- Decides, and while the decision keeps the root `r`, keeps `next` unchanged and a kept object's
writes block, forbids those objects and decides again with the written objects at their nodes:
the decision of each pass in order, the last one final. As `publishGraph` does, the passes stop at
the first decision that keeps no root or would change `next`. Each pass that continues forbids an
object no earlier pass forbade (`blocked_fresh`), so the passes number at most one more than the
current objects whatever the budget (`demote_length_le`). -/
def demote (input : Input) (al : Discovery) (pin : Array Bool) (r : Nat) :
    Nat → List Nat → List Requirement → List (Array (Option Nat))
  | 0, forbidden, written => [decide input al pin forbidden written]
  | fuel + 1, forbidden, written =>
    let kept := decide input al pin forbidden written
    let blocked := blockedObjects input pin kept
    if (kept[r]?.bind id).isNone || !keepsNext input kept || blocked.isEmpty then [kept]
    else
      kept :: demote input al pin r fuel (forbidden ++ blocked)
        (written ++ writtenPairs input pin kept)

/-- The decisions of a call's passes when `next`'s root is node `r`. The budget, one demotion per
current object, never cuts the passes short (`demote_last_unblocked`). -/
def rounds (input : Input) (al : Discovery) (r : Nat) : List (Array (Option Nat)) :=
  demote input al al.pinned r input.cur.nodes.size [] []

/-! ## Outcome -/

/-- The result of the reference: whether the call succeeds, and per next node the current object
kept there and the contents; `root` is the result's root. The trace fields count observations:
`gets`, `nextGets` and `freshGets` per object and key, `allWrites` per kept current object. -/
structure Outcome where
  ok : Bool
  origins : Array (Option Nat)
  nodes : Array Obj
  root : Val
  /-- The number of decision passes: one, plus one per demotion; none when the first decision
  keeps no root or would change `next`, which rejects the call before any write. -/
  passes : Nat
  /-- Whether the call is rejected because its last decision would change `next`
  (`keepsNext`): it keeps the root but keeps an object `next` holds at another node, or leaves a
  node below an untouched node not untouched. Earlier passes wrote into no object `next` holds. -/
  changesNext : Bool := false
  /-- The getter runs of current objects read as `current`, per current object and key: the reads
  that compare them with `next` and each pass's readback. -/
  gets : List (Nat × String × Nat)
  /-- The getter runs of current objects read as part of `next` (`captureReads`), per current
  object and key: the objects `next` holds, the subtrees kept in place among them. -/
  nextGets : List (Nat × String × Nat) := []
  /-- The getter runs of the objects only `next` holds, per next node and key. -/
  freshGets : List (Nat × String × Nat) := []
  /-- The writes of every pass, as `(current object, key, kind)`, without duplicates: a pass writes
  what its decision needs, and a later pass writes a slot again when its decision keeps another
  object there. -/
  allWrites : List (Nat × String × String)
  deriving Lean.ToJson, Repr

/-- Whether current object `i` holds `k` as an accessor, whose getter a read of the key runs. -/
def accessorKey (input : Input) (i : Nat) (k : String) : Bool := getterAt (input.cur.node i) k

/-- Whether next node `j` is current object `i` itself, which `next` reads as its own. -/
def isOwn (input : Input) (j i : Nat) : Bool := input.same[j]?.bind id == some i

/-- The current objects the read phase reads as `current` at next node `j`: its candidates, and at
a pinned node, which has none, the object capture aligned it with before a walk found the node
inside a subtree kept in place. Never the object the node is (`isOwn`): reading `next` read that
very object, and what it read there serves as its slots. -/
def readAt (input : Input) (al : Discovery) (j : Nat) : List Nat :=
  (if al.pinned[j]?.getD false then (al.first[j]?.bind id).toList
    else al.candidates[j]?.getD []).filter fun i => !isOwn input j i

/-- The getters the read phase runs: each accessor of an object read at a next node (`readAt`), at a
key of that node, once per current object and key however many nodes read it. -/
def capturedKeys (input : Input) (al : Discovery) : List (Nat × String) :=
  ((List.range input.next.nodes.size).flatMap fun j =>
    (readAt input al j).flatMap fun i =>
      (keysOf (input.next.node j)).filterMap fun k =>
        if accessorKey input i k then some (i, k) else none).eraseDups

/-- The getters a pass's readback runs after its writes: each accessor of each current object the
pass keeps at a published node, at a key of the next node kept as it, once per object and key. A
write anywhere can change any kept object, so every published kept object is read back; a pinned
or untouched node is `next`'s own object and is not. -/
def readbackKeys (input : Input) (pin : Array Bool) (kept : Array (Option Nat)) :
    List (Nat × String) :=
  ((List.range input.next.nodes.size).flatMap fun j =>
    if skipped input pin kept j then []
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

/-- The writes of a decision: per kept node that is published, neither pinned nor untouched, the
writes its object needs. -/
def writesOfDecision (input : Input) (pin : Array Bool) (kept : Array (Option Nat)) :
    List (Nat × String × String) :=
  (List.range input.next.nodes.size).flatMap fun j =>
    match kept[j]?.bind id with
    | some i =>
      if skipped input pin kept j then []
      else (writesOf (identityOf kept) (input.cur.node i) (input.next.node j)).1.map
        fun (k, w) => (i, k, w)
    | none => []

/-- The result of a successful final decision `kept` after the passes `rounds`: per next node the
kept object's contents or a fresh copy, the writes and the getter counts. A call whose passes write
nothing reads nothing back; otherwise each pass reads back the objects its decision keeps at
published nodes. -/
def publish (input : Input) (al : Discovery) (pin : Array Bool)
    (rounds : List (Array (Option Nat))) (kept : Array (Option Nat)) (r : Nat) : Outcome :=
  let n := input.next.nodes.size
  let nodes := (Array.range n).map fun j =>
    match kept[j]?.bind id with
    | some i => if skipped input pin kept j then input.next.node j
      else keptObj (input.cur.node i) (input.next.node j)
    | none => (input.next.node j).copy
  let allWrites := (rounds.map (writesOfDecision input pin)).flatten.eraseDups
  let readbacks := if allWrites.isEmpty then [] else rounds.map (readbackKeys input pin)
  { ok := true, origins := kept, nodes, root := .ref r, passes := rounds.length,
    gets := getCounts (capturedKeys input al) readbacks, allWrites }

/-- The input with every array's extensibility as observed. -/
def normalized (raw : Input) : Input :=
  { raw with cur := raw.cur.normalize, next := raw.next.normalize }

/-- Runs the reference. -/
def run (raw : Input) : Outcome :=
  let input := normalized raw
  let n := input.next.nodes.size
  let asIs : Outcome :=
    { ok := true, origins := (Array.range n).map fun j => input.same[j]?.bind id,
      nodes := input.next.nodes, root := input.next.root, passes := 0, gets := [],
      allWrites := [] }
  let rejected (passes : Nat) (changesNext : Bool) : Outcome :=
    { ok := false, origins := #[], nodes := #[], root := .prim .undef, passes, changesNext,
      gets := [], allWrites := [] }
  match input.cur.root, input.next.root with
  | .ref _, .ref r =>
    -- `next` is read in full before any decision, whether the call succeeds or not.
    let reads := captureReads input r
    let withReads (o : Outcome) : Outcome :=
      { o with nextGets := curCounts reads, freshGets := freshCounts reads }
    let al := discover input
    let passes := rounds input al r
    let final := passes.getLastD #[]
    let count := if passes.length = 1 then 0 else passes.length
    -- A root the first decision cannot keep, or a first decision that would change `next`,
    -- rejects the call before any write; a root a write blocked, or a later decision that would
    -- change `next`, after the passes before it.
    withReads (if (final[r]?.bind id).isNone then rejected count false
    else if !keepsNext input final then rejected count true
    else publish input al al.pinned passes final r)
  | _, _ => asIs

end Reconcile.Spec.Reconcile
