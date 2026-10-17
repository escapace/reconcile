import Serialization.Codec

namespace SerializationLab

-- Extends the node-rooted table model without changing its row/reference representation.
structure RootGraph (n : Nat) where
  root : Token (Fin n)
  nodes : Fin n → Node (Fin n)

structure RootWire where
  root : Token Nat
  rows : List (Node Nat)

def encodeRootGraph {n : Nat} (g : RootGraph n) : RootWire :=
  ⟨encodeToken g.root, List.ofFn fun i => encodeNode (g.nodes i)⟩

def decodeRootToken (n : Nat) (w : RootWire) : Option (Token (Fin n)) :=
  decodeToken n w.root

def decodeRootRow (n : Nat) (w : RootWire) (i : Fin n) : Option (Node (Fin n)) :=
  w.rows[i.val]?.bind (decodeNode n)

theorem rootGraph_size {n : Nat} (g : RootGraph n) :
    (encodeRootGraph g).rows.length = n := by
  simp [encodeRootGraph]

theorem rootToken_roundtrip {n : Nat} (g : RootGraph n) :
    decodeRootToken n (encodeRootGraph g) = some g.root := by
  simp [decodeRootToken, encodeRootGraph]

theorem rootRow_roundtrip {n : Nat} (g : RootGraph n) (i : Fin n) :
    decodeRootRow n (encodeRootGraph g) i = some (g.nodes i) := by
  simp [decodeRootRow, encodeRootGraph, i.isLt]

theorem rootGraph_roundtrip {n : Nat} (g : RootGraph n) :
    decodeRootToken n (encodeRootGraph g) = some g.root ∧
      ∀ i, decodeRootRow n (encodeRootGraph g) i = some (g.nodes i) :=
  ⟨rootToken_roundtrip g, rootRow_roundtrip g⟩

def primitiveGraph (atom : String) : RootGraph 0 :=
  ⟨.atom atom, fun i => Fin.elim0 i⟩

theorem primitive_empty_table (atom : String) :
    (encodeRootGraph (primitiveGraph atom)).rows = [] := by
  simp [encodeRootGraph, primitiveGraph]

theorem primitive_roundtrip (atom : String) :
    decodeRootToken 0 (encodeRootGraph (primitiveGraph atom)) = some (.atom atom) :=
  rootToken_roundtrip _

theorem zero_node_reference_rejected (i : Nat) :
    decodeToken 0 (.ref i) = none := by
  simp [decodeToken, decodeRef]

#print axioms rootGraph_size
#print axioms rootToken_roundtrip
#print axioms rootRow_roundtrip
#print axioms rootGraph_roundtrip
#print axioms primitive_empty_table
#print axioms primitive_roundtrip
#print axioms zero_node_reference_rejected

end SerializationLab
