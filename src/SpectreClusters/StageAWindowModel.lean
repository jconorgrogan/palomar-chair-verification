module

public import SpectreClusters.StageABindingCore
public import SpectreClusters.StageAWindowData
public import SpectreClusters.GridMotions

@[expose] public section


namespace SpectreClusters.StageA

def domain (kind : HTKind) : List Cell := htCells kind ++ haloOrder kind

def ownerAt (kind : HTKind) (word : List Nat) (slot : Nat) : HTPlacement :=
  if slot < (htCells kind).length then canonicalRoot kind
  else candidateAt kind (word.getD (slot - (htCells kind).length) 0)

def alignmentValidB (kind : HTKind) (n : Nat) : Bool :=
  let t := candidateAt kind n
  (alignmentPairs kind n).all fun ij =>
    ij.1 < (domain kind).length && ij.2 < (domain t.kind).length &&
    cellEqB ((domain kind).getD ij.1 ⟨(0,0),0⟩)
      (moveCell t.turn t.center ((domain t.kind).getD ij.2 ⟨(0,0),0⟩))

def supportB (kind : HTKind) (word : List Nat) (n : Nat) (support : List Nat) : Bool :=
  let t := candidateAt kind n
  (alignmentPairs kind n).all fun ij =>
    poseEqB (ownerAt kind word ij.1)
      (movePlacement t.turn t.center (ownerAt t.kind support ij.2))

def rawWordAt (kind : HTKind) (i : Nat) : List Nat := (rawWords kind).getD i []

def noSupportB (stage : Nat) (kind : HTKind) (i n : Nat) : Bool :=
  let t := candidateAt kind n
  (keptIds stage t.kind).all fun j => !(supportB kind (rawWordAt kind i) n (rawWordAt t.kind j))

def rejectionCheckB (stage : Nat) (kind : HTKind) (i : Nat) : Bool :=
  let n := rejectionNeighbor stage kind i
  (rawWordAt kind i).contains n && alignmentValidB kind n && noSupportB stage kind i n

end SpectreClusters.StageA
