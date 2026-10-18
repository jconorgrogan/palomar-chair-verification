module

public import SpectreGeometry.ReverseLocalStarOccurrenceBaseData
public import SpectreGeometry.ReverseLocalStarOccurrenceTable0
public import SpectreGeometry.ReverseLocalStarOccurrenceTable1
public import SpectreGeometry.ReverseLocalStarOccurrenceTable2
public import SpectreGeometry.ReverseLocalStarOccurrenceTable3
public import SpectreGeometry.ReverseLocalStarOccurrenceTable4
public import SpectreGeometry.ReverseLocalStarOccurrenceTable5
public import SpectreGeometry.ReverseLocalStarOccurrenceTable6
public import SpectreGeometry.ReverseLocalStarOccurrenceTable7
public import SpectreGeometry.ReverseLocalStarOccurrenceTable8

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
open SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch
open ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def sideRowsTable : List (List (List (List Nat))) := [sideRows0,sideRows1,sideRows2,sideRows3,sideRows4,sideRows5,sideRows6,sideRows7,sideRows8]
def tripleRowsTable : List (List (List (List Nat))) := [tripleRows0,tripleRows1,tripleRows2,tripleRows3,tripleRows4,tripleRows5,tripleRows6,tripleRows7,tripleRows8]

def incidentIds (k : Fin 9) (v : Nat) : List Nat :=
  (if k.val=0 then incidentRows0 else incidentRows1).getD v []
def localStar (a : State) (v : Nat) : List (List Point) :=
  (incidentIds a.1 v).map (fun i =>
    (triangleVertexList (targetVertices a.1) ((meshTriangles a.1).getD i (0,0,0))).map
      (fun p => SpectreClusters.rotate a.2 (SpectreClusters.sub p (targetVertex a.1 v))))
def pointLE (p q : Point) : Bool := decide (p.1<q.1 ∨ (p.1=q.1 ∧ p.2≤q.2))
def triangleLE (p q : List Point) : Bool :=
  let a := p.getD 0 (0,0); let b := q.getD 0 (0,0)
  let c := p.getD 1 (0,0); let d := q.getD 1 (0,0)
  pointLE a b && (!(pointLE b a) || (pointLE c d &&
    (!(pointLE d c) || pointLE (p.getD 2 (0,0)) (q.getD 2 (0,0)))))
def normalized (ts : List (List Point)) : List (List Point) :=
  (ts.map (fun t => t.mergeSort pointLE)).mergeSort triangleLE

def occurrenceCheckB (ts : List (List Point)) (code : Nat) : Bool :=
  decide (code<744) &&
    (normalized (ts.map (fun t => t.map (SpectreClusters.rotate ⟨code%6,Nat.mod_lt _ (by decide)⟩))) ==
      normalized (canonicalStars.getD (code/6) []))
def sideCode (a b : State) (d : Fin 6) (j : Nat) : Nat :=
  let rows := (sideRowsTable.getD a.1.val []).getD a.2.val []
  ((rows.find? (fun row => row.take 4 == [b.1.val,b.2.val,d.val,j])).getD []).getD 4 744
def tripleCode (a b c : State) (d : Fin 6) : Nat :=
  let rows := (tripleRowsTable.getD a.1.val []).getD a.2.val []
  ((rows.find? (fun row => row.take 5 == [b.1.val,b.2.val,c.1.val,c.2.val,d.val])).getD []).getD 5 744

def stateBoundaryIds (a : State) (d : Fin 6) : List Nat := boundaryIndices a.1 (sideTurn a.2 d)
def sideOccurrenceB (a b : State) (d : Fin 6) (j : Nat) : Bool :=
  let ids := stateBoundaryIds a d
  let ids' := stateBoundaryIds b (opposite d)
  occurrenceCheckB (localStar a (ids.getD j 0) ++ localStar b (ids'.getD (ids'.length-1-j) 0))
    (sideCode a b d j)
def tripleOccurrenceB (a b c : State) (d : Fin 6) : Bool :=
  occurrenceCheckB (localStar a ((stateBoundaryIds a d).getLastD 0) ++
    localStar b ((stateBoundaryIds b (opposite d)).headD 0) ++
    localStar c ((stateBoundaryIds c (rotateTurn 4 (rotateTurn 1 d))).headD 0))
    (tripleCode a b c d)

def SideCertificate (a : State) : Prop := ∀ (b : State) (d : Fin 6) (j : Fin 12),
  sideMatch a b d → 0<j.val → j.val+1<(stateBoundaryIds a d).length →
    sideOccurrenceB a b d j.val = true
def TripleCertificate (a : State) : Prop := ∀ (b c : State) (d : Fin 6),
  sideMatch a b d → sideMatch a c (rotateTurn 1 d) → sideMatch b c (rotateTurn 2 d) →
    tripleOccurrenceB a b c d = true
end SpectreGeometry.ReverseLocalStarOccurrences
