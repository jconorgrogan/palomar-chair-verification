module

public import SpectreGeometry.ReverseClusterTriangulationData
public import SpectreClusters.ReverseClusterCocycleData

@[expose] public section

namespace SpectreGeometry.ReverseClusterVertexIntersections
open SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch
open ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
structure GeometryCase where
  rootBig : Bool
  neighborBig : Bool
  turn : Fin 6
  shift : Point
  pairs : List (Nat×Nat)

def geometryCase0 : GeometryCase := ⟨false,false,2,(-12,0),[(0,10),(1,9),(2,8),(3,7),(4,6),(5,5),(42,12),(43,11)]⟩
def geometryCase1 : GeometryCase := ⟨false,false,2,(2,8),[(32,42),(33,41),(34,40),(35,39),(36,38),(37,37)]⟩
def geometryCase2 : GeometryCase := ⟨false,false,4,(0,-12),[(5,5),(6,4),(7,3),(8,2),(9,1),(10,0),(11,43),(12,42)]⟩
def geometryCase3 : GeometryCase := ⟨false,false,4,(-8,10),[(37,37),(38,36),(39,35),(40,34),(41,33),(42,32)]⟩
def geometryCase4 : GeometryCase := ⟨false,true,0,(-14,4),[(0,26),(1,25),(2,24),(3,23),(4,22),(5,21),(42,28),(43,27)]⟩
def geometryCase5 : GeometryCase := ⟨false,true,1,(-12,12),[(37,13),(38,12),(39,11),(40,10),(41,9),(42,8)]⟩
def geometryCase6 : GeometryCase := ⟨false,true,5,(12,-12),[(12,8),(13,7),(14,6),(15,5),(16,4),(17,3),(18,2),(19,1),(20,0),(21,45),(22,44)]⟩
def geometryCase7 : GeometryCase := ⟨false,true,2,(2,8),[(32,44),(33,43),(34,42),(35,41),(36,40),(37,39)]⟩
def geometryCase8 : GeometryCase := ⟨false,true,5,(-10,14),[(37,29),(38,28),(39,27),(40,26),(41,25),(42,24)]⟩
def geometryCase9 : GeometryCase := ⟨false,true,4,(0,-12),[(5,5),(6,4),(7,3),(8,2),(9,1),(10,0),(11,45),(12,44)]⟩
def geometryCase10 : GeometryCase := ⟨false,true,1,(10,-2),[(22,2),(23,1),(24,0),(25,45),(26,44),(27,43),(28,42),(29,41),(30,40),(31,39),(32,38)]⟩
def geometryCase11 : GeometryCase := ⟨true,false,0,(14,-4),[(21,5),(22,4),(23,3),(24,2),(25,1),(26,0),(27,43),(28,42)]⟩
def geometryCase12 : GeometryCase := ⟨true,false,1,(-12,0),[(0,20),(1,19),(2,18),(3,17),(4,16),(5,15),(6,14),(7,13),(8,12),(44,22),(45,21)]⟩
def geometryCase13 : GeometryCase := ⟨true,false,5,(0,-12),[(8,42),(9,41),(10,40),(11,39),(12,38),(13,37)]⟩
def geometryCase14 : GeometryCase := ⟨true,true,1,(2,8),[(28,8),(29,7),(30,6),(31,5),(32,4),(33,3),(34,2),(35,1),(36,0),(37,45),(38,44)]⟩
def geometryCase15 : GeometryCase := ⟨true,true,5,(-10,2),[(0,36),(1,35),(2,34),(3,33),(4,32),(5,31),(6,30),(7,29),(8,28),(44,38),(45,37)]⟩
def geometryCase16 : GeometryCase := ⟨true,true,5,(0,-12),[(8,44),(9,43),(10,42),(11,41),(12,40),(13,39)]⟩
def geometryCase17 : GeometryCase := ⟨true,true,0,(14,-4),[(21,5),(22,4),(23,3),(24,2),(25,1),(26,0),(27,45),(28,44)]⟩
def geometryCase18 : GeometryCase := ⟨true,true,4,(14,-16),[(13,13),(14,12),(15,11),(16,10),(17,9),(18,8),(19,7),(20,6),(21,5)]⟩
def geometryCase19 : GeometryCase := ⟨true,true,2,(-10,8),[(38,8),(39,7),(40,6),(41,5),(42,4),(43,3),(44,2)]⟩
def geometryCase20 : GeometryCase := ⟨true,true,2,(12,-18),[(13,29),(14,28),(15,27),(16,26),(17,25),(18,24),(19,23),(20,22),(21,21)]⟩
def geometryCase21 : GeometryCase := ⟨true,false,1,(14,-4),[(24,42),(25,41),(26,40),(27,39),(28,38),(29,37)]⟩
def geometryCase22 : GeometryCase := ⟨true,false,4,(-8,10),[(39,37),(40,36),(41,35),(42,34),(43,33),(44,32)]⟩
def geometryCase23 : GeometryCase := ⟨true,true,1,(-12,12),[(39,13),(40,12),(41,11),(42,10),(43,9),(44,8)]⟩
def geometryCase24 : GeometryCase := ⟨true,true,1,(14,-4),[(24,44),(25,43),(26,42),(27,41),(28,40),(29,39)]⟩
def geometryCase25 : GeometryCase := ⟨true,true,3,(6,6),[(29,39),(30,38),(31,37),(32,36),(33,35),(34,34),(35,33),(36,32),(37,31),(38,30),(39,29)]⟩
def geometryCase26 : GeometryCase := ⟨true,true,5,(-10,14),[(39,29),(40,28),(41,27),(42,26),(43,25),(44,24)]⟩
def geometryCase27 : GeometryCase := ⟨true,true,1,(10,-14),[(13,39),(14,38),(15,37),(16,36),(17,35),(18,34),(19,33),(20,32),(21,31),(22,30),(23,29),(24,28)]⟩
def geometryCase28 : GeometryCase := ⟨true,true,5,(4,10),[(28,24),(29,23),(30,22),(31,21),(32,20),(33,19),(34,18),(35,17),(36,16),(37,15),(38,14),(39,13)]⟩
def geometryCase29 : GeometryCase := ⟨true,false,2,(-12,0),[(0,10),(1,9),(2,8),(3,7),(4,6),(5,5),(44,12),(45,11)]⟩
def geometryCase30 : GeometryCase := ⟨true,true,0,(-14,4),[(0,26),(1,25),(2,24),(3,23),(4,22),(5,21),(44,28),(45,27)]⟩
def geometryCase31 : GeometryCase := ⟨true,true,2,(-2,-14),[(5,21),(6,20),(7,19),(8,18),(9,17),(10,16),(11,15),(12,14),(13,13)]⟩
def geometryCase32 : GeometryCase := ⟨true,false,5,(-8,10),[(0,24),(1,23),(2,22),(38,32),(39,31),(40,30),(41,29),(42,28),(43,27),(44,26),(45,25)]⟩
def geometryCase33 : GeometryCase := ⟨true,true,4,(-8,-2),[(2,44),(3,43),(4,42),(5,41),(6,40),(7,39),(8,38)]⟩
def geometryCase34 : GeometryCase := ⟨true,true,4,(18,-6),[(21,21),(22,20),(23,19),(24,18),(25,17),(26,16),(27,15),(28,14),(29,13)]⟩
def geometryCases : List GeometryCase := [geometryCase0,geometryCase1,geometryCase2,geometryCase3,geometryCase4,geometryCase5,geometryCase6,geometryCase7,geometryCase8,geometryCase9,geometryCase10,geometryCase11,geometryCase12,geometryCase13,geometryCase14,geometryCase15,geometryCase16,geometryCase17,geometryCase18,geometryCase19,geometryCase20,geometryCase21,geometryCase22,geometryCase23,geometryCase24,geometryCase25,geometryCase26,geometryCase27,geometryCase28,geometryCase29,geometryCase30,geometryCase31,geometryCase32,geometryCase33,geometryCase34]
def geometryCase (k : Fin 35) : GeometryCase := geometryCases.getD k.val geometryCase0
def classRows0 : List (List Nat) := [[0,2,0,0],[0,2,4,1],[0,4,1,2],[0,4,5,3],[1,0,0,4],[1,1,5,5],[1,5,2,6],[2,1,5,5],[2,2,4,7],[2,5,2,6],[2,5,5,8],[3,0,0,4],[3,1,5,5],[3,2,4,7],[3,5,2,6],[4,2,4,7],[4,4,1,9],[4,5,5,8],[5,0,0,4],[5,2,4,7],[5,4,1,9],[6,0,0,4],[6,1,3,10],[6,1,5,5],[7,1,5,5],[7,2,4,7],[7,5,2,6],[8,2,4,7],[8,4,1,9]]
def classRows1 : List (List Nat) := [[0,0,3,11],[0,1,0,12],[0,5,1,13],[1,1,4,14],[1,5,0,15],[2,1,4,14],[2,5,1,16],[3,1,4,14],[3,5,1,16],[4,0,3,17],[4,4,2,18],[4,5,1,16],[5,0,3,17],[5,4,2,18],[5,5,1,16],[6,2,5,19],[6,5,0,15],[7,1,4,14],[7,2,2,20],[7,5,1,16],[8,0,3,17],[8,2,2,20],[8,4,2,18],[8,5,1,16]]
def classRows2 : List (List Nat) := [[0,1,0,12],[0,1,3,21],[0,4,5,22],[0,5,1,13],[1,1,5,23],[1,5,0,15],[2,1,3,24],[2,1,5,23],[2,3,4,25],[2,5,1,16],[2,5,5,26],[3,1,2,27],[3,1,3,24],[3,1,5,23],[3,5,1,16],[4,1,3,24],[4,3,4,25],[4,5,1,16],[4,5,5,26],[5,1,2,27],[5,1,3,24],[5,5,1,16],[6,1,5,23],[6,5,0,15],[7,1,3,24],[7,1,5,23],[7,3,4,25],[7,5,1,16],[8,1,3,24],[8,3,4,25],[8,5,1,16]]
def classRows3 : List (List Nat) := [[0,0,3,11],[0,1,0,12],[0,4,5,22],[0,5,1,13],[1,1,5,23],[1,5,0,15],[2,1,5,23],[2,5,1,16],[2,5,4,28],[2,5,5,26],[3,1,5,23],[3,5,1,16],[4,0,3,17],[4,4,2,18],[4,5,1,16],[4,5,4,28],[4,5,5,26],[5,0,3,17],[5,4,2,18],[5,5,1,16],[6,1,5,23],[6,5,0,15],[7,1,5,23],[7,2,2,20],[7,5,1,16],[8,0,3,17],[8,2,2,20],[8,4,2,18],[8,5,1,16]]
def classRows4 : List (List Nat) := [[0,1,3,21],[0,2,0,29],[0,4,5,22],[1,0,0,30],[1,1,5,23],[1,2,1,31],[2,1,3,24],[2,1,5,23],[2,3,4,25],[2,5,5,26],[3,0,0,30],[3,1,2,27],[3,1,3,24],[3,1,5,23],[3,2,1,31],[4,1,3,24],[4,3,4,25],[4,5,5,26],[5,0,0,30],[5,1,2,27],[5,1,3,24],[5,2,1,31],[6,0,0,30],[6,1,5,23],[6,2,1,31],[7,1,3,24],[7,1,5,23],[7,2,1,31],[7,3,4,25],[8,1,3,24],[8,2,1,31],[8,3,4,25]]
def classRows5 : List (List Nat) := [[0,0,3,11],[0,2,0,29],[0,4,5,22],[1,0,0,30],[1,1,5,23],[1,2,1,31],[2,1,5,23],[2,5,4,28],[2,5,5,26],[3,0,0,30],[3,1,5,23],[3,2,1,31],[4,0,3,17],[4,4,2,18],[4,5,4,28],[4,5,5,26],[5,0,0,30],[5,0,3,17],[5,2,1,31],[5,4,2,18],[6,0,0,30],[6,1,5,23],[6,2,1,31],[7,1,5,23],[7,2,1,31],[7,2,2,20],[8,0,3,17],[8,2,1,31],[8,2,2,20],[8,4,2,18]]
def classRows6 : List (List Nat) := [[0,0,3,11],[0,5,1,13],[0,5,5,32],[1,1,4,14],[1,4,0,33],[2,1,4,14],[2,5,1,16],[3,1,4,14],[3,5,1,16],[4,0,3,17],[4,4,2,18],[4,5,1,16],[5,0,3,17],[5,4,2,18],[5,5,1,16],[7,1,4,14],[7,2,2,20],[7,5,1,16],[8,0,3,17],[8,2,2,20],[8,4,2,18],[8,5,1,16]]
def classRows7 : List (List Nat) := [[0,1,0,12],[0,4,5,22],[0,5,1,13],[1,1,5,23],[1,4,3,34],[1,5,0,15],[2,1,5,23],[2,3,4,25],[2,5,1,16],[2,5,5,26],[3,1,5,23],[3,4,3,34],[3,5,1,16],[4,3,4,25],[4,4,2,18],[4,5,1,16],[4,5,5,26],[5,4,2,18],[5,4,3,34],[5,5,1,16],[6,1,5,23],[6,4,3,34],[6,5,0,15],[7,1,5,23],[7,2,2,20],[7,3,4,25],[7,4,3,34],[7,5,1,16],[8,2,2,20],[8,3,4,25],[8,4,2,18],[8,4,3,34],[8,5,1,16]]
def classRows8 : List (List Nat) := [[0,2,0,29],[0,4,5,22],[1,0,0,30],[1,1,5,23],[1,2,1,31],[1,4,3,34],[2,1,5,23],[2,3,4,25],[2,5,5,26],[3,0,0,30],[3,1,5,23],[3,2,1,31],[3,4,3,34],[4,3,4,25],[4,4,2,18],[4,5,5,26],[5,0,0,30],[5,2,1,31],[5,4,2,18],[5,4,3,34],[6,0,0,30],[6,1,5,23],[6,2,1,31],[6,4,3,34],[7,1,5,23],[7,2,1,31],[7,2,2,20],[7,3,4,25],[7,4,3,34],[8,2,1,31],[8,2,2,20],[8,3,4,25],[8,4,2,18],[8,4,3,34]]
def classRows : List (List (List Nat)) := [classRows0,classRows1,classRows2,classRows3,classRows4,classRows5,classRows6,classRows7,classRows8]
def kindMark (big : Bool) : Fin 9 := if big then 1 else 0
def rootVertices (g : GeometryCase) : List Point := targetVertices (kindMark g.rootBig)
def neighborVertices (g : GeometryCase) : List Point := targetVertices (kindMark g.neighborBig)
def neighborVertex (g : GeometryCase) (j : Nat) : Point :=
  SpectreClusters.add (scalePoint 6 g.shift)
    (SpectreClusters.rotate g.turn ((neighborVertices g).getD j (0,0)))
def CollisionRowCertificate (k : Fin 35) (i : Nat) : Prop := ∀ j : Fin 133,
  i < (rootVertices (geometryCase k)).length → j.val < (neighborVertices (geometryCase k)).length →
    (rootVertices (geometryCase k)).getD i (0,0) = neighborVertex (geometryCase k) j.val →
      (i,j.val) ∈ (geometryCase k).pairs

def classCode (a b : State) (d : Fin 6) : Nat :=
  let rows := classRows.getD a.1.val []
  ((rows.find? (fun row => row.take 3 == [b.1.val,(sideTurn a.2 b.2).val,(sideTurn a.2 d).val])).getD []).getD 3 35

def actualBoundaryPairs (a b : State) (d : Fin 6) : List (Nat×Nat) :=
  let ids := boundaryIndices a.1 (sideTurn a.2 d)
  let ids' := boundaryIndices b.1 (sideTurn b.2 (opposite d))
  (List.range ids.length).map (fun j => (ids.getD j 0,ids'.getD (ids'.length-1-j) 0))

def CaseBindingCertificate (k : Fin 9) : Prop := ∀ (r : Fin 6) (bk : Fin 9) (br d : Fin 6),
  sideMatch (k,r) (bk,br) d →
    classCode (k,r) (bk,br) d < 35 ∧
    let g := geometryCases.getD (classCode (k,r) (bk,br) d) geometryCase0
    g.rootBig = (k.val != 0) ∧ g.neighborBig = (bk.val != 0) ∧
    g.turn = sideTurn r br ∧
    g.shift = SpectreClusters.rotate (inverseTurn r) (vertexDelta (k,r) (bk,br) d) ∧
    g.pairs.all (fun p => decide (p ∈ actualBoundaryPairs (k,r) (bk,br) d)) = true
end SpectreGeometry.ReverseClusterVertexIntersections
