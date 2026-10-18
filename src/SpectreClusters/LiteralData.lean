module

public import SpectreClusters.KiteGrid

@[expose] public section


/-! Literal mathematical data from Smith, Myers, Kaplan, Goodman-Strauss,
arXiv:2305.17743v2, 00_macros.tex (CC BY 4.0). rawtileA is the 8-kite
hat and rawtileB the 10-kite turtle in Section 3 of the Spectre paper.
These are NOT the original Hat paper's parameter-naming convention.
The common hcoords(0,0)=(2,0) vertex-coordinate translation is removed.
Source hashes and an original extraction are in cluster_bridge_20261013. -/
namespace SpectreClusters

inductive HTKind | hat | turtle deriving DecidableEq, Repr

def htCells : HTKind → List Cell
  | .hat => [⟨(0,0),0⟩,⟨(0,0),3⟩,⟨(0,0),4⟩,⟨(0,0),5⟩,⟨(1,-1),0⟩,⟨(1,-1),1⟩,⟨(1,0),2⟩,⟨(1,0),3⟩]
  | .turtle => [⟨(0,-1),0⟩,⟨(0,-1),1⟩,⟨(0,0),0⟩,⟨(0,0),3⟩,⟨(0,0),4⟩,⟨(0,0),5⟩,⟨(1,-1),1⟩,⟨(1,-1),2⟩,⟨(1,0),3⟩,⟨(1,0),4⟩]

def htPolygon : HTKind → List Point
  | .hat => [(0,0),(-2,1),(-2,0),(0,-2),(1,-2),(2,-4),(4,-5),(4,-4),(3,-3),(4,-2),(3,0),(2,0),(1,1)]
  | .turtle => [(0,0),(-2,1),(-2,0),(-3,0),(-2,-2),(2,-4),(3,-3),(4,-4),(5,-4),(4,-2),(2,-1),(2,0),(1,1)]

def htRefinedPolygon : HTKind → List Point
  | .hat => [(0,0),(-2,1),(-2,0),(-1,-1),(0,-2),(1,-2),(2,-4),(4,-5),(4,-4),(3,-3),(4,-2),(3,0),(2,0),(1,1)]
  | .turtle => [(0,0),(-2,1),(-2,0),(-3,0),(-2,-2),(0,-3),(2,-4),(3,-3),(4,-4),(5,-4),(4,-2),(2,-1),(2,0),(1,1)]

structure HTPlacement where
  kind : HTKind
  turn : Turn
  center : Point
  deriving DecidableEq, Repr

def placementCells (p : HTPlacement) : List Cell :=
  (htCells p.kind).map (moveCell p.turn p.center)

inductive ClusterKind | t6h | t7h | t8h deriving DecidableEq, Repr

def clusterPieces : ClusterKind → List HTPlacement
  | .t6h => [⟨.turtle,0,(0,0)⟩,⟨.hat,2,(1,0)⟩,⟨.hat,3,(0,1)⟩,⟨.hat,1,(-1,0)⟩,⟨.hat,5,(0,-1)⟩,⟨.hat,0,(1,-1)⟩,⟨.hat,1,(2,-1)⟩]
  | .t7h => [⟨.turtle,0,(0,0)⟩,⟨.hat,2,(1,0)⟩,⟨.hat,3,(0,1)⟩,⟨.hat,1,(-1,0)⟩,⟨.hat,5,(0,-1)⟩,⟨.hat,0,(1,-1)⟩,⟨.hat,0,(1,-2)⟩,⟨.hat,1,(2,-1)⟩]
  | .t8h => [⟨.turtle,0,(0,0)⟩,⟨.hat,2,(1,0)⟩,⟨.hat,3,(0,1)⟩,⟨.hat,1,(-1,0)⟩,⟨.hat,5,(0,-1)⟩,⟨.hat,0,(1,-1)⟩,⟨.hat,0,(1,-2)⟩,⟨.hat,1,(2,-1)⟩,⟨.hat,2,(2,0)⟩]

def clusterCells (k : ClusterKind) : List Cell :=
  (clusterPieces k).flatMap placementCells

def clusterPolygon : ClusterKind → List Point
  | .t6h => [(-5,1),(-4,0),(-4,-1),(-4,-2),(-3,-3),(-4,-4),(-3,-6),(-2,-6),(-2,-5),(0,-6),(1,-5),(2,-6),(3,-6),(4,-8),(6,-9),(6,-8),(7,-8),(8,-8),(8,-7),(10,-8),(11,-7),(10,-6),(9,-6),(8,-4),(6,-3),(6,-2),(5,-1),(6,0),(5,2),(4,2),(3,3),(2,4),(1,4),(0,6),(-2,7),(-2,6),(-1,5),(-2,4),(-4,5),(-4,4),(-5,4),(-4,2)]
  | .t7h => [(-5,1),(-4,0),(-4,-1),(-4,-2),(-3,-3),(-4,-4),(-3,-6),(-2,-6),(-1,-7),(0,-8),(1,-8),(2,-10),(4,-11),(4,-10),(3,-9),(4,-8),(6,-9),(6,-8),(7,-8),(8,-8),(8,-7),(10,-8),(11,-7),(10,-6),(9,-6),(8,-4),(6,-3),(6,-2),(5,-1),(6,0),(5,2),(4,2),(3,3),(2,4),(1,4),(0,6),(-2,7),(-2,6),(-1,5),(-2,4),(-4,5),(-4,4),(-5,4),(-4,2)]
  | .t8h => [(-5,1),(-4,0),(-4,-1),(-4,-2),(-3,-3),(-4,-4),(-3,-6),(-2,-6),(-1,-7),(0,-8),(1,-8),(2,-10),(4,-11),(4,-10),(3,-9),(4,-8),(6,-9),(6,-8),(7,-8),(8,-8),(8,-7),(10,-8),(11,-7),(10,-6),(10,-5),(10,-4),(9,-3),(10,-2),(9,0),(8,0),(8,-1),(6,0),(5,2),(4,2),(3,3),(2,4),(1,4),(0,6),(-2,7),(-2,6),(-1,5),(-2,4),(-4,5),(-4,4),(-5,4),(-4,2)]

end SpectreClusters
