module

public import SpectreGeometry.ReversePhysicalClusterData

@[expose] public section


/-! Finite physical path data. The P poses are orientation-preserving; the
map from the literal raw H/T coordinates uses the one common reflection. -/
namespace SpectreGeometry.ReversePhysicalCluster
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
open SpectreClusters SpectreClusters.ReverseExistence Deformation
open SpectreFinite SpectreFinite.HexSearch

def physicalRootTurn (r : Fin 6) : Fin 12 :=
  ⟨(12-2*r.val)%12,Nat.mod_lt _ (by decide)⟩
def halfExactPoint (p : ExactPoint) : ExactPoint :=
  ((p.1.1/2,p.1.2/2),(p.2.1/2,p.2.2/2))
def physicalRotate4 (r : Fin 6) (p : ExactPoint) : ExactPoint :=
  halfExactPoint (complexMulExact (SpectreGeometry.direction (physicalRootTurn r)) p)
def physicalPath4 (k : Fin 9) (d : Fin 6) : List ExactPoint :=
  ((markedPaths k).getD d.val []).map (vertexImage4 (k.val != 0))
def physicalCorner4 (k : Fin 9) (d : Fin 6) : ExactPoint :=
  vertexImage4 (k.val != 0) (corner k d)
def physicalStatePath4 (a : State) (d : Fin 6) : List ExactPoint :=
  (physicalPath4 a.1 (sideTurn a.2 d)).map (physicalRotate4 a.2)
def physicalStateCorner4 (a : State) (d : Fin 6) : ExactPoint :=
  physicalRotate4 a.2 (physicalCorner4 a.1 (sideTurn a.2 d))
def physicalDelta4 (a b : State) (d : Fin 6) : ExactPoint :=
  ExactPoint.sub (physicalStateCorner4 a d) (physicalStateCorner4 b (rotateTurn 4 d))

def PhysicalBoundaryCertificate (k : Fin 9) : Prop :=
  ∀ (r : Fin 6) (j : Fin 9) (t : Fin 6) (d : Fin 6), sideMatch (k,r) (j,t) d →
    physicalDelta4 (k,r) (j,t) d =
      ExactPoint.sub (physicalStateCorner4 (k,r) (rotateTurn 1 d))
        (physicalStateCorner4 (j,t) (opposite d)) ∧
    physicalStatePath4 (k,r) d =
      ((physicalStatePath4 (j,t) (opposite d)).reverse).map
        (ExactPoint.add (physicalDelta4 (k,r) (j,t) d))

end SpectreGeometry.ReversePhysicalCluster
