module

public import SpectreGeometry.ReversePhysicalClusterData

@[expose] public section


/-! Exact binding of the reflected Euclidean raw H/T frame to the already
certified forward deformation's target vertices. -/
namespace SpectreGeometry.ReversePhysicalCluster
open SpectreClusters Deformation
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def rawFrame4 (p : SpectreClusters.Point) : ExactPoint := ((0,2*p.1),(-2*p.1-4*p.2,0))
def rawLocalTargetVertex4 (kind : HTKind) (r : Turn) (e : Fin 14) : ExactPoint :=
  rawFrame4 (SpectreClusters.rotate r
    ((htRefinedPolygon kind).getD (physicalIndex kind e).val (0,0)))
def rawTargetOffset4 (kind : HTKind) (r : Turn) : ExactPoint :=
  ExactPoint.sub (rawLocalTargetVertex4 kind r 0) (targetVertex4 (physicalTurn ⟨kind,r,(0,0)⟩) 0)

theorem physicalIndex_involutive : ∀ kind : HTKind, ∀ e : Fin 14,
    physicalIndex kind (physicalIndex kind e) = e := by
  intro kind; cases kind <;> decide

theorem raw_local_target_binding : ∀ kind : HTKind, ∀ r : Turn, ∀ e : Fin 14,
    rawLocalTargetVertex4 kind r e =
      ExactPoint.add (rawTargetOffset4 kind r) (targetVertex4 (physicalTurn ⟨kind,r,(0,0)⟩) e) := by
  intro kind; cases kind <;> decide

end SpectreGeometry.ReversePhysicalCluster
