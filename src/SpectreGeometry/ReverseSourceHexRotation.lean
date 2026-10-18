module

public import SpectreGeometry.ReverseSourceHexIntersections
public import SpectreGeometry.GridAffineGeometry
public import SpectreFinite.HexRotation

@[expose] public section


/-! Rotation binding for the fixed source hexagons. These are direct real
coordinate proofs, separate from the frozen source-cover construction. -/
namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set SpectreClusters SpectreFinite.HexSearch

theorem gridRotation_inverse_cancel (r : Fin 6) (p : RealPoint) :
    gridRotation r (gridRotation (inverseTurn r) p) = p := by
  fin_cases r <;> ext <;> simp [gridRotation,inverseTurn] <;> ring

/-- The source hexagon's six inequalities are permuted by every grid turn. -/
theorem sourceHexCarrier_gridRotation_iff (r : Fin 6) (p : RealPoint) :
    gridRotation r p ∈ sourceHexCarrier (0,0) ↔ p ∈ sourceHexCarrier (0,0) := by
  fin_cases r <;>
    simp only [gridRotation,sourceHexCarrier,sourceHexOffset,Set.mem_ofPred_eq,
      Int.cast_zero,sub_zero] <;>
    constructor <;> rintro ⟨h1,h2,h3,h4,h5,h6⟩ <;>
    refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith

/-- Actual set-image invariance, with a concrete inverse rotation witness. -/
theorem gridRotation_image_sourceHexCarrier (r : Fin 6) :
    gridRotation r '' sourceHexCarrier (0,0) = sourceHexCarrier (0,0) := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact (sourceHexCarrier_gridRotation_iff r q).mpr hq
  · intro hp
    exact ⟨gridRotation (inverseTurn r) p,(sourceHexCarrier_gridRotation_iff (inverseTurn r) p).mpr hp,
      gridRotation_inverse_cancel r p⟩

/-- Corner labels rotate in exactly the same direction as the source carrier. -/
theorem gridRotation_sourceHexCorner (r d : Fin 6) :
    gridRotation r (sourceHexCorner d) = sourceHexCorner (rotateTurn r d) := by
  fin_cases r <;> fin_cases d <;> norm_num [gridRotation,sourceHexCorner,rotateTurn]

end
end SpectreGeometry.ReverseExistence
