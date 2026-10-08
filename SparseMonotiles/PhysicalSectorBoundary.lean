module

public import SparseMonotiles.SectorRegularity
public import SparseMonotiles.IncidentTileBoundary

@[expose] public section

/-! # Genuine root sectors force boundary status of every incident tile -/
namespace SparseMonotiles
open Set

/-- A genuine normal-space sector pulls back to a regular closed ambient model. -/
theorem normal_sector_pullback_regular_closed {d : ℕ}
    (R : AffineSubspace ℝ (Point d)) (p : Point d)
    {S : Set R.directionᗮ} {θ : ℝ} (hS : SectorAngleSum.HasSectorAngle S θ) :
    closure (interior (ridgeNormalProjection R p ⁻¹' S)) =
      ridgeNormalProjection R p ⁻¹' S := by
  rw [ridgeNormalProjection_preimage_interior, ridgeNormalProjection_preimage_closure,
    hS.regular_closed]

/-- Actual root-sector geometry supplies the local regularity needed for the
whole incident family. No boundary premise is imposed on its other indices. -/
theorem IsTiling.incident_mem_frontier_of_root_sector {d : ℕ}
    {T : Set (Point d)} {tiles : Set (Set (Point d))}
    (ht : IsTiling T tiles) (hT : IsCompact T)
    (R : AffineSubspace ℝ (Point d)) (p : Point d)
    (root : incidentTiles tiles p)
    {S : Set R.directionᗮ} {θ : ℝ} (hS : SectorAngleSum.HasSectorAngle S θ)
    (hmodel : LocalSetEq p (root : Set (Point d)) (ridgeNormalProjection R p ⁻¹' S))
    (hboundary : p ∈ frontier (root : Set (Point d))) :
    ∀ A : incidentTiles tiles p, p ∈ frontier (A : Set (Point d)) := by
  have hreg := hmodel.mem_closure_interior_of_model root.property.2
    (show ridgeNormalProjection R p ⁻¹' S ⊆
      closure (interior (ridgeNormalProjection R p ⁻¹' S)) from
      (normal_sector_pullback_regular_closed R p hS).symm.subset)
  exact ht.incident_mem_frontier_of_regular_root hT root.property.1 hboundary hreg

#print axioms normal_sector_pullback_regular_closed
#print axioms IsTiling.incident_mem_frontier_of_root_sector
end SparseMonotiles
