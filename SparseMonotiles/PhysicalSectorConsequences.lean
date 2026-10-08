module

public import SparseMonotiles.PhysicalSectorPartition
public import SparseMonotiles.SectorRootBoundary

@[expose] public section

/-! # Genuine root sectors discharge their own boundary premise -/
namespace SparseMonotiles
open Set

theorem T5_key_root_incident_card_two
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (R : AffineSubspace ℝ (Point 5)) {p : Point 5} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 5)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5)) = g A '' T5)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T5WorldAffineFields (g ⟨A,A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T5WorldAffineFields (g ⟨A,A.property.1⟩) j) 0)
    (root : incidentTiles tiles p) {θ δ : ℝ}
    (hroot : SectorAngleSum.HasSectorAngle (T5IncidentNormalCone g R p root) θ)
    (hδ : 0 < δ) (hδ' : δ < Real.pi/4)
    (hkey : θ = Real.pi-δ ∨ θ = Real.pi+δ) :
    Nat.card (incidentTiles tiles p) = 2 := by
  have hinv : SectorArithmetic.InAngleInventory θ :=
    Or.inr (Or.inr (Or.inr ⟨δ,hδ,hδ',hkey⟩))
  have hbounds := angleInventory_pos_lt_two_pi hinv
  have hpart := T5_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  have hboundary := mem_frontier_of_normal_sector R p hpart.2.1 hroot
    hbounds.1 hbounds.2 (hpart.2.2.1 root).2.2
  exact T5_generic_key_root_exactly_two_incident ht R hp hcodim g hg hactive root
    hroot hδ hδ' hkey hboundary

theorem T5_flat_root_incident_card_two_or_three
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (R : AffineSubspace ℝ (Point 5)) {p : Point 5} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 5)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5)) = g A '' T5)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T5WorldAffineFields (g ⟨A,A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T5WorldAffineFields (g ⟨A,A.property.1⟩) j) 0)
    (root : incidentTiles tiles p)
    (hroot : SectorAngleSum.HasSectorAngle (T5IncidentNormalCone g R p root) Real.pi) :
    Nat.card (incidentTiles tiles p) = 2 ∨ Nat.card (incidentTiles tiles p) = 3 := by
  have hpart := T5_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  have hboundary := mem_frontier_of_normal_sector R p hpart.2.1 hroot
    Real.pi_pos (by linarith [Real.pi_pos]) (hpart.2.2.1 root).2.2
  exact T5_generic_flat_root_incident_count ht R hp hcodim g hg hactive root hroot hboundary

#print axioms T5_key_root_incident_card_two
#print axioms T5_flat_root_incident_card_two_or_three

theorem T7_key_root_incident_card_two
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (R : AffineSubspace ℝ (Point 7)) {p : Point 7} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 7)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7)) = g A '' T7)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T7WorldAffineFields (g ⟨A,A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T7WorldAffineFields (g ⟨A,A.property.1⟩) j) 0)
    (root : incidentTiles tiles p) {θ δ : ℝ}
    (hroot : SectorAngleSum.HasSectorAngle (T7IncidentNormalCone g R p root) θ)
    (hδ : 0 < δ) (hδ' : δ < Real.pi/4)
    (hkey : θ = Real.pi-δ ∨ θ = Real.pi+δ) :
    Nat.card (incidentTiles tiles p) = 2 := by
  have hinv : SectorArithmetic.InAngleInventory θ :=
    Or.inr (Or.inr (Or.inr ⟨δ,hδ,hδ',hkey⟩))
  have hbounds := angleInventory_pos_lt_two_pi hinv
  have hpart := T7_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  have hboundary := mem_frontier_of_normal_sector R p hpart.2.1 hroot
    hbounds.1 hbounds.2 (hpart.2.2.1 root).2.2
  exact T7_generic_key_root_exactly_two_incident ht R hp hcodim g hg hactive root
    hroot hδ hδ' hkey hboundary

theorem T7_flat_root_incident_card_two_or_three
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (R : AffineSubspace ℝ (Point 7)) {p : Point 7} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 7)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7)) = g A '' T7)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T7WorldAffineFields (g ⟨A,A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T7WorldAffineFields (g ⟨A,A.property.1⟩) j) 0)
    (root : incidentTiles tiles p)
    (hroot : SectorAngleSum.HasSectorAngle (T7IncidentNormalCone g R p root) Real.pi) :
    Nat.card (incidentTiles tiles p) = 2 ∨ Nat.card (incidentTiles tiles p) = 3 := by
  have hpart := T7_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  have hboundary := mem_frontier_of_normal_sector R p hpart.2.1 hroot
    Real.pi_pos (by linarith [Real.pi_pos]) (hpart.2.2.1 root).2.2
  exact T7_generic_flat_root_incident_count ht R hp hcodim g hg hactive root hroot hboundary

#print axioms T7_key_root_incident_card_two
#print axioms T7_flat_root_incident_card_two_or_three

end SparseMonotiles
