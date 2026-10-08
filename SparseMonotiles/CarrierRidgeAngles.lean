module

public import SparseMonotiles.CarrierRidgeInventory
public import SparseMonotiles.SectorAngleSumInventories

@[expose] public section

/-! # Exact carrier sector angles from the derived literal normal inventory -/
namespace SparseMonotiles

open Set

/-- Every genuine boundary cone in the derived carrier inventory has exactly
one of the three carrier widths, together with its actual angular-sector proof. -/
theorem IsRightAngleBoundaryCone.hasSectorAngle
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S : Set E} (h : IsRightAngleBoundaryCone S) :
    ∃ θ, SectorAngleSum.HasSectorAngle S θ ∧
      (θ = Real.pi / 2 ∨ θ = Real.pi ∨ θ = 3 * Real.pi / 2) ∧
      SectorArithmetic.InAngleInventory θ := by
  have hne {n : E} (hn : ‖n‖ = 1) : n ≠ 0 := by
    intro hz
    simp [hz] at hn
  rcases h with ⟨n, hn, rfl⟩ | ⟨n, m, hn, hm, hnm, hS⟩
  · have hi := SectorAngleSum.halfplane_angle_inventory n (hne hn)
    exact ⟨Real.pi, hi.1, Or.inr (Or.inl rfl), hi.2⟩
  · have hi := SectorAngleSum.orthogonal_normal_angle_inventory n m (hne hn) (hne hm) hnm
    rcases hS with rfl | rfl
    · exact ⟨Real.pi / 2, hi.1.1, Or.inl rfl, hi.1.2⟩
    · exact ⟨3 * Real.pi / 2, hi.2.1, Or.inr (Or.inr rfl), hi.2.2⟩

/-- Carrier branch of the actual T5 boundary normal model, now with computed
angles rather than merely an asserted numerical angle inventory. -/
theorem T5_carrier_germ_sector_angle_inventory
    (g : Point 5 ≃ᵢ Point 5) (R : AffineSubspace ℝ (Point 5))
    {p : Point 5} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 5)
    (hactive : ∀ j, T5WorldAffineFields g j p = 0 →
      R ≤ affineFormPlane (T5WorldAffineFields g j) 0)
    {T : Set (Point 5)} {S : Set R.directionᗮ}
    (hS : IsPositiveCone S)
    (hmodel : LocalSetEq p T (ridgeNormalProjection R p ⁻¹' S))
    (hcarrier : LocalSetEq p T (g '' carrier 5))
    (hboundary : p ∈ frontier T) :
    ∃ θ, SectorAngleSum.HasSectorAngle S θ ∧
      (θ = Real.pi / 2 ∨ θ = Real.pi ∨ θ = 3 * Real.pi / 2) ∧
      SectorArithmetic.InAngleInventory θ :=
  (T5_boundary_normal_model_inventory_of_carrier_germ
    g R hp hcodim hactive hS hmodel hcarrier hboundary).hasSectorAngle

/-- The identical exact carrier-angle bridge for T7. -/
theorem T7_carrier_germ_sector_angle_inventory
    (g : Point 7 ≃ᵢ Point 7) (R : AffineSubspace ℝ (Point 7))
    {p : Point 7} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 7)
    (hactive : ∀ j, T7WorldAffineFields g j p = 0 →
      R ≤ affineFormPlane (T7WorldAffineFields g j) 0)
    {T : Set (Point 7)} {S : Set R.directionᗮ}
    (hS : IsPositiveCone S)
    (hmodel : LocalSetEq p T (ridgeNormalProjection R p ⁻¹' S))
    (hcarrier : LocalSetEq p T (g '' carrier 7))
    (hboundary : p ∈ frontier T) :
    ∃ θ, SectorAngleSum.HasSectorAngle S θ ∧
      (θ = Real.pi / 2 ∨ θ = Real.pi ∨ θ = 3 * Real.pi / 2) ∧
      SectorArithmetic.InAngleInventory θ :=
  (T7_boundary_normal_model_inventory_of_carrier_germ
    g R hp hcodim hactive hS hmodel hcarrier hboundary).hasSectorAngle

#print axioms IsRightAngleBoundaryCone.hasSectorAngle
#print axioms T5_carrier_germ_sector_angle_inventory
#print axioms T7_carrier_germ_sector_angle_inventory

end SparseMonotiles
