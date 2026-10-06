module

public import SparseMonotiles.StripCreaseCrossingCarrierCells
public import SparseMonotiles.StripCreaseCrossingCarrierQuadrant
public import SparseMonotiles.TileGeometry

@[expose] public section

/-! # Concrete exposed unit carrier edges at actual right-angle sectors -/
namespace SparseMonotiles
open Set

/-- Every active native carrier coordinate is constant along the whole
physical ridge, as a direct consequence of the actual affine field inventory. -/
theorem carrier_frame_critical_coordinate_constant {d : ℕ}
    (a : Point d ≃ᵃⁱ[ℝ] Point d) (R : AffineSubspace ℝ (Point d)) {p : Point d}
    (hactive : ∀ j : CarrierHalfspaceIndex d, carrierFrameFields a j p = 0 →
      R ≤ affineFormPlane (carrierFrameFields a j) 0)
    (i : Fin d) (hi : i ∈ carrierCriticalAxes (a p)) :
    ∀ x ∈ R, a x i = a p i := by
  rcases (mem_carrierCriticalAxes (a p) i).mp hi with hi | hi | hi
  · have hz : carrierFrameFields a (i,0) p = 0 := by simp [carrierFrameFields_apply,carrierHalfspaceSlack,hi]
    intro x hx
    have he := (mem_affineFormPlane _ _ _).mp (hactive (i,0) hz hx)
    simpa [carrierFrameFields_apply,carrierHalfspaceSlack,hi] using he
  · have hz : carrierFrameFields a (i,2) p = 0 := by simp [carrierFrameFields_apply,carrierHalfspaceSlack,hi]
    intro x hx
    have he := (mem_affineFormPlane _ _ _).mp (hactive (i,2) hz hx)
    simp [carrierFrameFields_apply,carrierHalfspaceSlack] at he
    rw [hi]
    linarith
  · have hz : carrierFrameFields a (i,1) p = 0 := by simp [carrierFrameFields_apply,carrierHalfspaceSlack,hi]
    intro x hx
    have he := (mem_affineFormPlane _ _ _).mp (hactive (i,1) hz hx)
    simp [carrierFrameFields_apply,carrierHalfspaceSlack] at he
    rw [hi]
    linarith


/-- A literal T5 right-angle sector yields two actual exposed unit facets
and a relative-interior point of their shared native integer edge. Carrier
ownership, exposure, strict other coordinates, and whole-ridge equations are
all conclusions. -/
theorem T5_right_angle_sector_exposed_unit_edge
    (g : Point 5 ≃ᵢ Point 5) (R : AffineSubspace ℝ (Point 5))
    {p : Point 5} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 5)
    (hactive : ∀ j, T5WorldAffineFields g j p = 0 →
      R ≤ affineFormPlane (T5WorldAffineFields g j) 0)
    {S : Set R.directionᗮ} (hS : IsPositiveCone S)
    (hmodel : LocalSetEq p (g '' T5) (ridgeNormalProjection R p ⁻¹' S))
    (hboundary : p ∈ frontier (g '' T5))
    (hright : SectorAngleSum.HasSectorAngle S (Real.pi/2)) :
    ∃ i j : Fin 5, ∃ b c : Bool, ∃ q : Contact.Cell 5, i ≠ j ∧
      Contact.IsChairCell q ∧ g.symm p ∈ closedIntegerCell q ∧
      g.symm p i = (q i : ℝ)+(if b then 0 else 1) ∧
      g.symm p j = (q j : ℝ)+(if c then 0 else 1) ∧
      (∀ a, a ≠ i → a ≠ j → (q a : ℝ) < g.symm p a ∧ g.symm p a < (q a : ℝ)+1) ∧
      (¬ Contact.IsChairCell ({cell := q,axis := i,positive := !b} : Contact.Facet 5).neighbor) ∧
      (¬ Contact.IsChairCell ({cell := q,axis := j,positive := !c} : Contact.Facet 5).neighbor) ∧
      (∀ x ∈ R, g.symm x i = g.symm p i ∧ g.symm x j = g.symm p j) ∧
      S = (fun v : R.directionᗮ => g.symm.toRealAffineIsometryEquiv.linearIsometryEquiv
        (v : Point 5)) ⁻¹' (carrierAxisHalfspace i b ∩ carrierAxisHalfspace j c) := by
  have hc := T5_right_angle_normal_cone_carrier_germ g R hp hcodim hactive hS hmodel hboundary hright
  have himage := hc.mem_iff.mp ((T5_isCompact.image g.continuous).isClosed.frontier_subset hboundary)
  have hnative : g.symm p ∈ carrier 5 := by
    obtain ⟨x,hx,hxp⟩ := himage
    rw [← hxp,g.symm_apply_apply]
    exact hx
  obtain ⟨_,i,j,b,c,hij,hi,hj,hC,hS'⟩ :=
    T5_right_angle_normal_cone_coordinate_quadrant g R hp hcodim hactive hS hmodel hboundary hright
  have hact : ∀ l : CarrierHalfspaceIndex 5, carrierFrameFields g.symm.toRealAffineIsometryEquiv l p = 0 →
      R ≤ affineFormPlane (carrierFrameFields g.symm.toRealAffineIsometryEquiv l) 0 :=
    fun l hl => hactive (.inl l) hl
  have hcard := carrier_frame_criticalAxes_card_le_two g.symm.toRealAffineIsometryEquiv R hp hcodim hact
  have hcrit := carrier_critical_axes_covered_of_card_le_two (g.symm p) i j hij hi hj hcard
  obtain ⟨q,hq,hpq,hendi,hendj,hother,hexpi,hexpj⟩ :=
    carrier_quadrant_exists_exposed_edge hnative i j b c hij hi hj hcrit hC
  refine ⟨i,j,b,c,q,hij,hq,hpq,hendi,hendj,hother,hexpi,hexpj,?_,hS'⟩
  intro x hx
  exact ⟨carrier_frame_critical_coordinate_constant g.symm.toRealAffineIsometryEquiv R hact i hi x hx,
    carrier_frame_critical_coordinate_constant g.symm.toRealAffineIsometryEquiv R hact j hj x hx⟩

#print axioms T5_right_angle_sector_exposed_unit_edge

/-- A literal T7 right-angle sector yields two actual exposed unit facets
and a relative-interior point of their shared native integer edge. Carrier
ownership, exposure, strict other coordinates, and whole-ridge equations are
all conclusions. -/
theorem T7_right_angle_sector_exposed_unit_edge
    (g : Point 7 ≃ᵢ Point 7) (R : AffineSubspace ℝ (Point 7))
    {p : Point 7} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 7)
    (hactive : ∀ j, T7WorldAffineFields g j p = 0 →
      R ≤ affineFormPlane (T7WorldAffineFields g j) 0)
    {S : Set R.directionᗮ} (hS : IsPositiveCone S)
    (hmodel : LocalSetEq p (g '' T7) (ridgeNormalProjection R p ⁻¹' S))
    (hboundary : p ∈ frontier (g '' T7))
    (hright : SectorAngleSum.HasSectorAngle S (Real.pi/2)) :
    ∃ i j : Fin 7, ∃ b c : Bool, ∃ q : Contact.Cell 7, i ≠ j ∧
      Contact.IsChairCell q ∧ g.symm p ∈ closedIntegerCell q ∧
      g.symm p i = (q i : ℝ)+(if b then 0 else 1) ∧
      g.symm p j = (q j : ℝ)+(if c then 0 else 1) ∧
      (∀ a, a ≠ i → a ≠ j → (q a : ℝ) < g.symm p a ∧ g.symm p a < (q a : ℝ)+1) ∧
      (¬ Contact.IsChairCell ({cell := q,axis := i,positive := !b} : Contact.Facet 7).neighbor) ∧
      (¬ Contact.IsChairCell ({cell := q,axis := j,positive := !c} : Contact.Facet 7).neighbor) ∧
      (∀ x ∈ R, g.symm x i = g.symm p i ∧ g.symm x j = g.symm p j) ∧
      S = (fun v : R.directionᗮ => g.symm.toRealAffineIsometryEquiv.linearIsometryEquiv
        (v : Point 7)) ⁻¹' (carrierAxisHalfspace i b ∩ carrierAxisHalfspace j c) := by
  have hc := T7_right_angle_normal_cone_carrier_germ g R hp hcodim hactive hS hmodel hboundary hright
  have himage := hc.mem_iff.mp ((T7_isCompact.image g.continuous).isClosed.frontier_subset hboundary)
  have hnative : g.symm p ∈ carrier 7 := by
    obtain ⟨x,hx,hxp⟩ := himage
    rw [← hxp,g.symm_apply_apply]
    exact hx
  obtain ⟨_,i,j,b,c,hij,hi,hj,hC,hS'⟩ :=
    T7_right_angle_normal_cone_coordinate_quadrant g R hp hcodim hactive hS hmodel hboundary hright
  have hact : ∀ l : CarrierHalfspaceIndex 7, carrierFrameFields g.symm.toRealAffineIsometryEquiv l p = 0 →
      R ≤ affineFormPlane (carrierFrameFields g.symm.toRealAffineIsometryEquiv l) 0 :=
    fun l hl => hactive (.inl l) hl
  have hcard := carrier_frame_criticalAxes_card_le_two g.symm.toRealAffineIsometryEquiv R hp hcodim hact
  have hcrit := carrier_critical_axes_covered_of_card_le_two (g.symm p) i j hij hi hj hcard
  obtain ⟨q,hq,hpq,hendi,hendj,hother,hexpi,hexpj⟩ :=
    carrier_quadrant_exists_exposed_edge hnative i j b c hij hi hj hcrit hC
  refine ⟨i,j,b,c,q,hij,hq,hpq,hendi,hendj,hother,hexpi,hexpj,?_,hS'⟩
  intro x hx
  exact ⟨carrier_frame_critical_coordinate_constant g.symm.toRealAffineIsometryEquiv R hact i hi x hx,
    carrier_frame_critical_coordinate_constant g.symm.toRealAffineIsometryEquiv R hact j hj x hx⟩

#print axioms T7_right_angle_sector_exposed_unit_edge

#print axioms carrier_frame_critical_coordinate_constant
end SparseMonotiles
