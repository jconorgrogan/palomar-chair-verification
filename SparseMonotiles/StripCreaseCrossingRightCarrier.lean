module

public import SparseMonotiles.KeyRidgeAngles
public import SparseMonotiles.SectorAngleUniqueness

@[expose] public section

/-! # A right-angle actual sector must come from a carrier germ -/
namespace SparseMonotiles
open Set Canonical

/-- Every nonconstant actual key model has angle strictly greater than π/2.
Thus a right-angle sector cannot be a key ridge or a key-side flat patch. -/
theorem key_active_normal_model_angle_gt_half_pi {n : ℕ} (k : KeyData (n+1))
    (hd : ∀ i b, 0 < keySideDistance k i b)
    (hs : ∀ i b, 0 < keySideSlope k i b ∧ keySideSlope k i b ≤ 1/2)
    (e : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1))
    (R : AffineSubspace ℝ (Point (n+1))) {p : Point (n+1)} (hp : p ∈ R)
    (hactive : ∀ a, keyPyramidHalfspaceSlack k a (e p) = 0 →
      ∀ x ∈ R, keyPyramidHalfspaceSlack k a (e x) = 0)
    (b : Bool) {M T : Set (Point (n+1))} {S : Set R.directionᗮ}
    (hM : IsActiveKeyRidgeModel (fun a x => keyPyramidHalfspaceSlack k a (e x)) b p M)
    (hS : IsPositiveCone S)
    (hmodel : LocalSetEq p T (ridgeNormalProjection R p ⁻¹' S))
    (hlocal : LocalSetEq p T M) :
    ∃ θ, SectorAngleSum.HasSectorAngle S θ ∧ Real.pi/2 < θ := by
  rcases hM with ⟨hz,heq⟩ | ⟨i,si,hz,heq⟩ |
    ⟨i,si,h0,hi,heq⟩ | ⟨i,j,si,sj,hij,hi,hj,heq⟩
  · rw [heq] at hlocal
    have h := key_facet_halfspace_normal_model_sector_angle k hd e R hp none
      (hactive _ hz) (!b) hS hmodel (by cases b <;> exact hlocal)
    exact ⟨Real.pi,h.1,by linarith [Real.pi_pos]⟩
  · rw [heq] at hlocal
    have h := key_facet_halfspace_normal_model_sector_angle k hd e R hp (some (i,si))
      (hactive _ hz) b hS hmodel hlocal
    exact ⟨Real.pi,h.1,by linarith [Real.pi_pos]⟩
  · rw [heq] at hlocal
    have h := key_base_side_normal_model_sector_angle k hd e R hp i si (hs i si)
      (hactive _ h0) (hactive _ hi) b hS hmodel hlocal
    refine ⟨_,h.1.1,?_⟩
    have hδ := h.2
    cases b <;> simp only [Bool.false_eq_true,if_false,if_true] <;> linarith [hδ.1,hδ.2,Real.pi_pos]
  · rw [heq] at hlocal
    have h := key_side_side_normal_model_sector_angle k hd e R hp i j hij si sj (hs i si) (hs j sj)
      (hactive _ hi) (hactive _ hj) b hS hmodel hlocal
    refine ⟨_,h.1.1,?_⟩
    have hδ := h.2
    cases b <;> simp only [Bool.false_eq_true,if_false,if_true] <;> linarith [hδ.1,hδ.2,Real.pi_pos]

private theorem right_carrier_image_isometry_as_preimage {d : ℕ}
    (g : Point d ≃ᵢ Point d) (M : Set (Point d)) : g '' M = g.symm ⁻¹' M := by
  ext x
  exact ⟨fun ⟨y,hy,hxy⟩ => by simpa only [Set.mem_preimage,← hxy,g.symm_apply_apply] using hy,
    fun hx => ⟨g.symm x,hx,g.apply_symm_apply x⟩⟩


/-- A genuine right-angle cone of the literal T5 body has a carrier germ.
Every possible key branch is excluded by its proved angle and angle uniqueness. -/
theorem T5_right_angle_normal_cone_carrier_germ
    (g : Point 5 ≃ᵢ Point 5) (R : AffineSubspace ℝ (Point 5))
    {p : Point 5} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 5)
    (hactive : ∀ j, T5WorldAffineFields g j p = 0 →
      R ≤ affineFormPlane (T5WorldAffineFields g j) 0)
    {S : Set R.directionᗮ} (hS : IsPositiveCone S)
    (hmodel : LocalSetEq p (g '' T5) (ridgeNormalProjection R p ⁻¹' S))
    (hboundary : p ∈ frontier (g '' T5))
    (hright : SectorAngleSum.HasSectorAngle S (Real.pi/2)) :
    LocalSetEq p (g '' T5) (g '' carrier 5) := by
  rcases T5_generic_active_physical_key_model_inventory g R hcodim hp hactive hboundary with
    hcarrier | ⟨k,hk,q,M,hq,hzero,hM,hlocal⟩
  · exact hcarrier
  · let e : Point 5 ≃ᵃⁱ[ℝ] Point 5 := g.symm.toRealAffineIsometryEquiv.trans q.euclidean.symm
    have hMw := IsActiveKeyRidgeModel.preimage (posedHalfspaceSlack5 q) k.bump g.symm p hM
    rw [right_carrier_image_isometry_as_preimage g M] at hlocal
    obtain ⟨θ,hθ,hgt⟩ := key_active_normal_model_angle_gt_half_pi
      ((referenceBox5 true).toKeyData 19200) referenceSideDistance5_pos referenceSideSlope5_bounds
      e R hp hzero k.bump hMw hS hmodel hlocal
    have hdim : Module.finrank ℝ R.directionᗮ = 2 := by
      apply ridge_orthogonal_finrank_two R
      simpa only [Point,finrank_euclideanSpace,Fintype.card_fin] using hcodim
    have heq := hθ.angle_unique hdim hright
    rw [heq] at hgt
    exact (lt_irrefl _ hgt).elim

#print axioms T5_right_angle_normal_cone_carrier_germ

/-- A genuine right-angle cone of the literal T7 body has a carrier germ.
Every possible key branch is excluded by its proved angle and angle uniqueness. -/
theorem T7_right_angle_normal_cone_carrier_germ
    (g : Point 7 ≃ᵢ Point 7) (R : AffineSubspace ℝ (Point 7))
    {p : Point 7} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 7)
    (hactive : ∀ j, T7WorldAffineFields g j p = 0 →
      R ≤ affineFormPlane (T7WorldAffineFields g j) 0)
    {S : Set R.directionᗮ} (hS : IsPositiveCone S)
    (hmodel : LocalSetEq p (g '' T7) (ridgeNormalProjection R p ⁻¹' S))
    (hboundary : p ∈ frontier (g '' T7))
    (hright : SectorAngleSum.HasSectorAngle S (Real.pi/2)) :
    LocalSetEq p (g '' T7) (g '' carrier 7) := by
  rcases T7_generic_active_physical_key_model_inventory g R hcodim hp hactive hboundary with
    hcarrier | ⟨k,hk,q,M,hq,hzero,hM,hlocal⟩
  · exact hcarrier
  · let e : Point 7 ≃ᵃⁱ[ℝ] Point 7 := g.symm.toRealAffineIsometryEquiv.trans q.euclidean.symm
    have hMw := IsActiveKeyRidgeModel.preimage (posedHalfspaceSlack7 q) k.bump g.symm p hM
    rw [right_carrier_image_isometry_as_preimage g M] at hlocal
    obtain ⟨θ,hθ,hgt⟩ := key_active_normal_model_angle_gt_half_pi
      ((referenceBox7 true).toKeyData 188160) referenceSideDistance7_pos referenceSideSlope7_bounds
      e R hp hzero k.bump hMw hS hmodel hlocal
    have hdim : Module.finrank ℝ R.directionᗮ = 2 := by
      apply ridge_orthogonal_finrank_two R
      simpa only [Point,finrank_euclideanSpace,Fintype.card_fin] using hcodim
    have heq := hθ.angle_unique hdim hright
    rw [heq] at hgt
    exact (lt_irrefl _ hgt).elim

#print axioms T7_right_angle_normal_cone_carrier_germ

#print axioms key_active_normal_model_angle_gt_half_pi
end SparseMonotiles
