module

public import SparseMonotiles.StripCreaseCrossingRightCarrier

@[expose] public section

/-! # Retain actual carrier coordinates in the right-angle seam branch -/
namespace SparseMonotiles
open Set

/-- Right-angle width picks the native quadrant constructor while retaining
its actual active coordinate axes and signs. -/
theorem IsCarrierCoordinateCone.right_angle_quadrant {d : ℕ}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : Point d ≃ₗᵢ[ℝ] E) (V : Submodule ℝ E) [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V = 2) (p : Point d)
    (hmem : ∀ i ∈ carrierCriticalAxes p, e (EuclideanSpace.single i 1) ∈ V)
    {C : Set (Point d)} (hC : IsCarrierCoordinateCone p C)
    (hangle : SectorAngleSum.HasSectorAngle ((fun v : V => e.symm (v : E)) ⁻¹' C) (Real.pi/2)) :
    ∃ i j : Fin d, ∃ b c : Bool, i ≠ j ∧
      i ∈ carrierCriticalAxes p ∧ j ∈ carrierCriticalAxes p ∧
      C = carrierAxisHalfspace i b ∩ carrierAxisHalfspace j c := by
  have hne {v : V} (hv : ‖v‖ = 1) : v ≠ 0 := by intro hz; simp [hz] at hv
  cases hC with
  | empty =>
      have hz : SectorAngleSum.HasSectorAngle
          ((fun v : V => e.symm (v : E)) ⁻¹' (∅ : Set (Point d))) 0 := .empty (by simp)
      have heq := hangle.angle_unique hdim hz
      linarith [Real.pi_pos]
  | univ =>
      have hz : SectorAngleSum.HasSectorAngle
          ((fun v : V => e.symm (v : E)) ⁻¹' (Set.univ : Set (Point d))) (2*Real.pi) := .full (by simp)
      have heq := hangle.angle_unique hdim hz
      linarith [Real.pi_pos]
  | half i b hi =>
      rw [← normalHalfspace_signedAxisNormal e V i (hmem i hi) b] at hangle
      have hz := SectorAngleSum.halfplane_angle_inventory (signedAxisNormal e V i (hmem i hi) b)
        (hne (norm_signedAxisNormal e V i (hmem i hi) b))
      have heq := hangle.angle_unique hdim hz.1
      linarith [Real.pi_pos]
  | quadrant i j b c hij hi hj => exact ⟨i,j,b,c,hij,hi,hj,rfl⟩
  | reflex i j hij hi hj =>
      have hi' : i ∈ carrierCriticalAxes p := by simp [hi]
      have hj' : j ∈ carrierCriticalAxes p := by simp [hj]
      rw [preimage_union,← normalHalfspace_signedAxisNormal e V i (hmem i hi') false,
        ← normalHalfspace_signedAxisNormal e V j (hmem j hj') false] at hangle
      have hz := SectorAngleSum.orthogonal_normal_angle_inventory
        (signedAxisNormal e V i (hmem i hi') false) (signedAxisNormal e V j (hmem j hj') false)
        (hne (norm_signedAxisNormal e V i (hmem i hi') false))
        (hne (norm_signedAxisNormal e V j (hmem j hj') false))
        (inner_signedAxisNormal e V i j (hmem i hi') (hmem j hj') false false hij)
      have heq := hangle.angle_unique hdim hz.2.1
      linarith [Real.pi_pos]

/-- An actual right-angle carrier germ is a native coordinate quadrant, with
both axes retained and certified active. All cone equalities are derived from
actual local models and positive homogeneity. -/
theorem right_angle_carrier_germ_coordinate_quadrant {d : ℕ}
    (a : Point d ≃ᵃⁱ[ℝ] Point d) (R : AffineSubspace ℝ (Point d))
    {p : Point d} (hp : p ∈ R) (hcodim : Module.finrank ℝ R.direction+2=d)
    (hactive : ∀ j : CarrierHalfspaceIndex d, carrierFrameFields a j p = 0 →
      R ≤ affineFormPlane (carrierFrameFields a j) 0)
    {T : Set (Point d)} {S : Set R.directionᗮ} (hS : IsPositiveCone S)
    (hmodel : LocalSetEq p T (ridgeNormalProjection R p ⁻¹' S))
    (hcarrier : LocalSetEq p T (a ⁻¹' carrier d))
    (hright : SectorAngleSum.HasSectorAngle S (Real.pi/2)) :
    ∃ i j : Fin d, ∃ b c : Bool, i ≠ j ∧
      i ∈ carrierCriticalAxes (a p) ∧ j ∈ carrierCriticalAxes (a p) ∧
      carrierLinearCone (a p) = carrierAxisHalfspace i b ∩ carrierAxisHalfspace j c ∧
      S = (fun v : R.directionᗮ => a.linearIsometryEquiv (v : Point d)) ⁻¹'
        (carrierAxisHalfspace i b ∩ carrierAxisHalfspace j c) := by
  have hmem (i) (hi : i ∈ carrierCriticalAxes (a p)) :=
    carrier_frame_axis_mem_ridge_orthogonal a R hp hactive hi
  have hcoord := carrierLinearCone_inventory (by omega : 2 ≤ d) (a p)
    (carrier_frame_criticalAxes_card_le_two a R hp hcodim hactive)
  have hclosed := (hcoord.normal_inventory a.linearIsometryEquiv.symm R.directionᗮ (a p) hmem).isClosed
  simp only [LinearIsometryEquiv.symm_symm] at hclosed
  have hlocal := hmodel.symm.trans
    (hcarrier.trans (carrier_frame_localSetEq_normal_section a R hp hactive))
  have heq := normalCones_eq_of_localSetEq R p hS
    (closure_frozenRidgeSection_isPositiveCone R p (carrierFrameFields a)
      (carrierHalfspaceFormula d)) hlocal
  rw [carrier_frame_frozenRidgeSection_eq] at heq
  rw [hclosed.closure_eq] at heq
  have hdim : Module.finrank ℝ R.directionᗮ = 2 := by
    apply ridge_orthogonal_finrank_two R
    simpa only [Point,finrank_euclideanSpace,Fintype.card_fin] using hcodim
  obtain ⟨i,j,b,c,hij,hi,hj,hC⟩ := hcoord.right_angle_quadrant
    a.linearIsometryEquiv.symm R.directionᗮ hdim (a p) hmem (by simpa only [LinearIsometryEquiv.symm_symm,← heq] using hright)
  exact ⟨i,j,b,c,hij,hi,hj,hC,heq.trans (congrArg _ hC)⟩

/-- The native seam point is on the genuine integer codimension-two
skeleton; distinct active carrier coordinates are enough. -/
theorem mem_integerSkeleton_of_two_critical_axes {d : ℕ} (p : Point d)
    (i j : Fin d) (hij : i ≠ j)
    (hi : i ∈ carrierCriticalAxes p) (hj : j ∈ carrierCriticalAxes p) :
    p ∈ integerSkeleton d := by
  have hint (a : Fin d) (ha : a ∈ carrierCriticalAxes p) : ∃ z : ℤ, p a = (z : ℝ) := by
    rcases (mem_carrierCriticalAxes p a).mp ha with h | h | h
    · exact ⟨0,by simpa using h⟩
    · exact ⟨1,by simpa using h⟩
    · exact ⟨2,by simpa using h⟩
  exact ⟨i,j,hij,hint i hi,hint j hj⟩


/-- Literal T5 right sectors retain their native coordinate quadrant and
actual integer-skeleton seam point, with no carrier-branch premise. -/
theorem T5_right_angle_normal_cone_coordinate_quadrant
    (g : Point 5 ≃ᵢ Point 5) (R : AffineSubspace ℝ (Point 5))
    {p : Point 5} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 5)
    (hactive : ∀ j, T5WorldAffineFields g j p = 0 →
      R ≤ affineFormPlane (T5WorldAffineFields g j) 0)
    {S : Set R.directionᗮ} (hS : IsPositiveCone S)
    (hmodel : LocalSetEq p (g '' T5) (ridgeNormalProjection R p ⁻¹' S))
    (hboundary : p ∈ frontier (g '' T5))
    (hright : SectorAngleSum.HasSectorAngle S (Real.pi/2)) :
    g.symm p ∈ integerSkeleton 5 ∧
    ∃ i j : Fin 5, ∃ b c : Bool, i ≠ j ∧
      i ∈ carrierCriticalAxes (g.symm p) ∧ j ∈ carrierCriticalAxes (g.symm p) ∧
      carrierLinearCone (g.symm p) = carrierAxisHalfspace i b ∩ carrierAxisHalfspace j c ∧
      S = (fun v : R.directionᗮ => g.symm.toRealAffineIsometryEquiv.linearIsometryEquiv
        (v : Point 5)) ⁻¹' (carrierAxisHalfspace i b ∩ carrierAxisHalfspace j c) := by
  have hc := T5_right_angle_normal_cone_carrier_germ g R hp hcodim hactive hS hmodel hboundary hright
  obtain ⟨i,j,b,c,hij,hi,hj,hC,hS'⟩ := right_angle_carrier_germ_coordinate_quadrant
    g.symm.toRealAffineIsometryEquiv R hp hcodim (fun j hj => hactive (.inl j) hj)
    hS hmodel (by simpa only [inverse_frame_carrier_preimage] using hc) hright
  exact ⟨mem_integerSkeleton_of_two_critical_axes (g.symm p) i j hij hi hj,i,j,b,c,hij,hi,hj,hC,hS'⟩

#print axioms T5_right_angle_normal_cone_coordinate_quadrant

/-- Literal T7 right sectors retain their native coordinate quadrant and
actual integer-skeleton seam point, with no carrier-branch premise. -/
theorem T7_right_angle_normal_cone_coordinate_quadrant
    (g : Point 7 ≃ᵢ Point 7) (R : AffineSubspace ℝ (Point 7))
    {p : Point 7} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 7)
    (hactive : ∀ j, T7WorldAffineFields g j p = 0 →
      R ≤ affineFormPlane (T7WorldAffineFields g j) 0)
    {S : Set R.directionᗮ} (hS : IsPositiveCone S)
    (hmodel : LocalSetEq p (g '' T7) (ridgeNormalProjection R p ⁻¹' S))
    (hboundary : p ∈ frontier (g '' T7))
    (hright : SectorAngleSum.HasSectorAngle S (Real.pi/2)) :
    g.symm p ∈ integerSkeleton 7 ∧
    ∃ i j : Fin 7, ∃ b c : Bool, i ≠ j ∧
      i ∈ carrierCriticalAxes (g.symm p) ∧ j ∈ carrierCriticalAxes (g.symm p) ∧
      carrierLinearCone (g.symm p) = carrierAxisHalfspace i b ∩ carrierAxisHalfspace j c ∧
      S = (fun v : R.directionᗮ => g.symm.toRealAffineIsometryEquiv.linearIsometryEquiv
        (v : Point 7)) ⁻¹' (carrierAxisHalfspace i b ∩ carrierAxisHalfspace j c) := by
  have hc := T7_right_angle_normal_cone_carrier_germ g R hp hcodim hactive hS hmodel hboundary hright
  obtain ⟨i,j,b,c,hij,hi,hj,hC,hS'⟩ := right_angle_carrier_germ_coordinate_quadrant
    g.symm.toRealAffineIsometryEquiv R hp hcodim (fun j hj => hactive (.inl j) hj)
    hS hmodel (by simpa only [inverse_frame_carrier_preimage] using hc) hright
  exact ⟨mem_integerSkeleton_of_two_critical_axes (g.symm p) i j hij hi hj,i,j,b,c,hij,hi,hj,hC,hS'⟩

#print axioms T7_right_angle_normal_cone_coordinate_quadrant
#print axioms IsCarrierCoordinateCone.right_angle_quadrant
#print axioms right_angle_carrier_germ_coordinate_quadrant
#print axioms mem_integerSkeleton_of_two_critical_axes
end SparseMonotiles
