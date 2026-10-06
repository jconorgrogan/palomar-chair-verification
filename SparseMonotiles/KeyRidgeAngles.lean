module

public import SparseMonotiles.ActivePhysicalKeyModelInventory
public import SparseMonotiles.KeySlackNormals
public import SparseMonotiles.NormalSpaceGeometry
public import SparseMonotiles.CarrierRidgeAngles

@[expose] public section

/-!
# Actual key boundary models have the certified sector angles

Every supporting form below belongs to the literal key, transported by its
arbitrary physical frame. The two-plane shapes come from the active material
inventory; normal-space restriction preserves their actual Euclidean angles.
-/
namespace SparseMonotiles

open Set InnerProductGeometry NormalSpaceGeometry

/-- Active closed key-model syntax commutes with a change of coordinates. -/
theorem IsActiveKeyRidgeModel.preimage {n : ℕ}
    (slack : PyramidHalfspaceIndex n → Point (n+1) → ℝ) (b : Bool)
    (f : Point (n+1) → Point (n+1)) (p : Point (n+1)) {M : Set (Point (n+1))}
    (h : IsActiveKeyRidgeModel slack b (f p) M) :
    IsActiveKeyRidgeModel (fun j x => slack j (f x)) b p (f ⁻¹' M) := by
  rcases h with ⟨hz, heq⟩ | ⟨i, si, hz, heq⟩ |
    ⟨i, si, h0, hi, heq⟩ | ⟨i, j, si, sj, hij, hi, hj, heq⟩
  · refine Or.inl ⟨hz, ?_⟩
    rw [heq]; cases b <;> rfl
  · refine Or.inr (Or.inl ⟨i, si, hz, ?_⟩)
    rw [heq]; cases b <;> rfl
  · refine Or.inr (Or.inr (Or.inl ⟨i, si, h0, hi, ?_⟩))
    rw [heq]; cases b <;> rfl
  · refine Or.inr (Or.inr (Or.inr ⟨i, j, si, sj, hij, hi, hj, ?_⟩))
    rw [heq]; cases b <;> rfl

private theorem normal_model_sector_angle_transfer
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (R : AffineSubspace ℝ E) (p : E) {T : Set E} {S Q : Set R.directionᗮ}
    (hS : IsPositiveCone S)
    (hmodel : LocalSetEq p T (ridgeNormalProjection R p ⁻¹' S))
    (hQ : LocalSetEq p T (ridgeNormalProjection R p ⁻¹' Q))
    {θ : ℝ} (hangle : SectorAngleSum.HasSectorAngle Q θ)
    (hinv : SectorArithmetic.InAngleInventory θ) :
    SectorAngleSum.HasSectorAngle S θ ∧ SectorArithmetic.InAngleInventory θ := by
  have heq := normalCones_eq_of_localSetEq R p hS hangle.positive (hmodel.symm.trans hQ)
  exact ⟨heq.symm ▸ hangle, hinv⟩

/-- Every selected active key facet yields its actual nonzero restricted inward
normal and both exact closed halfspace orientations. -/
theorem key_facet_normal_space_adapter {n : ℕ} (k : KeyData (n+1))
    (hd : ∀ i b, 0 < keySideDistance k i b)
    (e : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1))
    (R : AffineSubspace ℝ (Point (n+1))) {p : Point (n+1)} (hp : p ∈ R)
    (a : PyramidFacetIndex n)
    (hzero : ∀ x ∈ R, keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex a) (e x) = 0) :
    ∃ nR : R.directionᗮ,
      (nR : Point (n+1)) = keyWorldInwardNormal k e a ∧ nR ≠ 0 ∧
      {x | 0 ≤ keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex a) (e x)} =
        ridgeNormalProjection R p ⁻¹' SectorAngleSum.normalHalfspace nR ∧
      {x | keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex a) (e x) ≤ 0} =
        ridgeNormalProjection R p ⁻¹' SectorAngleSum.normalHalfspace (-nR) := by
  obtain ⟨nR, hnR, hne, _, _, hpos, hneg⟩ :=
    active_supporting_slack_adapter R hp
      (fun x => keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex a) (e x))
      (keyWorldInwardNormal k e a) (keyWorldInwardNormal_ne_zero k e a)
      (keyFacetScale_pos k hd a)
      (fun x => key_facet_world_slack_difference k hd e a x p) hzero
  exact ⟨nR, hnR, hne, hpos, hneg⟩

/-- The two inward normals of a base--side convex model retain the literal
canonical base-crease deviation in every world frame. -/
theorem key_world_base_side_normal_angle {n : ℕ} (k : KeyData (n+1))
    (e : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) (i : Fin n) (b : Bool)
    (hs : 0 ≤ keySideSlope k i b) :
    angle (keyWorldInwardNormal k e none) (-keyWorldInwardNormal k e (some (i,b))) =
      baseCreaseDeviation (keySideSlope k i b) := by
  change angle (e.linearIsometryEquiv.symm (-pyramidBaseNormal n))
    (-e.linearIsometryEquiv.symm (-pyramidSlopeNormal i b (keySideSlope k i b))) = _
  rw [← map_neg, neg_neg]
  exact (e.linearIsometryEquiv.symm.toLinearIsometry.angle_map _ _).trans
    (SectorAngleSum.base_side_inward_angle i b (keySideSlope k i b) hs)

/-- The two inward side normals have the literal canonical side deviation. -/
theorem key_world_side_side_normal_angle {n : ℕ} (k : KeyData (n+1))
    (e : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) (i j : Fin n) (hij : i ≠ j)
    (b c : Bool) :
    angle (keyWorldInwardNormal k e (some (i,b))) (keyWorldInwardNormal k e (some (j,c))) =
      sideCreaseDeviation (keySideSlope k i b) (keySideSlope k j c) := by
  change angle (e.linearIsometryEquiv.symm (-pyramidSlopeNormal i b (keySideSlope k i b)))
    (e.linearIsometryEquiv.symm (-pyramidSlopeNormal j c (keySideSlope k j c))) = _
  exact (e.linearIsometryEquiv.symm.toLinearIsometry.angle_map _ _).trans
    ((angle_neg_neg _ _).trans (SectorAngleSum.side_side_inward_angle i j hij b c _ _))

/-- Either closed orientation of an actual active key facet has width π. -/
theorem key_facet_halfspace_normal_model_sector_angle {n : ℕ} (k : KeyData (n+1))
    (hd : ∀ i b, 0 < keySideDistance k i b)
    (e : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1))
    (R : AffineSubspace ℝ (Point (n+1))) {p : Point (n+1)} (hp : p ∈ R)
    (a : PyramidFacetIndex n)
    (hzero : ∀ x ∈ R, keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex a) (e x) = 0)
    (positive : Bool) {T : Set (Point (n+1))} {S : Set R.directionᗮ}
    (hS : IsPositiveCone S)
    (hmodel : LocalSetEq p T (ridgeNormalProjection R p ⁻¹' S))
    (hlocal : LocalSetEq p T (if positive then
      {x | 0 ≤ keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex a) (e x)} else
      {x | keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex a) (e x) ≤ 0})) :
    SectorAngleSum.HasSectorAngle S Real.pi ∧ SectorArithmetic.InAngleInventory Real.pi := by
  obtain ⟨nR, _, hn, hpos, hneg⟩ := key_facet_normal_space_adapter k hd e R hp a hzero
  cases positive
  · change LocalSetEq p T {x | keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex a) (e x) ≤ 0}
      at hlocal
    rw [hneg] at hlocal
    have hi := SectorAngleSum.halfplane_angle_inventory (-nR) (neg_ne_zero.mpr hn)
    exact normal_model_sector_angle_transfer R p hS hmodel hlocal hi.1 hi.2
  · change LocalSetEq p T {x | 0 ≤ keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex a) (e x)}
      at hlocal
    rw [hpos] at hlocal
    have hi := SectorAngleSum.halfplane_angle_inventory nR hn
    exact normal_model_sector_angle_transfer R p hS hmodel hlocal hi.1 hi.2

/-- Pair-specific base--side endpoint: the distinguished actual crease keeps
its exact nonflat width, π+δ for a bump and π−δ for a dent. -/
theorem key_base_side_normal_model_sector_angle {n : ℕ} (k : KeyData (n+1))
    (hd : ∀ i b, 0 < keySideDistance k i b)
    (e : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1))
    (R : AffineSubspace ℝ (Point (n+1))) {p : Point (n+1)} (hp : p ∈ R)
    (i : Fin n) (si : Bool)
    (hslope : 0 < keySideSlope k i si ∧ keySideSlope k i si ≤ 1/2)
    (hbase : ∀ x ∈ R, keyPyramidHalfspaceSlack k (.inl false) (e x) = 0)
    (hside : ∀ x ∈ R, keyPyramidHalfspaceSlack k (.inr (i,si)) (e x) = 0)
    (b : Bool) {T : Set (Point (n+1))} {S : Set R.directionᗮ}
    (hS : IsPositiveCone S)
    (hmodel : LocalSetEq p T (ridgeNormalProjection R p ⁻¹' S))
    (hlocal : LocalSetEq p T (closedBaseSideWedge
      (fun j x => keyPyramidHalfspaceSlack k j (e x)) (.inl false) (.inr (i,si)) b)) :
    (SectorAngleSum.HasSectorAngle S (if b then Real.pi + baseCreaseDeviation (keySideSlope k i si)
      else Real.pi - baseCreaseDeviation (keySideSlope k i si)) ∧
    SectorArithmetic.InAngleInventory (if b then Real.pi + baseCreaseDeviation (keySideSlope k i si)
      else Real.pi - baseCreaseDeviation (keySideSlope k i si))) ∧
    0 < baseCreaseDeviation (keySideSlope k i si) ∧
      baseCreaseDeviation (keySideSlope k i si) < Real.pi/4 := by
  obtain ⟨nb, hnb, hneb, hbpos, hbneg⟩ := key_facet_normal_space_adapter k hd e R hp none hbase
  obtain ⟨ns, hns, hnes, hspos, hsneg⟩ :=
    key_facet_normal_space_adapter k hd e R hp (some (i,si)) hside
  simp only [pyramidFacetHalfspaceIndex] at hbpos hbneg hspos hsneg
  have ha : angle nb (-ns) = baseCreaseDeviation (keySideSlope k i si) := by
    rw [← R.directionᗮ.angle_coe nb (-ns)]
    change angle (nb : Point (n+1)) (-(ns : Point (n+1))) = _
    rw [hnb, hns]
    exact key_world_base_side_normal_angle k e i si hslope.1.le
  have hb := baseCreaseDeviation_bounds (keySideSlope k i si) hslope.1 hslope.2
  refine ⟨?_, hb⟩
  cases b
  · change LocalSetEq p T
      ({x | 0 ≤ keyPyramidHalfspaceSlack k (.inl false) (e x)} ∩
       {x | keyPyramidHalfspaceSlack k (.inr (i,si)) (e x) ≤ 0}) at hlocal
    rw [hbpos, hsneg, ← preimage_inter] at hlocal
    have hi := SectorAngleSum.small_normal_angle_inventory nb (-ns) hneb
      (neg_ne_zero.mpr hnes) (by rw [ha]; exact hb.1) (by rw [ha]; exact hb.2)
    rw [ha] at hi
    exact normal_model_sector_angle_transfer R p hS hmodel hlocal hi.1.1 hi.1.2
  · change LocalSetEq p T
      ({x | keyPyramidHalfspaceSlack k (.inl false) (e x) ≤ 0} ∪
       {x | 0 ≤ keyPyramidHalfspaceSlack k (.inr (i,si)) (e x)}) at hlocal
    rw [hbneg, hspos, ← preimage_union] at hlocal
    have ha' : angle (-nb) ns = baseCreaseDeviation (keySideSlope k i si) := by
      have he : angle (-nb) ns = angle nb (-ns) := by simpa using angle_neg_neg nb (-ns)
      exact he.trans ha
    have hi := SectorAngleSum.small_normal_angle_inventory (-nb) ns
      (neg_ne_zero.mpr hneb) hnes (by rw [ha']; exact hb.1) (by rw [ha']; exact hb.2)
    rw [ha'] at hi
    exact normal_model_sector_angle_transfer R p hS hmodel hlocal hi.2.1 hi.2.2

/-- Pair-specific distinct-side endpoint: the distinguished actual crease keeps
its exact nonflat width, π−δ for a bump and π+δ for a dent. -/
theorem key_side_side_normal_model_sector_angle {n : ℕ} (k : KeyData (n+1))
    (hd : ∀ i b, 0 < keySideDistance k i b)
    (e : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1))
    (R : AffineSubspace ℝ (Point (n+1))) {p : Point (n+1)} (hp : p ∈ R)
    (i j : Fin n) (hij : i ≠ j) (si sj : Bool)
    (hsi : 0 < keySideSlope k i si ∧ keySideSlope k i si ≤ 1/2)
    (hsj : 0 < keySideSlope k j sj ∧ keySideSlope k j sj ≤ 1/2)
    (hsidei : ∀ x ∈ R, keyPyramidHalfspaceSlack k (.inr (i,si)) (e x) = 0)
    (hsidej : ∀ x ∈ R, keyPyramidHalfspaceSlack k (.inr (j,sj)) (e x) = 0)
    (b : Bool) {T : Set (Point (n+1))} {S : Set R.directionᗮ}
    (hS : IsPositiveCone S)
    (hmodel : LocalSetEq p T (ridgeNormalProjection R p ⁻¹' S))
    (hlocal : LocalSetEq p T (closedSideSideWedge
      (fun a x => keyPyramidHalfspaceSlack k a (e x)) (.inr (i,si)) (.inr (j,sj)) b)) :
    (SectorAngleSum.HasSectorAngle S
      (if b then Real.pi - sideCreaseDeviation (keySideSlope k i si) (keySideSlope k j sj)
       else Real.pi + sideCreaseDeviation (keySideSlope k i si) (keySideSlope k j sj)) ∧
    SectorArithmetic.InAngleInventory
      (if b then Real.pi - sideCreaseDeviation (keySideSlope k i si) (keySideSlope k j sj)
       else Real.pi + sideCreaseDeviation (keySideSlope k i si) (keySideSlope k j sj))) ∧
    0 < sideCreaseDeviation (keySideSlope k i si) (keySideSlope k j sj) ∧
      sideCreaseDeviation (keySideSlope k i si) (keySideSlope k j sj) < Real.pi/4 := by
  obtain ⟨ni, hni, hnei, hipos, hineg⟩ :=
    key_facet_normal_space_adapter k hd e R hp (some (i,si)) hsidei
  obtain ⟨nj, hnj, hnej, hjpos, hjneg⟩ :=
    key_facet_normal_space_adapter k hd e R hp (some (j,sj)) hsidej
  simp only [pyramidFacetHalfspaceIndex] at hipos hineg hjpos hjneg
  have ha : angle ni nj = sideCreaseDeviation (keySideSlope k i si) (keySideSlope k j sj) := by
    rw [← R.directionᗮ.angle_coe ni nj]
    change angle (ni : Point (n+1)) (nj : Point (n+1)) = _
    rw [hni, hnj]
    exact key_world_side_side_normal_angle k e i j hij si sj
  have hb := sideCreaseDeviation_bounds (keySideSlope k i si) (keySideSlope k j sj)
    hsi.1 hsj.1 hsi.2 hsj.2
  refine ⟨?_, hb⟩
  cases b
  · change LocalSetEq p T
      ({x | keyPyramidHalfspaceSlack k (.inr (i,si)) (e x) ≤ 0} ∪
       {x | keyPyramidHalfspaceSlack k (.inr (j,sj)) (e x) ≤ 0}) at hlocal
    rw [hineg, hjneg, ← preimage_union] at hlocal
    have ha' : angle (-ni) (-nj) = sideCreaseDeviation (keySideSlope k i si) (keySideSlope k j sj) := by
      rw [angle_neg_neg, ha]
    have hi := SectorAngleSum.small_normal_angle_inventory (-ni) (-nj)
      (neg_ne_zero.mpr hnei) (neg_ne_zero.mpr hnej)
      (by rw [ha']; exact hb.1) (by rw [ha']; exact hb.2)
    rw [ha'] at hi
    exact normal_model_sector_angle_transfer R p hS hmodel hlocal hi.2.1 hi.2.2
  · change LocalSetEq p T
      ({x | 0 ≤ keyPyramidHalfspaceSlack k (.inr (i,si)) (e x)} ∩
       {x | 0 ≤ keyPyramidHalfspaceSlack k (.inr (j,sj)) (e x)}) at hlocal
    rw [hipos, hjpos, ← preimage_inter] at hlocal
    have hi := SectorAngleSum.small_normal_angle_inventory ni nj hnei hnej
      (by rw [ha]; exact hb.1) (by rw [ha]; exact hb.2)
    rw [ha] at hi
    exact normal_model_sector_angle_transfer R p hS hmodel hlocal hi.1.1 hi.1.2

/-- The complete actual nonconstant key-model inventory becomes a genuine
sector-angle inventory in the normal space. -/
theorem key_active_normal_model_sector_inventory {n : ℕ} (k : KeyData (n+1))
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
    ∃ θ, SectorAngleSum.HasSectorAngle S θ ∧ SectorArithmetic.InAngleInventory θ := by
  rcases hM with ⟨hz, heq⟩ | ⟨i, si, hz, heq⟩ |
    ⟨i, si, h0, hi, heq⟩ | ⟨i, j, si, sj, hij, hi, hj, heq⟩
  · rw [heq] at hlocal
    have h := key_facet_halfspace_normal_model_sector_angle k hd e R hp none
      (hactive _ hz) (!b) hS hmodel (by cases b <;> exact hlocal)
    exact ⟨Real.pi, h⟩
  · rw [heq] at hlocal
    have h := key_facet_halfspace_normal_model_sector_angle k hd e R hp (some (i,si))
      (hactive _ hz) b hS hmodel hlocal
    exact ⟨Real.pi, h⟩
  · rw [heq] at hlocal
    have h := key_base_side_normal_model_sector_angle k hd e R hp i si (hs i si)
      (hactive _ h0) (hactive _ hi) b hS hmodel hlocal
    exact ⟨_, h.1⟩
  · rw [heq] at hlocal
    have h := key_side_side_normal_model_sector_angle k hd e R hp i j hij si sj (hs i si) (hs j sj)
      (hactive _ hi) (hactive _ hj) b hS hmodel hlocal
    exact ⟨_, h.1⟩

private theorem image_isometry_eq_inverse_preimage {d : ℕ}
    (g : Point d ≃ᵢ Point d) (M : Set (Point d)) : g '' M = g.symm ⁻¹' M := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [mem_preimage, g.symm_apply_apply] using hy
  · intro hx
    exact ⟨g.symm x, hx, g.apply_symm_apply x⟩

/-- Every actual boundary normal cone of T5 has a proved geometric sector
angle in the allowed inventory, whether its germ comes from the carrier or a key. -/
theorem T5_boundary_normal_cone_sector_inventory
    (g : Point 5 ≃ᵢ Point 5) (R : AffineSubspace ℝ (Point 5))
    {p : Point 5} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 5)
    (hactive : ∀ j, T5WorldAffineFields g j p = 0 →
      R ≤ affineFormPlane (T5WorldAffineFields g j) 0)
    {S : Set R.directionᗮ} (hS : IsPositiveCone S)
    (hmodel : LocalSetEq p (g '' T5) (ridgeNormalProjection R p ⁻¹' S))
    (hboundary : p ∈ frontier (g '' T5)) :
    ∃ θ, SectorAngleSum.HasSectorAngle S θ ∧ SectorArithmetic.InAngleInventory θ := by
  rcases T5_generic_active_physical_key_model_inventory g R hcodim hp hactive hboundary with
    hcarrier | ⟨k, hk, q, M, hq, hzero, hM, hlocal⟩
  · obtain ⟨θ, hθ, _, hi⟩ :=
      T5_carrier_germ_sector_angle_inventory g R hp hcodim hactive hS hmodel hcarrier hboundary
    exact ⟨θ, hθ, hi⟩
  · let e : Point 5 ≃ᵃⁱ[ℝ] Point 5 := g.symm.toRealAffineIsometryEquiv.trans q.euclidean.symm
    have hMw := IsActiveKeyRidgeModel.preimage (Canonical.posedHalfspaceSlack5 q)
      k.bump g.symm p hM
    rw [image_isometry_eq_inverse_preimage g M] at hlocal
    exact key_active_normal_model_sector_inventory
      ((Canonical.referenceBox5 true).toKeyData 19200)
      Canonical.referenceSideDistance5_pos Canonical.referenceSideSlope5_bounds
      e R hp hzero k.bump hMw hS hmodel hlocal

/-- The corresponding complete actual boundary sector inventory for T7. -/
theorem T7_boundary_normal_cone_sector_inventory
    (g : Point 7 ≃ᵢ Point 7) (R : AffineSubspace ℝ (Point 7))
    {p : Point 7} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 7)
    (hactive : ∀ j, T7WorldAffineFields g j p = 0 →
      R ≤ affineFormPlane (T7WorldAffineFields g j) 0)
    {S : Set R.directionᗮ} (hS : IsPositiveCone S)
    (hmodel : LocalSetEq p (g '' T7) (ridgeNormalProjection R p ⁻¹' S))
    (hboundary : p ∈ frontier (g '' T7)) :
    ∃ θ, SectorAngleSum.HasSectorAngle S θ ∧ SectorArithmetic.InAngleInventory θ := by
  rcases T7_generic_active_physical_key_model_inventory g R hcodim hp hactive hboundary with
    hcarrier | ⟨k, hk, q, M, hq, hzero, hM, hlocal⟩
  · obtain ⟨θ, hθ, _, hi⟩ :=
      T7_carrier_germ_sector_angle_inventory g R hp hcodim hactive hS hmodel hcarrier hboundary
    exact ⟨θ, hθ, hi⟩
  · let e : Point 7 ≃ᵃⁱ[ℝ] Point 7 := g.symm.toRealAffineIsometryEquiv.trans q.euclidean.symm
    have hMw := IsActiveKeyRidgeModel.preimage (Canonical.posedHalfspaceSlack7 q)
      k.bump g.symm p hM
    rw [image_isometry_eq_inverse_preimage g M] at hlocal
    exact key_active_normal_model_sector_inventory
      ((Canonical.referenceBox7 true).toKeyData 188160)
      Canonical.referenceSideDistance7_pos Canonical.referenceSideSlope7_bounds
      e R hp hzero k.bump hMw hS hmodel hlocal

#print axioms key_facet_normal_space_adapter
#print axioms key_base_side_normal_model_sector_angle
#print axioms key_side_side_normal_model_sector_angle
#print axioms key_active_normal_model_sector_inventory
#print axioms T5_boundary_normal_cone_sector_inventory
#print axioms T7_boundary_normal_cone_sector_inventory

end SparseMonotiles
