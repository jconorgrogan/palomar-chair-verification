module

public import SpectreGeometry.PolygonProductKeyGenericRidgeSectors
public import SpectreGeometry.PolygonProductKeyNormalAngles
public import SpectreGeometry.LocalConeGerm
public import SpectreGeometry.NormalPlaneSectorMeasure

@[expose] public section


/-!
# Literal material-cone masses at actual product-key ridges

The four local cones below are derived from actual-body sector neighborhoods
and the actual incident-plane equations. Positive base ridges are unions,
negative base ridges intersections, positive side ridges intersections, and
negative side ridges unions. Their angular masses are computed using literal
cosine/sine directions in an arbitrary isometric two-plane chart containing
both computed normals. These range assumptions remain explicit; no normal
span, sector classification, or cone-germ hypothesis is assumed.
-/

namespace SpectreGeometry.ProductCrease
open SpectreGeometry PhysicalRegistration Set MeasureTheory InnerProductGeometry
open scoped InnerProductSpace
noncomputable section

/-- The reentrant material cone at a positive-label base ridge. -/
def basePositiveMaterialCone (u : ProductKeySite) (b : ProductKeySide) : Set EFour :=
  {v | inner ℝ (productKeyOutwardNormal u) v ≤ 0 ∨
    inner ℝ (productKeySideNormal u b) v ≤ 0}

/-- The convex material cone at a negative-label base ridge. -/
def baseNegativeMaterialCone (u : ProductKeySite) (b : ProductKeySide) : Set EFour :=
  {v | inner ℝ (productKeyOutwardNormal u) v ≤ 0 ∧
    inner ℝ (productKeySideNormal u b) v ≤ 0}

/-- The convex material cone at a positive-label side ridge. -/
def sidePositiveMaterialCone (u : ProductKeySite) (b c : ProductKeySide) : Set EFour :=
  {v | inner ℝ (productKeySideNormal u b) v ≤ 0 ∧
    inner ℝ (productKeySideNormal u c) v ≤ 0}

/-- The reentrant material cone at a negative-label side ridge. -/
def sideNegativeMaterialCone (u : ProductKeySite) (b c : ProductKeySide) : Set EFour :=
  {v | inner ℝ (productKeySideNormal u b) v ≤ 0 ∨
    inner ℝ (productKeySideNormal u c) v ≤ 0}

/-- Literal directions in a displacement cone, in the given isometric chart. -/
def materialConeDirections (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour)
    (C : Set EFour) : Set Real.Angle :=
  {θ | L (PlanarSectorMeasure.direction θ) ∈ C}

private theorem affine_halfspace_displacement_iff (x n o : EFour) (c : ℝ)
    (hx : inner ℝ n (x-o) = c) (v : EFour) :
    inner ℝ n (x+v-o) ≤ c ↔ inner ℝ n v ≤ 0 := by
  rw [add_sub_right_comm, inner_add_right, hx]
  exact add_le_iff_nonpos_right c

private theorem localConeGerm_of_affine_union (S U : Set EFour)
    (x o n m : EFour) (c d : ℝ) (hU : IsOpen U) (hxU : x ∈ U)
    (hn : inner ℝ n (x-o) = c) (hm : inner ℝ m (x-o) = d)
    (he : ∀ y ∈ U, y ∈ S ↔ inner ℝ n (y-o) ≤ c ∨ inner ℝ m (y-o) ≤ d) :
    LocalConeGerm S x {v | inner ℝ n v ≤ 0 ∨ inner ℝ m v ≤ 0} := by
  refine ⟨(fun v : EFour => x+v) ⁻¹' U,
    hU.preimage (continuous_const.add continuous_id), by simpa using hxU, ?_⟩
  intro v hv
  rw [he (x+v) hv]
  exact or_congr (affine_halfspace_displacement_iff x n o c hn v)
    (affine_halfspace_displacement_iff x m o d hm v)

private theorem localConeGerm_of_affine_inter (S U : Set EFour)
    (x o n m : EFour) (c d : ℝ) (hU : IsOpen U) (hxU : x ∈ U)
    (hn : inner ℝ n (x-o) = c) (hm : inner ℝ m (x-o) = d)
    (he : ∀ y ∈ U, y ∈ S ↔ inner ℝ n (y-o) ≤ c ∧ inner ℝ m (y-o) ≤ d) :
    LocalConeGerm S x {v | inner ℝ n v ≤ 0 ∧ inner ℝ m v ≤ 0} := by
  refine ⟨(fun v : EFour => x+v) ⁻¹' U,
    hU.preimage (continuous_const.add continuous_id), by simpa using hxU, ?_⟩
  intro v hv
  rw [he (x+v) hv]
  exact and_congr (affine_halfspace_displacement_iff x n o c hn v)
    (affine_halfspace_displacement_iff x m o d hm v)

/-- The actual positive base ridge gives the union displacement germ. -/
theorem baseGeneric_local_cone_pos (u : ProductKeySite) (b : ProductKeySide)
    (x : EFour) (hx : x ∈ baseGeneric u b) (ha : 0 < (productKeySignedLabel u : ℝ)) :
    LocalConeGerm polygonProductKeyBody x (basePositiveMaterialCone u b) := by
  obtain ⟨U, hU, hxU, he⟩ := baseGeneric_local_sector_pos u b x hx ha
  exact localConeGerm_of_affine_union _ U x (productKeyCenter u)
    (productKeyOutwardNormal u) (productKeySideNormal u b) 0
    (productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN)
    hU hxU hx.1.2 (product_key_side_face_plane u b x hx.1.1) he

/-- The actual negative base ridge gives the intersection displacement germ. -/
theorem baseGeneric_local_cone_neg (u : ProductKeySite) (b : ProductKeySide)
    (x : EFour) (hx : x ∈ baseGeneric u b) (ha : (productKeySignedLabel u : ℝ) < 0) :
    LocalConeGerm polygonProductKeyBody x (baseNegativeMaterialCone u b) := by
  obtain ⟨U, hU, hxU, he⟩ := baseGeneric_local_sector_neg u b x hx ha
  exact localConeGerm_of_affine_inter _ U x (productKeyCenter u)
    (productKeyOutwardNormal u) (productKeySideNormal u b) 0
    (productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN)
    hU hxU hx.1.2 (product_key_side_face_plane u b x hx.1.1) he

/-- The actual positive side ridge gives the intersection displacement germ. -/
theorem sideGeneric_local_cone_pos (u : ProductKeySite) (b c : ProductKeySide)
    (x : EFour) (hx : x ∈ sideGeneric u b c) (ha : 0 < (productKeySignedLabel u : ℝ)) :
    LocalConeGerm polygonProductKeyBody x (sidePositiveMaterialCone u b c) := by
  obtain ⟨U, hU, hxU, he⟩ := sideGeneric_local_sector_pos u b c x hx ha
  exact localConeGerm_of_affine_inter _ U x (productKeyCenter u)
    (productKeySideNormal u b) (productKeySideNormal u c)
    (productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN)
    (productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN)
    hU hxU (product_key_side_face_plane u b x hx.1.1)
    (product_key_side_face_plane u c x hx.1.2) he

/-- The actual negative side ridge gives the union displacement germ. -/
theorem sideGeneric_local_cone_neg (u : ProductKeySite) (b c : ProductKeySide)
    (x : EFour) (hx : x ∈ sideGeneric u b c) (ha : (productKeySignedLabel u : ℝ) < 0) :
    LocalConeGerm polygonProductKeyBody x (sideNegativeMaterialCone u b c) := by
  obtain ⟨U, hU, hxU, he⟩ := sideGeneric_local_sector_neg u b c x hx ha
  exact localConeGerm_of_affine_union _ U x (productKeyCenter u)
    (productKeySideNormal u b) (productKeySideNormal u c)
    (productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN)
    (productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN)
    hU hxU (product_key_side_face_plane u b x hx.1.1)
    (product_key_side_face_plane u c x hx.1.2) he

private theorem outward_ne_zero (u : ProductKeySite) : productKeyOutwardNormal u ≠ 0 := by
  intro h
  have hn := productKeyOutwardNormal_norm u
  rw [h, norm_zero] at hn
  norm_num at hn

private theorem side_ne_zero (u : ProductKeySite) (b : ProductKeySide) :
    productKeySideNormal u b ≠ 0 := by
  intro h
  have hn := product_key_side_normal_inner_outward u b
  rw [h, inner_zero_left] at hn
  norm_num at hn

private theorem base_angle_lt_pi (u : ProductKeySite) (b : ProductKeySide) :
    angle (productKeySideNormal u b) (productKeyOutwardNormal u) < Real.pi := by
  linarith [(product_key_base_normal_angle u b).2, Real.pi_pos]

private theorem side_angle_lt_pi (u : ProductKeySite) (b c : ProductKeySide)
    (hbc : b.1 ≠ c.1) :
    angle (productKeySideNormal u b) (productKeySideNormal u c) < Real.pi := by
  linarith [(product_key_side_normal_angle u b c hbc).2, Real.pi_pos]

/-- Positive base mass is π plus the actual computed base-normal angle. -/
theorem basePositiveMaterialCone_angular_mass (u : ProductKeySite) (b : ProductKeySide)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour)
    (hSide : productKeySideNormal u b ∈ Set.range L)
    (hOut : productKeyOutwardNormal u ∈ Set.range L) :
    volume (materialConeDirections L (basePositiveMaterialCone u b)) =
      ENNReal.ofReal (Real.pi + angle (productKeySideNormal u b) (productKeyOutwardNormal u)) := by
  have he : materialConeDirections L (basePositiveMaterialCone u b) =
      sectorHalfplane L (productKeySideNormal u b) ∪
        sectorHalfplane L (productKeyOutwardNormal u) := by
    ext θ
    exact or_comm
  rw [he]
  exact volume_sectorHalfplane_union L (side_ne_zero u b) (outward_ne_zero u)
    hSide hOut (base_angle_lt_pi u b)

/-- Negative base mass is π minus the actual computed base-normal angle. -/
theorem baseNegativeMaterialCone_angular_mass (u : ProductKeySite) (b : ProductKeySide)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour)
    (hSide : productKeySideNormal u b ∈ Set.range L)
    (hOut : productKeyOutwardNormal u ∈ Set.range L) :
    volume (materialConeDirections L (baseNegativeMaterialCone u b)) =
      ENNReal.ofReal (Real.pi - angle (productKeySideNormal u b) (productKeyOutwardNormal u)) := by
  have he : materialConeDirections L (baseNegativeMaterialCone u b) =
      sectorHalfplane L (productKeySideNormal u b) ∩
        sectorHalfplane L (productKeyOutwardNormal u) := by
    ext θ
    exact and_comm
  rw [he]
  exact volume_sectorHalfplane_inter L (side_ne_zero u b) (outward_ne_zero u)
    hSide hOut (base_angle_lt_pi u b)

/-- Positive side mass is π minus the actual computed side-normal angle. -/
theorem sidePositiveMaterialCone_angular_mass (u : ProductKeySite) (b c : ProductKeySide)
    (hbc : b.1 ≠ c.1) (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour)
    (hb : productKeySideNormal u b ∈ Set.range L)
    (hc : productKeySideNormal u c ∈ Set.range L) :
    volume (materialConeDirections L (sidePositiveMaterialCone u b c)) =
      ENNReal.ofReal (Real.pi - angle (productKeySideNormal u b) (productKeySideNormal u c)) := by
  exact volume_sectorHalfplane_inter L (side_ne_zero u b) (side_ne_zero u c)
    hb hc (side_angle_lt_pi u b c hbc)

/-- Negative side mass is π plus the actual computed side-normal angle. -/
theorem sideNegativeMaterialCone_angular_mass (u : ProductKeySite) (b c : ProductKeySide)
    (hbc : b.1 ≠ c.1) (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour)
    (hb : productKeySideNormal u b ∈ Set.range L)
    (hc : productKeySideNormal u c ∈ Set.range L) :
    volume (materialConeDirections L (sideNegativeMaterialCone u b c)) =
      ENNReal.ofReal (Real.pi + angle (productKeySideNormal u b) (productKeySideNormal u c)) := by
  exact volume_sectorHalfplane_union L (side_ne_zero u b) (side_ne_zero u c)
    hb hc (side_angle_lt_pi u b c hbc)

/-- The actual signed-label choice, with its base union/intersection polarity. -/
def baseMaterialCone (u : ProductKeySite) (b : ProductKeySide) : Set EFour :=
  if 0 < (productKeySignedLabel u : ℝ) then basePositiveMaterialCone u b
  else baseNegativeMaterialCone u b

/-- The actual signed-label choice, with its side intersection/union polarity. -/
def sideMaterialCone (u : ProductKeySite) (b c : ProductKeySide) : Set EFour :=
  if 0 < (productKeySignedLabel u : ℝ) then sidePositiveMaterialCone u b c
  else sideNegativeMaterialCone u b c

def baseMaterialAngle (u : ProductKeySite) (b : ProductKeySide) : ℝ :=
  if 0 < (productKeySignedLabel u : ℝ) then
    Real.pi + angle (productKeySideNormal u b) (productKeyOutwardNormal u)
  else Real.pi - angle (productKeySideNormal u b) (productKeyOutwardNormal u)

def sideMaterialAngle (u : ProductKeySite) (b c : ProductKeySide) : ℝ :=
  if 0 < (productKeySignedLabel u : ℝ) then
    Real.pi - angle (productKeySideNormal u b) (productKeySideNormal u c)
  else Real.pi + angle (productKeySideNormal u b) (productKeySideNormal u c)

private theorem label_neg_of_not_pos (u : ProductKeySite)
    (h : ¬0 < (productKeySignedLabel u : ℝ)) : (productKeySignedLabel u : ℝ) < 0 := by
  have hn : (productKeySignedLabel u : ℝ) ≠ 0 := by
    exact_mod_cast productKeySignedLabel_ne_zero u
  exact lt_of_le_of_ne (le_of_not_gt h) hn

theorem baseGeneric_local_cone (u : ProductKeySite) (b : ProductKeySide)
    (x : EFour) (hx : x ∈ baseGeneric u b) :
    LocalConeGerm polygonProductKeyBody x (baseMaterialCone u b) := by
  by_cases ha : 0 < (productKeySignedLabel u : ℝ)
  · simpa only [baseMaterialCone, if_pos ha] using baseGeneric_local_cone_pos u b x hx ha
  · simpa only [baseMaterialCone, if_neg ha] using
      baseGeneric_local_cone_neg u b x hx (label_neg_of_not_pos u ha)

theorem sideGeneric_local_cone (u : ProductKeySite) (b c : ProductKeySide)
    (x : EFour) (hx : x ∈ sideGeneric u b c) :
    LocalConeGerm polygonProductKeyBody x (sideMaterialCone u b c) := by
  by_cases ha : 0 < (productKeySignedLabel u : ℝ)
  · simpa only [sideMaterialCone, if_pos ha] using sideGeneric_local_cone_pos u b c x hx ha
  · simpa only [sideMaterialCone, if_neg ha] using
      sideGeneric_local_cone_neg u b c x hx (label_neg_of_not_pos u ha)

theorem baseMaterialCone_angular_mass (u : ProductKeySite) (b : ProductKeySide)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour)
    (hSide : productKeySideNormal u b ∈ Set.range L)
    (hOut : productKeyOutwardNormal u ∈ Set.range L) :
    volume (materialConeDirections L (baseMaterialCone u b)) = ENNReal.ofReal (baseMaterialAngle u b) := by
  by_cases ha : 0 < (productKeySignedLabel u : ℝ)
  · simpa only [baseMaterialCone, baseMaterialAngle, if_pos ha] using
      basePositiveMaterialCone_angular_mass u b L hSide hOut
  · simpa only [baseMaterialCone, baseMaterialAngle, if_neg ha] using
      baseNegativeMaterialCone_angular_mass u b L hSide hOut

theorem sideMaterialCone_angular_mass (u : ProductKeySite) (b c : ProductKeySide)
    (hbc : b.1 ≠ c.1) (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour)
    (hb : productKeySideNormal u b ∈ Set.range L)
    (hc : productKeySideNormal u c ∈ Set.range L) :
    volume (materialConeDirections L (sideMaterialCone u b c)) =
      ENNReal.ofReal (sideMaterialAngle u b c) := by
  by_cases ha : 0 < (productKeySignedLabel u : ℝ)
  · simpa only [sideMaterialCone, sideMaterialAngle, if_pos ha] using
      sidePositiveMaterialCone_angular_mass u b c hbc L hb hc
  · simpa only [sideMaterialCone, sideMaterialAngle, if_neg ha] using
      sideNegativeMaterialCone_angular_mass u b c hbc L hb hc

/-- Actual base material angles lie strictly near π and are never flat. -/
theorem baseMaterialAngle_bounds (u : ProductKeySite) (b : ProductKeySide) :
    11 * Real.pi / 12 < baseMaterialAngle u b ∧
      baseMaterialAngle u b < 13 * Real.pi / 12 ∧ baseMaterialAngle u b ≠ Real.pi := by
  rcases product_key_base_normal_angle u b with ⟨ha0, ha12⟩
  unfold baseMaterialAngle
  split_ifs <;> refine ⟨?_, ?_, ?_⟩ <;> linarith [Real.pi_pos]

/-- Actual distinct-axis side material angles lie strictly near π and are never flat. -/
theorem sideMaterialAngle_bounds (u : ProductKeySite) (b c : ProductKeySide)
    (hbc : b.1 ≠ c.1) :
    11 * Real.pi / 12 < sideMaterialAngle u b c ∧
      sideMaterialAngle u b c < 13 * Real.pi / 12 ∧ sideMaterialAngle u b c ≠ Real.pi := by
  rcases product_key_side_normal_angle u b c hbc with ⟨ha0, ha12⟩
  unfold sideMaterialAngle
  split_ifs <;> refine ⟨?_, ?_, ?_⟩ <;> linarith [Real.pi_pos]

private theorem real_mass_and_nonflat {s : Set Real.Angle} {a : ℝ}
    (hMass : volume s = ENNReal.ofReal a)
    (hLower : 11 * Real.pi / 12 < a) (hNe : a ≠ Real.pi) :
    (volume s).toReal = a ∧ volume s ≠ ENNReal.ofReal Real.pi := by
  have ha : 0 ≤ a := by linarith [Real.pi_pos]
  constructor
  · rw [hMass, ENNReal.toReal_ofReal ha]
  · intro h
    apply hNe
    have he := congrArg ENNReal.toReal (hMass.symm.trans h)
    simpa only [ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal Real.pi_pos.le] using he

/-- End-to-end actual-base endpoint: full local material germ, literal angular
mass in the supplied two-plane, strict near-π bounds, and nonflat measured mass.
Both computed-normal range hypotheses are deliberately exposed. -/
theorem baseGeneric_local_cone_angular_mass (u : ProductKeySite) (b : ProductKeySide)
    (x : EFour) (hx : x ∈ baseGeneric u b)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour)
    (hSide : productKeySideNormal u b ∈ Set.range L)
    (hOut : productKeyOutwardNormal u ∈ Set.range L) :
    LocalConeGerm polygonProductKeyBody x (baseMaterialCone u b) ∧
    volume (materialConeDirections L (baseMaterialCone u b)) = ENNReal.ofReal (baseMaterialAngle u b) ∧
    (volume (materialConeDirections L (baseMaterialCone u b))).toReal = baseMaterialAngle u b ∧
    11 * Real.pi / 12 < (volume (materialConeDirections L (baseMaterialCone u b))).toReal ∧
    (volume (materialConeDirections L (baseMaterialCone u b))).toReal < 13 * Real.pi / 12 ∧
    volume (materialConeDirections L (baseMaterialCone u b)) ≠ ENNReal.ofReal Real.pi := by
  have hm := baseMaterialCone_angular_mass u b L hSide hOut
  have hb := baseMaterialAngle_bounds u b
  have hr := real_mass_and_nonflat hm hb.1 hb.2.2
  refine ⟨baseGeneric_local_cone u b x hx, hm, hr.1, ?_, ?_, hr.2⟩
  · rw [hr.1]; exact hb.1
  · rw [hr.1]; exact hb.2.1

/-- End-to-end actual-side endpoint, with the actual distinct-axis premise and
both computed normals explicitly required to lie in the isometric chart. -/
theorem sideGeneric_local_cone_angular_mass (u : ProductKeySite) (b c : ProductKeySide)
    (hbc : b.1 ≠ c.1) (x : EFour) (hx : x ∈ sideGeneric u b c)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour)
    (hb : productKeySideNormal u b ∈ Set.range L)
    (hc : productKeySideNormal u c ∈ Set.range L) :
    LocalConeGerm polygonProductKeyBody x (sideMaterialCone u b c) ∧
    volume (materialConeDirections L (sideMaterialCone u b c)) = ENNReal.ofReal (sideMaterialAngle u b c) ∧
    (volume (materialConeDirections L (sideMaterialCone u b c))).toReal = sideMaterialAngle u b c ∧
    11 * Real.pi / 12 < (volume (materialConeDirections L (sideMaterialCone u b c))).toReal ∧
    (volume (materialConeDirections L (sideMaterialCone u b c))).toReal < 13 * Real.pi / 12 ∧
    volume (materialConeDirections L (sideMaterialCone u b c)) ≠ ENNReal.ofReal Real.pi := by
  have hm := sideMaterialCone_angular_mass u b c hbc L hb hc
  have ha := sideMaterialAngle_bounds u b c hbc
  have hr := real_mass_and_nonflat hm ha.1 ha.2.2
  refine ⟨sideGeneric_local_cone u b c x hx, hm, hr.1, ?_, ?_, hr.2⟩
  · rw [hr.1]; exact ha.1
  · rw [hr.1]; exact ha.2.1

end
end SpectreGeometry.ProductCrease
