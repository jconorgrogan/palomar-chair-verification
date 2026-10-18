module

public import PhysicalRegistration.PlanarSectorMeasure
public import PhysicalRegistration.TransversePlaneCoordinates
public import PhysicalRegistration.NativeDihedralAngles
public import PhysicalRegistration.ConicalFanRegularity

@[expose] public section

/-!
# Actual native key-sector angular masses

The direction sets are literal restrictions of the actual centered native
cones to the constructed root normal plane. Their masses are computed from
the Haar halfplane formulas, with every normal-span membership explicit or
derived from the actual incident boundary planes. No material-angle field or
angle-sum premise is introduced.
-/

namespace PhysicalRegistration.NativeChair
open scoped InnerProductSpace
open Set MeasureTheory
open TransversePlaneCoordinates
noncomputable section

/-- Actual directions of an ambient cone in the constructed root normal plane. -/
def transverseDirections {m : ℕ} (p q : Space m)
    (h : LinearIndependent ℝ ![p, q]) (C : Set (Space m)) : Set Real.Angle :=
  {θ | lift p q h (PlanarSectorMeasure.direction θ) ∈ C}

/-- The actual angular mass, expressed as a real number. -/
def transverseMass {m : ℕ} (p q : Space m)
    (h : LinearIndependent ℝ ![p, q]) (C : Set (Space m)) : ℝ :=
  (volume (transverseDirections p q h C)).toReal

theorem transverseDirections_halfspace {m : ℕ} (p q : Space m)
    (h : LinearIndependent ℝ ![p, q]) (n : Space m) (hn : n ∈ normalSpan p q) :
    transverseDirections p q h {z | ⟪n, z⟫_ℝ ≤ 0} =
      PlanarSectorMeasure.halfplane (normal p q h n hn) := by
  ext θ
  simp only [transverseDirections, PlanarSectorMeasure.halfplane, mem_ofPred_eq,
    inner_normal_lift p q h n hn]

theorem volume_transverseDirections_halfspace {m : ℕ} (p q : Space m)
    (h : LinearIndependent ℝ ![p, q]) (n : Space m)
    (hn : n ∈ normalSpan p q) (hn₀ : n ≠ 0) :
    volume (transverseDirections p q h {z | ⟪n, z⟫_ℝ ≤ 0}) =
      ENNReal.ofReal Real.pi := by
  rw [transverseDirections_halfspace p q h n hn]
  exact PlanarSectorMeasure.volume_halfplane (by simpa using hn₀)

theorem volume_transverseDirections_twoHalfspaceCone {m : ℕ} (p q : Space m)
    (h : LinearIndependent ℝ ![p, q]) (n w : Space m)
    (hn : n ∈ normalSpan p q) (hw : w ∈ normalSpan p q)
    (hn₀ : n ≠ 0) (hw₀ : w ≠ 0)
    (ha : InnerProductGeometry.angle n w < Real.pi) (b : Bool) :
    volume (transverseDirections p q h (twoHalfspaceCone n w b)) =
      ENNReal.ofReal (if b then Real.pi + InnerProductGeometry.angle n w
        else Real.pi - InnerProductGeometry.angle n w) := by
  have hnn : normal p q h n hn ≠ 0 := by simpa using hn₀
  have hwn : normal p q h w hw ≠ 0 := by simpa using hw₀
  have han : InnerProductGeometry.angle (normal p q h n hn) (normal p q h w hw) <
      Real.pi := by simpa using ha
  cases b
  · have heq : transverseDirections p q h (twoHalfspaceCone n w false) =
        PlanarSectorMeasure.halfplane (normal p q h n hn) ∩
          PlanarSectorMeasure.halfplane (normal p q h w hw) := by
      ext θ
      simp [transverseDirections, twoHalfspaceCone, PlanarSectorMeasure.halfplane,
        inner_normal_lift p q h n hn, inner_normal_lift p q h w hw]
    rw [heq, PlanarSectorMeasure.volume_halfplane_inter hnn hwn han]
    simp
  · have heq : transverseDirections p q h (twoHalfspaceCone n w true) =
        PlanarSectorMeasure.halfplane (normal p q h n hn) ∪
          PlanarSectorMeasure.halfplane (normal p q h w hw) := by
      ext θ
      simp [transverseDirections, twoHalfspaceCone, PlanarSectorMeasure.halfplane,
        inner_normal_lift p q h n hn, inner_normal_lift p q h w hw]
    rw [heq, PlanarSectorMeasure.volume_halfplane_union hnn hwn han]
    simp

theorem transverseMass_twoHalfspaceCone {m : ℕ} (p q : Space m)
    (h : LinearIndependent ℝ ![p, q]) (n w : Space m)
    (hn : n ∈ normalSpan p q) (hw : w ∈ normalSpan p q)
    (hn₀ : n ≠ 0) (hw₀ : w ≠ 0)
    (ha : InnerProductGeometry.angle n w < Real.pi) (b : Bool) :
    transverseMass p q h (twoHalfspaceCone n w b) =
      if b then Real.pi + InnerProductGeometry.angle n w
        else Real.pi - InnerProductGeometry.angle n w := by
  unfold transverseMass
  rw [volume_transverseDirections_twoHalfspaceCone p q h n w hn hw hn₀ hw₀ ha b,
    ENNReal.toReal_ofReal]
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · linarith
  · linarith [Real.pi_pos, InnerProductGeometry.angle_nonneg n w]

/-- A literal strict-branch key point has a flat material halfplane. -/
theorem transverseMass_strictSide {m J : ℕ} (a : Coefficients m J)
    (f : Space m ≃ᵢ Space m) (u : Site m) (s : Side m) (p q : Space m)
    (h : LinearIndependent ℝ ![p, q])
    (hn : placedNormal f (sideNormal a u s) ∈ normalSpan p q) :
    transverseMass p q h {z | ⟪placedNormal f (sideNormal a u s), z⟫_ℝ ≤ 0} = Real.pi := by
  unfold transverseMass
  rw [volume_transverseDirections_halfspace p q h _ hn (placed_sideNormal_ne_zero a f u s),
    ENNReal.toReal_ofReal Real.pi_pos.le]

/-- Exact base material mass, with its sign read from the native coefficient. -/
theorem transverseMass_base {m J : ℕ} (hm : 2 ≤ m) (a : Coefficients m J)
    (f : Space m ≃ᵢ Space m) (u : Site m) (s : Side m) (p q : Space m)
    (h : LinearIndependent ℝ ![p, q])
    (hn : placedNormal f (outward u.1) ∈ normalSpan p q)
    (hw : placedNormal f (sideNormal a u s) ∈ normalSpan p q) :
    transverseMass p q h (twoHalfspaceCone (placedNormal f (outward u.1))
      (placedNormal f (sideNormal a u s)) (decide (0 < (a.value u : ℝ)))) =
      if 0 < (a.value u : ℝ) then
        Real.pi + InnerProductGeometry.angle (placedNormal f (sideNormal a u s))
          (placedNormal f (outward u.1))
      else Real.pi - InnerProductGeometry.angle (placedNormal f (sideNormal a u s))
          (placedNormal f (outward u.1)) := by
  have hb := placed_base_normal_angle_bounds hm a u s f
  rw [transverseMass_twoHalfspaceCone p q h _ _ hn hw (placed_outward_ne_zero f u)
    (placed_sideNormal_ne_zero a f u s)]
  · simp only [decide_eq_true_eq, InnerProductGeometry.angle_comm (placedNormal f (outward u.1))]
  · rw [InnerProductGeometry.angle_comm]
    linarith [Real.pi_pos]

/-- Exact side-side material mass, with the opposite native sign convention. -/
theorem transverseMass_side {m J : ℕ} (hm : 2 ≤ m) (a : Coefficients m J)
    (f : Space m ≃ᵢ Space m) (u : Site m) (s t : Side m) (hst : s.1 ≠ t.1)
    (p q : Space m) (h : LinearIndependent ℝ ![p, q])
    (hn : placedNormal f (sideNormal a u s) ∈ normalSpan p q)
    (hw : placedNormal f (sideNormal a u t) ∈ normalSpan p q) :
    transverseMass p q h (twoHalfspaceCone (placedNormal f (sideNormal a u s))
      (placedNormal f (sideNormal a u t)) (decide ((a.value u : ℝ) < 0))) =
      if (a.value u : ℝ) < 0 then
        Real.pi + InnerProductGeometry.angle (placedNormal f (sideNormal a u s))
          (placedNormal f (sideNormal a u t))
      else Real.pi - InnerProductGeometry.angle (placedNormal f (sideNormal a u s))
          (placedNormal f (sideNormal a u t)) := by
  have hb := placed_side_normal_angle_bounds hm a u s t hst f
  rw [transverseMass_twoHalfspaceCone p q h _ _ hn hw (placed_sideNormal_ne_zero a f u s)
    (placed_sideNormal_ne_zero a f u t)]
  · simp only [decide_eq_true_eq]
  · linarith [Real.pi_pos]

private theorem pi_add_sub_acute_bounds {δ : ℝ} (hδ₀ : 0 < δ) (hδπ : δ < Real.pi / 4)
    (P : Prop) [Decidable P] :
    3 * Real.pi / 4 < (if P then Real.pi + δ else Real.pi - δ) ∧
      (if P then Real.pi + δ else Real.pi - δ) < 5 * Real.pi / 4 ∧
      (if P then Real.pi + δ else Real.pi - δ) ≠ Real.pi := by
  split_ifs <;> constructor
  all_goals first
    | linarith [Real.pi_pos]
    | exact ⟨by linarith [Real.pi_pos], by intro he; linarith⟩

/-- Genuine quantitative bounds and nonflatness of every native base material sector. -/
theorem transverseMass_base_bounds {m J : ℕ} (hm : 2 ≤ m) (a : Coefficients m J)
    (f : Space m ≃ᵢ Space m) (u : Site m) (s : Side m) (p q : Space m)
    (h : LinearIndependent ℝ ![p, q])
    (hn : placedNormal f (outward u.1) ∈ normalSpan p q)
    (hw : placedNormal f (sideNormal a u s) ∈ normalSpan p q) :
    let C := twoHalfspaceCone (placedNormal f (outward u.1))
      (placedNormal f (sideNormal a u s)) (decide (0 < (a.value u : ℝ)))
    3 * Real.pi / 4 < transverseMass p q h C ∧
      transverseMass p q h C < 5 * Real.pi / 4 ∧ transverseMass p q h C ≠ Real.pi := by
  dsimp only
  rw [transverseMass_base hm a f u s p q h hn hw]
  have hb := placed_base_normal_angle_bounds hm a u s f
  exact pi_add_sub_acute_bounds hb.1 hb.2 _

/-- Genuine quantitative bounds and nonflatness of every native side material sector. -/
theorem transverseMass_side_bounds {m J : ℕ} (hm : 2 ≤ m) (a : Coefficients m J)
    (f : Space m ≃ᵢ Space m) (u : Site m) (s t : Side m) (hst : s.1 ≠ t.1)
    (p q : Space m) (h : LinearIndependent ℝ ![p, q])
    (hn : placedNormal f (sideNormal a u s) ∈ normalSpan p q)
    (hw : placedNormal f (sideNormal a u t) ∈ normalSpan p q) :
    let C := twoHalfspaceCone (placedNormal f (sideNormal a u s))
      (placedNormal f (sideNormal a u t)) (decide ((a.value u : ℝ) < 0))
    3 * Real.pi / 4 < transverseMass p q h C ∧
      transverseMass p q h C < 5 * Real.pi / 4 ∧ transverseMass p q h C ≠ Real.pi := by
  dsimp only
  rw [transverseMass_side hm a f u s t hst p q h hn hw]
  have hb := placed_side_normal_angle_bounds hm a u s t hst f
  exact pi_add_sub_acute_bounds hb.1 hb.2 _

/-- The actual side face identifies its displayed normal among the incident
boundary planes, so membership in the root span is derived geometrically. -/
theorem sideNormal_mem_rootSpan_of_boundary_span {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (f : Space m ≃ᵢ Space m) (x p q : Space m)
    (hplanes : ∀ b : BoundaryPlaneIndex m, x ∈ f '' boundaryPlane a b →
      placedNormal f (boundaryPlaneNormal a b) ∈ Submodule.span ℝ ({p, q} : Set (Space m)))
    (u : Site m) (s : Side m) (hs : f.symm x ∈ sideFace a u s) :
    placedNormal f (sideNormal a u s) ∈ normalSpan p q :=
  hplanes (.inr (u, s)) ⟨f.symm x, sideFace_plane a u s _ hs, f.apply_symm_apply x⟩

theorem base_normals_mem_rootSpan_of_boundary_span {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (f : Space m ≃ᵢ Space m) (x p q : Space m)
    (hplanes : ∀ b : BoundaryPlaneIndex m, x ∈ f '' boundaryPlane a b →
      placedNormal f (boundaryPlaneNormal a b) ∈ Submodule.span ℝ ({p, q} : Set (Space m)))
    (u : Site m) (s : Side m) (hx : f.symm x ∈ genericBaseCrease a u s) :
    placedNormal f (outward u.1) ∈ normalSpan p q ∧
      placedNormal f (sideNormal a u s) ∈ normalSpan p q := by
  constructor
  · obtain ⟨k, hk, hn⟩ := normalCoord_zero_boundaryPlane a u (f.symm x) hx.1.2
    have hv := hplanes (.inl (normalIndex u.1, k))
      ⟨f.symm x, hk, f.apply_symm_apply x⟩
    rw [hn, placedNormal, map_smul]
    exact Submodule.smul_mem _ _ hv
  · exact sideNormal_mem_rootSpan_of_boundary_span a f x p q hplanes u s hx.1.1

theorem side_normals_mem_rootSpan_of_boundary_span {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (f : Space m ≃ᵢ Space m) (x p q : Space m)
    (hplanes : ∀ b : BoundaryPlaneIndex m, x ∈ f '' boundaryPlane a b →
      placedNormal f (boundaryPlaneNormal a b) ∈ Submodule.span ℝ ({p, q} : Set (Space m)))
    (u : Site m) (s t : Side m) (hx : f.symm x ∈ genericSideCrease a u s t) :
    placedNormal f (sideNormal a u s) ∈ normalSpan p q ∧
      placedNormal f (sideNormal a u t) ∈ normalSpan p q :=
  ⟨sideNormal_mem_rootSpan_of_boundary_span a f x p q hplanes u s hx.1.1,
    sideNormal_mem_rootSpan_of_boundary_span a f x p q hplanes u t hx.1.2⟩

/-- Bind the actual native shape classification to genuine mass information.
The ordinary branch retains the exact no-key/frontier witnesses needed by
the separate carrier quadrant calculation. -/
theorem ActualNativeCone.transverseMass_cases {m J : ℕ} [NeZero m] (hm : 2 ≤ m)
    {a : Coefficients m J} {f : Space m ≃ᵢ Space m} {x p q : Space m}
    {C : Set (Space m)} (hC : ActualNativeCone a f x C)
    (h : LinearIndependent ℝ ![p, q])
    (hplanes : ∀ b : BoundaryPlaneIndex m, x ∈ f '' boundaryPlane a b →
      placedNormal f (boundaryPlaneNormal a b) ∈ Submodule.span ℝ ({p, q} : Set (Space m))) :
    transverseMass p q h C = Real.pi ∨
      (3 * Real.pi / 4 < transverseMass p q h C ∧
        transverseMass p q h C < 5 * Real.pi / 4 ∧ transverseMass p q h C ≠ Real.pi) ∨
      (f.symm x ∈ frontier (body a) ∧ (∀ u, f.symm x ∉ keyGraph a u) ∧
        C = placedCarrierCone f x) := by
  cases hC with
  | strictSide u s hx hs =>
    left
    apply transverseMass_strictSide a f u s p q h
    exact sideNormal_mem_rootSpan_of_boundary_span a f x p q hplanes u s
      ⟨hx, strictBranchRegion_subset J u s hs⟩
  | base u s hx =>
    right; left
    obtain ⟨hn, hw⟩ := base_normals_mem_rootSpan_of_boundary_span a f x p q hplanes u s hx
    exact transverseMass_base_bounds hm a f u s p q h hn hw
  | side u s t hst hx =>
    right; left
    obtain ⟨hn, hw⟩ := side_normals_mem_rootSpan_of_boundary_span a f x p q hplanes u s t hx
    exact transverseMass_side_bounds hm a f u s t hst p q h hn hw
  | ordinary hx hkey => exact Or.inr (Or.inr ⟨hx, hkey, rfl⟩)

/-- Two positively homogeneous cones with the same actual centered membership
germ are equal: scale each test vector into their common positive-radius ball. -/
theorem HasCenteredGerm.cone_eq_of_homogeneous {m : ℕ} {S C D : Set (Space m)}
    {x : Space m} (hC : HasCenteredGerm S x C) (hD : HasCenteredGerm S x D)
    (hCh : ∀ (t : ℝ), 0 < t → ∀ z, t • z ∈ C ↔ z ∈ C)
    (hDh : ∀ (t : ℝ), 0 < t → ∀ z, t • z ∈ D ↔ z ∈ D) : C = D := by
  obtain ⟨r, hr, hCr⟩ := hC
  obtain ⟨s, hs, hDs⟩ := hD
  ext z
  obtain ⟨t, ht, htz⟩ := exists_pos_smul_norm_lt z (lt_min hr hs)
  calc
    z ∈ C ↔ t • z ∈ C := (hCh t ht z).symm
    _ ↔ x + t • z ∈ S := (hCr _ (htz.trans_le (min_le_left _ _))).symm
    _ ↔ t • z ∈ D := hDs _ (htz.trans_le (min_le_right _ _))
    _ ↔ z ∈ D := hDh t ht z

/-- At a specified actual base crease the chosen fan germ equals the explicit
base material cone, regardless of which native-shape proof was chosen. -/
theorem ActualTwoNormalGerm.cone_eq_base {m J : ℕ} [NeZero m] (hm : 2 ≤ m)
    {a : Coefficients m J} {f : Space m ≃ᵢ Space m} {x p q : Space m}
    (G : ActualTwoNormalGerm a f x p q) (u : Site m) (s : Side m)
    (hx : f.symm x ∈ genericBaseCrease a u s) :
    G.cone = twoHalfspaceCone (placedNormal f (outward u.1))
      (placedNormal f (sideNormal a u s)) (decide (0 < (a.value u : ℝ))) :=
  G.actual_germ.cone_eq_of_homogeneous (placed_genericBase_hasCenteredGerm hm a f x u s hx)
    G.sign_determined.homogeneous (twoHalfspaceCone_signDetermined _ _ _).homogeneous

theorem ActualTwoNormalGerm.cone_eq_side {m J : ℕ} [NeZero m] (hm : 2 ≤ m)
    {a : Coefficients m J} {f : Space m ≃ᵢ Space m} {x p q : Space m}
    (G : ActualTwoNormalGerm a f x p q) (u : Site m) (s t : Side m)
    (hx : f.symm x ∈ genericSideCrease a u s t) :
    G.cone = twoHalfspaceCone (placedNormal f (sideNormal a u s))
      (placedNormal f (sideNormal a u t)) (decide ((a.value u : ℝ) < 0)) :=
  G.actual_germ.cone_eq_of_homogeneous (placed_genericSide_hasCenteredGerm hm a f x u s t hx)
    G.sign_determined.homogeneous (twoHalfspaceCone_signDetermined _ _ _).homogeneous

/-- The root fan cone at an actual generic base crease has genuine nonflat
key-sector mass, with no assumption about the selected native-shape proof. -/
theorem ActualTwoNormalGerm.transverseMass_base_bounds {m J : ℕ} [NeZero m] (hm : 2 ≤ m)
    {a : Coefficients m J} {f : Space m ≃ᵢ Space m} {x p q : Space m}
    (G : ActualTwoNormalGerm a f x p q) (u : Site m) (s : Side m)
    (hx : f.symm x ∈ genericBaseCrease a u s) (h : LinearIndependent ℝ ![p, q])
    (hplanes : ∀ b : BoundaryPlaneIndex m, x ∈ f '' boundaryPlane a b →
      placedNormal f (boundaryPlaneNormal a b) ∈ Submodule.span ℝ ({p, q} : Set (Space m))) :
    3 * Real.pi / 4 < transverseMass p q h G.cone ∧
      transverseMass p q h G.cone < 5 * Real.pi / 4 ∧ transverseMass p q h G.cone ≠ Real.pi := by
  rw [G.cone_eq_base hm u s hx]
  obtain ⟨hn, hw⟩ := base_normals_mem_rootSpan_of_boundary_span a f x p q hplanes u s hx
  exact NativeChair.transverseMass_base_bounds hm a f u s p q h hn hw

theorem ActualTwoNormalGerm.transverseMass_side_bounds {m J : ℕ} [NeZero m] (hm : 2 ≤ m)
    {a : Coefficients m J} {f : Space m ≃ᵢ Space m} {x p q : Space m}
    (G : ActualTwoNormalGerm a f x p q) (u : Site m) (s t : Side m) (hst : s.1 ≠ t.1)
    (hx : f.symm x ∈ genericSideCrease a u s t) (h : LinearIndependent ℝ ![p, q])
    (hplanes : ∀ b : BoundaryPlaneIndex m, x ∈ f '' boundaryPlane a b →
      placedNormal f (boundaryPlaneNormal a b) ∈ Submodule.span ℝ ({p, q} : Set (Space m))) :
    3 * Real.pi / 4 < transverseMass p q h G.cone ∧
      transverseMass p q h G.cone < 5 * Real.pi / 4 ∧ transverseMass p q h G.cone ≠ Real.pi := by
  rw [G.cone_eq_side hm u s t hx]
  obtain ⟨hn, hw⟩ := side_normals_mem_rootSpan_of_boundary_span a f x p q hplanes u s t hx
  exact NativeChair.transverseMass_side_bounds hm a f u s t hst p q h hn hw

end
end PhysicalRegistration.NativeChair
