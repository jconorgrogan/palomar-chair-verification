module

public import SpectreGeometry.PolygonProductKeyCollarMargins
public import SpectreGeometry.EdgeNeighborhood

@[expose] public section


/-! Literal planar collar halfspaces for the optimized 56-key construction.
The active rectangle has tangent halfwidth 2 eta and outward halfheight rho;
the passive square has halfwidth 2 eta at (1/2,1/2). -/
namespace SpectreGeometry
noncomputable section
open Set

def productKeyActivePoint (s : ProductKeySite) (u z : ℝ) : RealPoint :=
  productKeyActiveCenter s + u • (productKeySign s • realEdge s.2.1) +
    z • productKeyPlanarOutward s.2.1

private theorem radial_active_point (s : ProductKeySite) (j : Fin 14) (u z : ℝ) :
    radialSide j (productKeyActivePoint s u z) =
      radialSide j (productKeyActiveCenter s) +
      u * productKeySign s * RealPoint.det (RealPoint.sub (realVertex j) realFanCenter) (realEdge s.2.1) +
      z * RealPoint.det (RealPoint.sub (realVertex j) realFanCenter) (productKeyPlanarOutward s.2.1) := by
  simp only [radialSide,productKeyActivePoint,side,RealPoint.det,RealPoint.sub,
    Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

private theorem radial_active_point_error (s : ProductKeySite) (j : Fin 14) (u z : ℝ)
    (hu : |u| ≤ 2 * productKeyEta) (hz : |z| ≤ productKeyRho) :
    |radialSide j (productKeyActivePoint s u z) - radialSide j (productKeyActiveCenter s)| ≤
      3 / 4000 := by
  rw [radial_active_point]
  have h1 : |u * productKeySign s *
      RealPoint.det (RealPoint.sub (realVertex j) realFanCenter) (realEdge s.2.1)| ≤
      (2 * productKeyEta) * 10 := by
    rw [abs_mul,abs_mul,product_key_sign_abs,mul_one]
    exact mul_le_mul hu (product_key_radial_edge_coefficient_bound s.2.1 j)
      (abs_nonneg _) (by norm_num [productKeyEta])
  have h2 : |z * RealPoint.det (RealPoint.sub (realVertex j) realFanCenter)
      (productKeyPlanarOutward s.2.1)| ≤ productKeyRho * 10 := by
    rw [abs_mul]
    exact mul_le_mul hz (product_key_radial_normal_coefficient_bound s.2.1 j)
      (abs_nonneg _) (by norm_num [productKeyRho])
  have htri := abs_add_le
    (u * productKeySign s * RealPoint.det (RealPoint.sub (realVertex j) realFanCenter) (realEdge s.2.1))
    (z * RealPoint.det (RealPoint.sub (realVertex j) realFanCenter) (productKeyPlanarOutward s.2.1))
  have he : ∀ a b c : ℝ, a + b + c - a = b + c := by intros; ring
  rw [he]
  exact htri.trans ((add_le_add h1 h2).trans (by norm_num [productKeyEta,productKeyRho]))

theorem product_key_active_point_radial_signs (s : ProductKeySite) (u z : ℝ)
    (hu : |u| ≤ 2 * productKeyEta) (hz : |z| ≤ productKeyRho) :
    0 < radialSide s.2.1 (productKeyActivePoint s u z) ∧
      radialSide (next s.2.1) (productKeyActivePoint s u z) < 0 := by
  have hm := product_key_active_radial_margins s
  have h1 := (abs_le.mp (radial_active_point_error s s.2.1 u z hu hz))
  have h2 := (abs_le.mp (radial_active_point_error s (next s.2.1) u z hu hz))
  constructor <;> linarith

theorem product_key_active_point_outer_side (s : ProductKeySite) (u z : ℝ) :
    side (realVertex s.2.1) (realVertex (next s.2.1)) (productKeyActivePoint s u z) = -z := by
  have hu := real_edges_unit_squared s.2.1
  simp only [RealPoint.dot,realEdge,RealPoint.sub] at hu
  have he : side (realVertex s.2.1) (realVertex (next s.2.1)) (productKeyActivePoint s u z) =
      -z * ((realEdge s.2.1).1 ^ 2 + (realEdge s.2.1).2 ^ 2) := by
    simp only [side,productKeyActivePoint,productKeyActiveCenter,productKeyPlanarOutward,
      realEdge,RealPoint.det,RealPoint.sub,Prod.fst_add,Prod.snd_add,
      Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    ring
  rw [he]
  have hs : (realEdge s.2.1).1 ^ 2 + (realEdge s.2.1).2 ^ 2 = 1 := by
    simpa [realEdge,RealPoint.sub,pow_two] using hu
  rw [hs,mul_one]

private theorem midpoint_radial (i : Fin 14) (y : RealPoint) :
    radialSide i (interpolate realFanCenter y (1/2)) = radialSide i y / 2 := by
  simp only [radialSide,side,interpolate,RealPoint.det,RealPoint.sub]
  ring

private theorem midpoint_outer_side (i : Fin 14) (y : RealPoint) :
    side (realVertex i) (realVertex (next i)) (interpolate realFanCenter y (1/2)) =
      (productKeyFanHeight i + side (realVertex i) (realVertex (next i)) y) / 2 := by
  simp only [productKeyFanHeight,side,interpolate,RealPoint.det,RealPoint.sub]
  ring

private theorem point_not_other_triangle (i j : Fin 14) (hij : i ≠ j) (y : RealPoint)
    (hmid : interpolate realFanCenter y (1/2) ∈ interior (triangleBody i)) :
    y ∉ triangleBody j := by
  intro hy
  have hc := realFanCenter_mem_triangleBody j
  have hm : (1/2 : ℝ) • realFanCenter + (1/2 : ℝ) • y ∈ triangleBody j :=
    (convex_convexHull ℝ {realVertex j,realVertex (next j),realize fanCenter})
      hc hy (by norm_num) (by norm_num) (by norm_num)
  have he : (1/2 : ℝ) • realFanCenter + (1/2 : ℝ) • y =
      interpolate realFanCenter y (1/2) := by
    apply Prod.ext <;> simp only [interpolate,Prod.fst_add,Prod.snd_add,
      Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring
  rw [he] at hm
  exact Set.disjoint_left.mp (triangleBody_interior_disjoint_body i j hij) hmid hm

theorem product_key_active_collar_halfplane (s : ProductKeySite) (u z : ℝ)
    (hu : |u| ≤ 2 * productKeyEta) (hz : |z| ≤ productKeyRho) :
    (productKeyActivePoint s u z ∈ polygonBody ↔ z ≤ 0) ∧
    (productKeyActivePoint s u z ∈ interior polygonBody ↔ z < 0) := by
  let i := s.2.1
  let y := productKeyActivePoint s u z
  have hr := product_key_active_point_radial_signs s u z hu hz
  have hm : interpolate realFanCenter y (1/2) ∈ interior (triangleBody i) := by
    apply (triangleBody_interior_iff i _).mpr
    rw [midpoint_radial,midpoint_radial,midpoint_outer_side]
    have ho := product_key_active_point_outer_side s u z
    have hf := product_key_fan_height_margin i
    have hz' := (abs_le.mp hz).2
    change z ≤ productKeyRho at hz'
    norm_num [productKeyRho] at hz'
    change side (realVertex i) (realVertex (next i)) y = -z at ho
    rw [ho]
    change 0 < radialSide i y ∧ radialSide (next i) y < 0 at hr
    exact ⟨by linarith [hr.1],by linarith,by linarith [hr.2]⟩
  let O : Set RealPoint := ⋃ j : {j : Fin 14 // j ≠ i}, triangleBody j.val
  have hclosed : IsClosed O := isClosed_iUnion_of_finite fun j => (triangleBody_compact j.val).isClosed
  have hyO : y ∉ O := by
    intro h
    obtain ⟨j,hj⟩ := mem_iUnion.mp h
    exact point_not_other_triangle i j.val (Ne.symm j.property) y hm hj
  have hsub : polygonBody ∩ Oᶜ ⊆ triangleBody i := by
    rintro x ⟨hx,ho⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    by_cases h : j = i
    · simpa [h] using hj
    · exact False.elim (ho (mem_iUnion.mpr ⟨⟨j,h⟩,hj⟩))
  have ho : side (realVertex i) (realVertex (next i)) y = -z :=
    product_key_active_point_outer_side s u z
  change 0 < radialSide i y ∧ radialSide (next i) y < 0 at hr
  constructor
  · constructor
    · intro h
      have hh := ((triangleBody_mem_iff i y).mp (hsub ⟨h,hyO⟩)).2.1
      rw [ho] at hh
      linarith
    · intro h
      exact mem_iUnion.mpr ⟨i,(triangleBody_mem_iff i y).mpr
        ⟨hr.1.le,by rw [ho]; linarith,hr.2.le⟩⟩
  · constructor
    · intro h
      have hs : interior polygonBody ∩ Oᶜ ⊆ triangleBody i :=
        fun x hx => hsub ⟨interior_subset hx.1,hx.2⟩
      have hi : y ∈ interior (triangleBody i) :=
        (interior_maximal hs (isOpen_interior.inter hclosed.isOpen_compl)) ⟨h,hyO⟩
      have hh := ((triangleBody_interior_iff i y).mp hi).2.1
      rw [ho] at hh
      linarith
    · intro h
      exact interior_mono (subset_iUnion triangleBody i)
        ((triangleBody_interior_iff i y).mpr ⟨hr.1,by rw [ho]; linarith,hr.2⟩)

theorem product_key_passive_square_interior (u v : ℝ)
    (hu : |u| ≤ 2 * productKeyEta) (hv : |v| ≤ 2 * productKeyEta) :
    ((1/2+u,1/2+v) : RealPoint) ∈ interior polygonBody := by
  apply interior_mono (subset_iUnion triangleBody (13 : Fin 14))
  apply (triangleBody_interior_iff 13 _).mpr
  have hu' := abs_le.mp hu
  have hv' := abs_le.mp hv
  norm_num [productKeyEta] at hu' hv'
  norm_num [radialSide,side,realVertex,realFanCenter,realize,vertex,vertices,
    next,fanCenter,Quad3.eval,RealPoint.sub,RealPoint.det]
  constructor
  · linarith
  · constructor <;> linarith

end
end SpectreGeometry
