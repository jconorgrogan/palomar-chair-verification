module

public import SparseMonotiles.StripCreaseCrossingSeamExtraction
public import SparseMonotiles.StripCreaseCrossingSeamNormals

@[expose] public section

/-! # Retain actual normals and exposed facets together for world-plane alignment -/
namespace SparseMonotiles
open Set

/-- The two normal-space sides of a physical carrier quadrant retain their
actual exposed unit facets and exact ambient supporting equations. -/
structure CarrierSeamGeometry {d : ℕ} (g : Point d ≃ᵢ Point d)
    (R : AffineSubspace ℝ (Point d)) (p : Point d) (S : Set R.directionᗮ) where
  first : Fin d
  second : Fin d
  positive₁ : Bool
  positive₂ : Bool
  different : first ≠ second
  cell : Contact.Cell d
  owner : Contact.IsChairCell cell
  exposed₁ : ¬ Contact.IsChairCell ({cell := cell,axis := first,positive := !positive₁} : Contact.Facet d).neighbor
  exposed₂ : ¬ Contact.IsChairCell ({cell := cell,axis := second,positive := !positive₂} : Contact.Facet d).neighbor
  endpoint₁ : g.symm p first = (cell first : ℝ)+(if positive₁ then 0 else 1)
  endpoint₂ : g.symm p second = (cell second : ℝ)+(if positive₂ then 0 else 1)
  other_strict : ∀ a, a ≠ first → a ≠ second →
    (cell a : ℝ) < g.symm p a ∧ g.symm p a < (cell a : ℝ)+1
  normal₁ : R.directionᗮ
  normal₂ : R.directionᗮ
  unit₁ : ‖normal₁‖ = 1
  unit₂ : ‖normal₂‖ = 1
  orthogonal : inner (𝕜 := ℝ) normal₁ normal₂ = 0
  cone_eq : S = SectorAngleSum.normalHalfspace normal₁ ∩ SectorAngleSum.normalHalfspace normal₂
  plane₁ : ∀ x, inner (𝕜 := ℝ) normal₁ (ridgeNormalProjection R p x) = 0 ↔ g.symm x first = g.symm p first
  plane₂ : ∀ x, inner (𝕜 := ℝ) normal₂ (ridgeNormalProjection R p x) = 0 ↔ g.symm x second = g.symm p second

def CarrierSeamGeometry.swap {d : ℕ} {g : Point d ≃ᵢ Point d}
    {R : AffineSubspace ℝ (Point d)} {p : Point d} {S : Set R.directionᗮ}
    (D : CarrierSeamGeometry g R p S) : CarrierSeamGeometry g R p S where
  first := D.second
  second := D.first
  positive₁ := D.positive₂
  positive₂ := D.positive₁
  different := D.different.symm
  cell := D.cell
  owner := D.owner
  exposed₁ := D.exposed₂
  exposed₂ := D.exposed₁
  endpoint₁ := D.endpoint₂
  endpoint₂ := D.endpoint₁
  other_strict a ha hb := D.other_strict a hb ha
  normal₁ := D.normal₂
  normal₂ := D.normal₁
  unit₁ := D.unit₂
  unit₂ := D.unit₁
  orthogonal := by rw [real_inner_comm]; exact D.orthogonal
  cone_eq := D.cone_eq.trans (inter_comm _ _)
  plane₁ := D.plane₂
  plane₂ := D.plane₁

theorem signedAxisNormal_ridge_plane {d : ℕ}
    (a : Point d ≃ᵃⁱ[ℝ] Point d) (R : AffineSubspace ℝ (Point d)) (p : Point d)
    (i : Fin d) (hi : a.linearIsometryEquiv.symm (EuclideanSpace.single i 1) ∈ R.directionᗮ)
    (b : Bool) (x : Point d) :
    inner (𝕜 := ℝ) (signedAxisNormal a.linearIsometryEquiv.symm R.directionᗮ i hi b)
      (ridgeNormalProjection R p x) = 0 ↔ a x i = a p i := by
  have heq : inner (𝕜 := ℝ) (⟨a.linearIsometryEquiv.symm (EuclideanSpace.single i 1),hi⟩ : R.directionᗮ)
      (ridgeNormalProjection R p x) = a x i-a p i := by
    change inner (𝕜 := ℝ) (NormalSpaceGeometry.restrictedNormal R.directionᗮ
      (a.linearIsometryEquiv.symm (EuclideanSpace.single i 1)) hi) (ridgeNormalProjection R p x) = _
    rw [NormalSpaceGeometry.inner_restrictedNormal_projection]
    have hmap := a.map_vsub x p
    change a.linearIsometryEquiv (x-p) = a x-a p at hmap
    rw [← a.linearIsometryEquiv.inner_map_map,a.linearIsometryEquiv.apply_symm_apply,hmap]
    simp [EuclideanSpace.inner_single_left]
  cases b <;> simp only [signedAxisNormal,Bool.false_eq_true,if_false,if_true,inner_neg_left,heq] <;>
    constructor <;> intro h <;> linarith


theorem T5_right_angle_carrier_seam_geometry
    (g : Point 5 ≃ᵢ Point 5) (R : AffineSubspace ℝ (Point 5))
    {p : Point 5} (hp : p ∈ R) (hcodim : Module.finrank ℝ R.direction+2=5)
    (hactive : ∀ j, T5WorldAffineFields g j p = 0 → R ≤ affineFormPlane (T5WorldAffineFields g j) 0)
    {S : Set R.directionᗮ} (hS : IsPositiveCone S)
    (hmodel : LocalSetEq p (g '' T5) (ridgeNormalProjection R p ⁻¹' S))
    (hboundary : p ∈ frontier (g '' T5))
    (hright : SectorAngleSum.HasSectorAngle S (Real.pi/2)) :
    Nonempty (CarrierSeamGeometry g R p S) := by
  have hc := T5_right_angle_normal_cone_carrier_germ g R hp hcodim hactive hS hmodel hboundary hright
  have himage := hc.mem_iff.mp ((T5_isCompact.image g.continuous).isClosed.frontier_subset hboundary)
  have hnative : g.symm p ∈ carrier 5 := by
    obtain ⟨x,hx,hxp⟩ := himage
    rw [← hxp,g.symm_apply_apply]; exact hx
  obtain ⟨_,i,j,b,c,hij,hi,hj,hC,hS'⟩ :=
    T5_right_angle_normal_cone_coordinate_quadrant g R hp hcodim hactive hS hmodel hboundary hright
  let a := g.symm.toRealAffineIsometryEquiv
  have hact : ∀ l : CarrierHalfspaceIndex 5, carrierFrameFields a l p = 0 →
      R ≤ affineFormPlane (carrierFrameFields a l) 0 := fun l hl => hactive (.inl l) hl
  have hcard := carrier_frame_criticalAxes_card_le_two a R hp hcodim hact
  have hcrit := carrier_critical_axes_covered_of_card_le_two (g.symm p) i j hij hi hj hcard
  obtain ⟨q,hq,hpq,hendi,hendj,hother,hexpi,hexpj⟩ :=
    carrier_quadrant_exists_exposed_edge hnative i j b c hij hi hj hcrit hC
  have hni := carrier_frame_axis_mem_ridge_orthogonal a R hp hact hi
  have hnj := carrier_frame_axis_mem_ridge_orthogonal a R hp hact hj
  let N := signedAxisNormal a.linearIsometryEquiv.symm R.directionᗮ i hni b
  let M := signedAxisNormal a.linearIsometryEquiv.symm R.directionᗮ j hnj c
  refine ⟨{
    first := i
    second := j
    positive₁ := b
    positive₂ := c
    different := hij
    cell := q
    owner := hq
    exposed₁ := hexpi
    exposed₂ := hexpj
    endpoint₁ := hendi
    endpoint₂ := hendj
    other_strict := hother
    normal₁ := N
    normal₂ := M
    unit₁ := norm_signedAxisNormal _ _ _ _ _
    unit₂ := norm_signedAxisNormal _ _ _ _ _
    orthogonal := inner_signedAxisNormal _ _ _ _ _ _ _ _ hij
    cone_eq := ?_
    plane₁ := signedAxisNormal_ridge_plane a R p i hni b
    plane₂ := signedAxisNormal_ridge_plane a R p j hnj c }⟩
  change S = normalHalfspace N ∩ normalHalfspace M
  rw [normalHalfspace_signedAxisNormal,normalHalfspace_signedAxisNormal,← preimage_inter]
  simpa only [LinearIsometryEquiv.symm_symm] using hS'

#print axioms T5_right_angle_carrier_seam_geometry

theorem T7_right_angle_carrier_seam_geometry
    (g : Point 7 ≃ᵢ Point 7) (R : AffineSubspace ℝ (Point 7))
    {p : Point 7} (hp : p ∈ R) (hcodim : Module.finrank ℝ R.direction+2=7)
    (hactive : ∀ j, T7WorldAffineFields g j p = 0 → R ≤ affineFormPlane (T7WorldAffineFields g j) 0)
    {S : Set R.directionᗮ} (hS : IsPositiveCone S)
    (hmodel : LocalSetEq p (g '' T7) (ridgeNormalProjection R p ⁻¹' S))
    (hboundary : p ∈ frontier (g '' T7))
    (hright : SectorAngleSum.HasSectorAngle S (Real.pi/2)) :
    Nonempty (CarrierSeamGeometry g R p S) := by
  have hc := T7_right_angle_normal_cone_carrier_germ g R hp hcodim hactive hS hmodel hboundary hright
  have himage := hc.mem_iff.mp ((T7_isCompact.image g.continuous).isClosed.frontier_subset hboundary)
  have hnative : g.symm p ∈ carrier 7 := by
    obtain ⟨x,hx,hxp⟩ := himage
    rw [← hxp,g.symm_apply_apply]; exact hx
  obtain ⟨_,i,j,b,c,hij,hi,hj,hC,hS'⟩ :=
    T7_right_angle_normal_cone_coordinate_quadrant g R hp hcodim hactive hS hmodel hboundary hright
  let a := g.symm.toRealAffineIsometryEquiv
  have hact : ∀ l : CarrierHalfspaceIndex 7, carrierFrameFields a l p = 0 →
      R ≤ affineFormPlane (carrierFrameFields a l) 0 := fun l hl => hactive (.inl l) hl
  have hcard := carrier_frame_criticalAxes_card_le_two a R hp hcodim hact
  have hcrit := carrier_critical_axes_covered_of_card_le_two (g.symm p) i j hij hi hj hcard
  obtain ⟨q,hq,hpq,hendi,hendj,hother,hexpi,hexpj⟩ :=
    carrier_quadrant_exists_exposed_edge hnative i j b c hij hi hj hcrit hC
  have hni := carrier_frame_axis_mem_ridge_orthogonal a R hp hact hi
  have hnj := carrier_frame_axis_mem_ridge_orthogonal a R hp hact hj
  let N := signedAxisNormal a.linearIsometryEquiv.symm R.directionᗮ i hni b
  let M := signedAxisNormal a.linearIsometryEquiv.symm R.directionᗮ j hnj c
  refine ⟨{
    first := i
    second := j
    positive₁ := b
    positive₂ := c
    different := hij
    cell := q
    owner := hq
    exposed₁ := hexpi
    exposed₂ := hexpj
    endpoint₁ := hendi
    endpoint₂ := hendj
    other_strict := hother
    normal₁ := N
    normal₂ := M
    unit₁ := norm_signedAxisNormal _ _ _ _ _
    unit₂ := norm_signedAxisNormal _ _ _ _ _
    orthogonal := inner_signedAxisNormal _ _ _ _ _ _ _ _ hij
    cone_eq := ?_
    plane₁ := signedAxisNormal_ridge_plane a R p i hni b
    plane₂ := signedAxisNormal_ridge_plane a R p j hnj c }⟩
  change S = normalHalfspace N ∩ normalHalfspace M
  rw [normalHalfspace_signedAxisNormal,normalHalfspace_signedAxisNormal,← preimage_inter]
  simpa only [LinearIsometryEquiv.symm_symm] using hS'

#print axioms T7_right_angle_carrier_seam_geometry

#print axioms signedAxisNormal_ridge_plane
end SparseMonotiles
