module

public import SpectreGeometry.PolygonProductKeyBody

@[expose] public section


/-! Compatibility on the entire boundary of each actual closed recipe collar.

At an active-height boundary point the tangent coordinates lie strictly inside
the collar, so its normal coordinate has absolute value exactly rho. The
height amplitude is strictly smaller than rho. This proves compatibility at
both normal caps as well as the zero-height tangent faces, without any extra
geometric hypothesis. The literal body therefore agrees with its hypograph
on the whole closed collar. An isolating open neighborhood also gives the
exact single-collar splice, without asserting an unjustified hypograph chart
outside the collar. -/

namespace PhysicalRegistration
open Set

variable {X : Type*} [TopologicalSpace X] {κ : Type*}

/-- On a neighborhood excluding every other tube, boundary compatibility
allows the exact replacement to be written using deletion of the closed tube.
The complement of the tube retains the original carrier. -/
theorem replaceTubes_local_closed_splice_iff
    (carrier : Set X) (tube hypograph : κ → Set X) (i : κ) (U : Set X)
    (hother : ∀ j, j ≠ i → Disjoint U (tube j))
    (hboundary : ∀ x ∈ tube i, x ∉ interior (tube i) →
      (x ∈ carrier ↔ x ∈ hypograph i)) :
    ∀ x ∈ U, x ∈ replaceTubes carrier tube hypograph ↔
      x ∈ (carrier \ tube i) ∪ (tube i ∩ hypograph i) := by
  classical
  intro x hxU
  have hnotother : ∀ j, j ≠ i → x ∉ tube j := by
    intro j hji hxj
    exact Set.disjoint_left.mp (hother j hji) hxU hxj
  constructor
  · intro hx
    rcases hx with ⟨hxC, hxNot⟩ | hxPiece
    · by_cases hxTube : x ∈ tube i
      · have hxNotI : x ∉ interior (tube i) :=
          fun hxI => hxNot (mem_iUnion.mpr ⟨i, hxI⟩)
        exact Or.inr ⟨hxTube, (hboundary x hxTube hxNotI).mp hxC⟩
      · exact Or.inl ⟨hxC, hxTube⟩
    · obtain ⟨j, hxj, hxHj⟩ := mem_iUnion.mp hxPiece
      by_cases hji : j = i
      · subst j
        exact Or.inr ⟨hxj, hxHj⟩
      · exact (hnotother j hji hxj).elim
  · intro hx
    rcases hx with ⟨hxC, hxNotTube⟩ | hxPiece
    · apply Or.inl
      refine ⟨hxC, ?_⟩
      intro hxUnion
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hxUnion
      by_cases hji : j = i
      · subst j
        exact hxNotTube (interior_subset hxj)
      · exact hnotother j hji (interior_subset hxj)
    · exact Or.inr (mem_iUnion.mpr ⟨i, hxPiece⟩)

/-- A finite family of pairwise disjoint closed tubes admits this exact local
single-tube description at every point of the selected closed tube. -/
theorem exists_replaceTubes_local_closed_splice [Finite κ]
    (carrier : Set X) (tube hypograph : κ → Set X)
    (hclosed : ∀ i, IsClosed (tube i))
    (hdisjoint : Pairwise fun i j => Disjoint (tube i) (tube j))
    (i : κ)
    (hboundary : ∀ y ∈ tube i, y ∉ interior (tube i) →
      (y ∈ carrier ↔ y ∈ hypograph i))
    {x : X} (hx : x ∈ tube i) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      (∀ j, j ≠ i → Disjoint U (tube j)) ∧
      ∀ y ∈ U, y ∈ replaceTubes carrier tube hypograph ↔
        y ∈ (carrier \ tube i) ∪ (tube i ∩ hypograph i) := by
  obtain ⟨U, hU, hxU, hother⟩ :=
    exists_isolating_open_tube tube hclosed hdisjoint i hx
  exact ⟨U, hU, hxU, hother,
    replaceTubes_local_closed_splice_iff carrier tube hypograph i U hother hboundary⟩

end PhysicalRegistration

namespace SpectreGeometry
noncomputable section
open Set PhysicalRegistration
open scoped InnerProductSpace

/-- Membership in the actual affine collar is exactly its physical-coordinate
closed-box condition. -/
theorem product_key_collar_coordinates (s : ProductKeySite) (x : EFour) :
    x ∈ productKeyCollar s ↔
      (∀ j : Fin 3, |inner ℝ (productKeyTangent s j) (x - productKeyCenter s)| ≤
        2 * productKeyEta) ∧
      |inner ℝ (productKeyOutwardNormal s) (x - productKeyCenter s)| ≤ productKeyRho := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    constructor
    · intro j
      rw [← productKeyFrame_tangent s j, product_key_affine_frame_coordinate]
      exact hw.1 j
    · rw [← productKeyFrame_normal s, product_key_affine_frame_coordinate]
      exact hw.2
  · intro hx
    refine ⟨(productKeyAffineIsometry s).symm x, ?_,
      (productKeyAffineIsometry s).apply_symm_apply x⟩
    constructor
    · intro j
      rw [← product_key_inverse_tangent_coordinate]
      exact hx.1 j
    · rw [← product_key_inverse_normal_coordinate]
      exact hx.2

/-- Inside the open normal strip, every noninterior point has zero key height.
This implication does not even require membership in the closed collar. -/
theorem product_key_height_zero_of_collar_noninterior
    (s : ProductKeySite) (x : EFour)
    (hstrip : |inner ℝ (productKeyOutwardNormal s) (x - productKeyCenter s)| <
      productKeyRho)
    (hx : x ∉ interior (productKeyCollar s)) :
    productKeyHeight s (x - productKeyCenter s) = 0 := by
  by_contra hactive
  apply hx
  apply product_key_strict_collar_subset_interior s
  constructor
  · intro j
    exact (product_key_height_support s (x - productKeyCenter s) hactive j).trans_lt
      (by norm_num [productKeyEta])
  · exact hstrip

/-- Nonzero height at a closed-collar boundary point forces a normal cap. -/
theorem product_key_active_collar_boundary_normal
    (s : ProductKeySite) (x : EFour) (hx : x ∈ productKeyCollar s)
    (hxNot : x ∉ interior (productKeyCollar s))
    (hactive : productKeyHeight s (x - productKeyCenter s) ≠ 0) :
    |inner ℝ (productKeyOutwardNormal s) (x - productKeyCenter s)| = productKeyRho := by
  apply le_antisymm ((product_key_collar_coordinates s x).mp hx).2
  apply le_of_not_gt
  intro hstrip
  exact hactive (product_key_height_zero_of_collar_noninterior s x hstrip hxNot)

/-- The raw polygon product and the actual signed hypograph agree on the
entire closed-collar boundary, including both normal caps. -/
theorem product_key_collar_boundary_compatibility
    (s : ProductKeySite) (x : EFour) (hx : x ∈ productKeyCollar s)
    (hxNot : x ∉ interior (productKeyCollar s)) :
    x ∈ polygonProductBody ↔ x ∈ productKeyHypograph s := by
  rw [(product_key_collar_carrier_outward s x hx).1]
  change (inner ℝ (productKeyOutwardNormal s) (x - productKeyCenter s) ≤ 0) ↔
    inner ℝ (productKeyOutwardNormal s) (x - productKeyCenter s) ≤
      productKeyHeight s (x - productKeyCenter s)
  by_cases hzero : productKeyHeight s (x - productKeyCenter s) = 0
  · rw [hzero]
  · have hcap := product_key_active_collar_boundary_normal s x hx hxNot hzero
    have hheight := abs_lt.mp (product_key_height_below_rho s (x - productKeyCenter s))
    have hrho : 0 < productKeyRho := by norm_num [productKeyRho]
    rcases le_total 0 (inner ℝ (productKeyOutwardNormal s) (x - productKeyCenter s))
      with hnormal | hnormal
    · rw [abs_of_nonneg hnormal] at hcap
      constructor <;> intro h <;> exfalso <;> linarith [hheight.2]
    · rw [abs_of_nonpos hnormal] at hcap
      exact ⟨fun _ => by linarith [hheight.1], fun _ => hnormal⟩

/-- The literal assembled body is its chosen keyed hypograph on the entire
closed collar, extending the previously proved interior statement. -/
theorem polygon_product_key_body_collar_iff
    (s : ProductKeySite) (x : EFour) (hx : x ∈ productKeyCollar s) :
    x ∈ polygonProductKeyBody ↔ x ∈ productKeyHypograph s :=
  replaceTubes_local_iff polygonProductBody productKeyCollar productKeyHypograph s
    (productKeyCollar s)
    (fun t hts => product_key_collars_disjoint s t hts.symm)
    (product_key_collar_boundary_compatibility s) x hx

theorem polygon_product_key_body_inter_collar (s : ProductKeySite) :
    polygonProductKeyBody ∩ productKeyCollar s =
      productKeyHypograph s ∩ productKeyCollar s := by
  ext x
  constructor
  · intro hx
    exact ⟨(polygon_product_key_body_collar_iff s x hx.2).mp hx.1, hx.2⟩
  · intro hx
    exact ⟨(polygon_product_key_body_collar_iff s x hx.2).mpr hx.1, hx.2⟩

/-- At every actual closed-collar point, including its boundary, an open
neighborhood excludes all other collars and gives the exact one-collar
replacement formula. Outside this collar the raw carrier is retained. -/
theorem polygon_product_key_body_local_closed_splice
    (s : ProductKeySite) (x : EFour) (hx : x ∈ productKeyCollar s) :
    ∃ U : Set EFour, IsOpen U ∧ x ∈ U ∧
      (∀ t, t ≠ s → Disjoint U (productKeyCollar t)) ∧
      ∀ y ∈ U, y ∈ polygonProductKeyBody ↔
        y ∈ (polygonProductBody \ productKeyCollar s) ∪
          (productKeyCollar s ∩ productKeyHypograph s) :=
  exists_replaceTubes_local_closed_splice polygonProductBody productKeyCollar
    productKeyHypograph product_key_collar_isClosed product_key_collars_pairwise_disjoint s
    (product_key_collar_boundary_compatibility s) hx

end
end SpectreGeometry
