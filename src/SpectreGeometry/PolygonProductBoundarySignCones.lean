module

public import SpectreGeometry.FiniteSignCone
public import SpectreGeometry.PlacedPolygonProductNormals
public import SpectreGeometry.PolygonConeStructure

@[expose] public section


namespace SpectreGeometry
noncomputable section
open Set FiniteConeFan
open scoped InnerProductSpace
local instance : DecidableEq EFour := Classical.decEq EFour

def factorBoundaryNormals (r : Bool) : BoundarySlot → Finset EFour
  | .inl i => {factorNormal r (previous i), factorNormal r i}
  | .inr i => {factorNormal r i}

def productBoundaryNormals : ProductBoundarySlot → Finset EFour
  | .left a => factorBoundaryNormals false a
  | .right b => factorBoundaryNormals true b
  | .both a b => factorBoundaryNormals false a ∪ factorBoundaryNormals true b

theorem factorBoundary_signDetermined (r : Bool) (b : BoundarySlot) :
    SignDetermined (factorBoundaryNormals r b)
      {v | factorProjection r v ∈ polygonBoundaryCone b} := by
  intro z w h
  cases b with
  | inr i =>
      have hi := (h (factorNormal r i) (by simp [factorBoundaryNormals])).2
      simpa only [factorNormal_inner_vector, polygonBoundaryCone, Set.mem_setOf_eq] using hi
  | inl i =>
      have hp := (h (factorNormal r (previous i)) (by simp [factorBoundaryNormals])).2
      have hi := (h (factorNormal r i) (by simp [factorBoundaryNormals])).2
      simp only [factorNormal_inner_vector] at hp hi
      by_cases he : i = 10
      · subst i
        simpa only [polygonBoundaryCone,
          polygonVertexCone_eq_halfplane_of_edges_eq 10 real_midpoint_edges_eq,
          Set.mem_setOf_eq] using hi
      · rcases lt_or_gt_of_ne (real_corner_det_ne_zero i he) with hn | hp'
        · simpa only [polygonBoundaryCone, polygonVertexCone_eq_union_of_neg i hn,
            Set.mem_setOf_eq, Set.mem_union] using or_congr hp hi
        · simpa only [polygonBoundaryCone, polygonVertexCone_eq_inter_of_pos i hp',
            Set.mem_setOf_eq, Set.mem_inter_iff] using and_congr hp hi

theorem productBoundary_signDetermined (b : ProductBoundarySlot) :
    SignDetermined (productBoundaryNormals b) (productBoundaryCone b) := by
  intro z w h
  cases b with
  | left a =>
      simpa only [productBoundaryCone, product_coordinates_mem_image,
        Set.mem_univ, and_true, Set.mem_setOf_eq] using factorBoundary_signDetermined false a z w h
  | right b =>
      simpa only [productBoundaryCone, product_coordinates_mem_image,
        Set.mem_univ, true_and, Set.mem_setOf_eq] using factorBoundary_signDetermined true b z w h
  | both a b =>
      have ha := factorBoundary_signDetermined false a z w
        (fun n hn => h n (Finset.mem_union_left _ hn))
      have hb := factorBoundary_signDetermined true b z w
        (fun n hn => h n (Finset.mem_union_right _ hn))
      simpa only [productBoundaryCone, product_coordinates_mem_image,
        Set.mem_setOf_eq] using and_congr ha hb

theorem productBoundaryCone_closed (b : ProductBoundarySlot) :
    IsClosed (productBoundaryCone b) := by
  have hc (r : Bool) (a : BoundarySlot) :
      IsClosed {v : EFour | factorProjection r v ∈ polygonBoundaryCone a} := by
    apply (polygonBoundaryCone_isClosed a).preimage
    cases r <;> unfold factorProjection <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop
  cases b with
  | left a =>
      convert hc false a using 1
      ext v
      simp only [productBoundaryCone, product_coordinates_mem_image, Set.mem_univ,
        and_true, Set.mem_setOf_eq]
  | right b =>
      convert hc true b using 1
      ext v
      simp only [productBoundaryCone, product_coordinates_mem_image, Set.mem_univ,
        true_and, Set.mem_setOf_eq]
  | both a b =>
      convert (hc false a).inter (hc true b) using 1
      ext v
      simp only [productBoundaryCone, product_coordinates_mem_image, Set.mem_inter_iff,
        Set.mem_setOf_eq]

theorem productBoundaryNormals_nonzero (b : ProductBoundarySlot) :
    ∀ n ∈ productBoundaryNormals b, n ≠ 0 := by
  have hf (r : Bool) (a : BoundarySlot) : ∀ n ∈ factorBoundaryNormals r a, n ≠ 0 := by
    cases a <;> simp only [factorBoundaryNormals, Finset.mem_insert, Finset.mem_singleton]
    · intro n hn; rcases hn with rfl | rfl <;> exact factorNormal_ne_zero _ _
    · intro n hn; subst n; exact factorNormal_ne_zero _ _
  cases b with
  | left a => exact hf false a
  | right b => exact hf true b
  | both a b =>
      intro n hn
      rcases Finset.mem_union.mp hn with h | h
      · exact hf false a n h
      · exact hf true b n h

theorem placed_productBoundary_signDetermined (f : EFour ≃ᵢ EFour) (b : ProductBoundarySlot) :
    SignDetermined ((productBoundaryNormals b).image f.toRealLinearIsometryEquiv)
      (f.toRealLinearIsometryEquiv '' productBoundaryCone b) :=
  (productBoundary_signDetermined b).image_linearIsometryEquiv f.toRealLinearIsometryEquiv

theorem placed_productBoundaryCone_closed (f : EFour ≃ᵢ EFour) (b : ProductBoundarySlot) :
    IsClosed (f.toRealLinearIsometryEquiv '' productBoundaryCone b) :=
  f.toRealLinearIsometryEquiv.toHomeomorph.isClosedMap _ (productBoundaryCone_closed b)

theorem placed_productBoundaryNormals_range_iff (f : EFour ≃ᵢ EFour)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour) (b : ProductBoundarySlot) :
    (∀ n ∈ (productBoundaryNormals b).image f.toRealLinearIsometryEquiv, n ∈ Set.range L) ↔
      PlacedProductBoundaryNormalsIn f L b := by
  have hf (r : Bool) (a : BoundarySlot) :
      (∀ n ∈ factorBoundaryNormals r a, f.toRealLinearIsometryEquiv n ∈ Set.range L) ↔
        PlacedBoundaryNormalsIn f L r a := by
    cases a <;> simp [factorBoundaryNormals, PlacedBoundaryNormalsIn]
  simp only [Finset.forall_mem_image]
  cases b <;> simp only [productBoundaryNormals, PlacedProductBoundaryNormalsIn,
    Finset.forall_mem_union, hf]

end
end SpectreGeometry
