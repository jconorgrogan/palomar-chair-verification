module

public import SpectreGeometry.ProductFinitePlaneAvoidance
public import SpectreGeometry.PolygonProductKeyBoundaryPlanes
public import SpectreGeometry.PolygonProductKeyGenericRidges

@[expose] public section


/-! Dense actual crease points that are generic for every supporting plane
of every incident body in an arbitrary indexed isometric packing. Neighbor
finiteness and properness of excluded planes are derived, not assumed. -/
namespace SpectreGeometry.ProductCrease
noncomputable section
open Set
open scoped InnerProductSpace

theorem image_product_key_boundary_plane_uncentered (b : ProductKeyBoundaryPlaneIndex)
    (f : EFour ≃ᵢ EFour) :
    f '' productKeyBoundaryPlane b =
      {y | inner ℝ (f.toRealLinearIsometryEquiv (productKeyBoundaryPlaneNormal b)) y =
        productKeyBoundaryPlaneLevel b +
          inner ℝ (f.toRealLinearIsometryEquiv (productKeyBoundaryPlaneNormal b))
            (f (productKeyBoundaryPlaneCenter b))} := by
  rw [image_product_key_boundary_plane]
  ext y
  simp only [mem_setOf_eq,inner_sub_right]
  constructor <;> intro h <;> linarith

theorem placed_crease_crossPlacement_genericity {ι : Type*}
    (f : ι → EFour ≃ᵢ EFour)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedPolygonProductKeyBody (f i))) (interior (placedPolygonProductKeyBody (f j))))
    (i : ι) (C G : Set (EFour)) (hC : Convex ℝ C) (hCompact : IsCompact C)
    (hG : closure G = C) (hbody : C ⊆ polygonProductKeyBody) :
    ∃ D : Set (EFour), D ⊆ f i '' G ∧ closure D = f i '' C ∧
      (∀ x ∈ D, ∀ j, (placedPolygonProductKeyBody (f j) ∩ placedPolygonProductKeyBody (f i)).Nonempty →
        ∀ b : ProductKeyBoundaryPlaneIndex, x ∈ f j '' productKeyBoundaryPlane b →
          f i '' C ⊆ f j '' productKeyBoundaryPlane b) ∧
      (∀ x ∈ D, ∀ j, x ∈ placedPolygonProductKeyBody (f j) →
        ∀ b : ProductKeyBoundaryPlaneIndex, x ∈ f j '' productKeyBoundaryPlane b →
          f i '' C ⊆ f j '' productKeyBoundaryPlane b) := by
  classical
  let N : Set ι := {j | (placedPolygonProductKeyBody (f j) ∩ placedPolygonProductKeyBody (f i)).Nonempty}
  let : Fintype N := (finite_placedPolygonProductKeyBody_neighbors f hdisjoint i).fintype
  let n : N × ProductKeyBoundaryPlaneIndex → EFour := fun k =>
    (f k.1.val).toRealLinearIsometryEquiv (productKeyBoundaryPlaneNormal k.2)
  let c : N × ProductKeyBoundaryPlaneIndex → ℝ := fun k =>
    productKeyBoundaryPlaneLevel k.2 + ⟪n k, f k.1.val (productKeyBoundaryPlaneCenter k.2)⟫_ℝ
  have hplacedConvex : Convex ℝ (f i '' C) :=
    Convex.affine_image (f i).toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap hC
  have hplacedClosed : IsClosed (f i '' C) := (hCompact.image (f i).continuous).isClosed
  have hplacedDense : closure (f i '' G) = f i '' C := by
    calc
      closure (f i '' G) = (f i).toHomeomorph '' closure G :=
        ((f i).toHomeomorph.image_closure G).symm
      _ = f i '' C := by rw [hG]; rfl
  obtain ⟨D, hDG, hDC, hDplane⟩ := convex_generic_finite_plane_dichotomy
    (f i '' C) (f i '' G) hplacedConvex hplacedClosed hplacedDense n c
  have hneighbor : ∀ x ∈ D, ∀ j,
      (placedPolygonProductKeyBody (f j) ∩ placedPolygonProductKeyBody (f i)).Nonempty →
      ∀ b : ProductKeyBoundaryPlaneIndex, x ∈ f j '' productKeyBoundaryPlane b →
        f i '' C ⊆ f j '' productKeyBoundaryPlane b := by
    intro x hx j hj b hb
    let k : N × ProductKeyBoundaryPlaneIndex := (⟨j, hj⟩, b)
    have hbeq : f j '' productKeyBoundaryPlane b = {y | ⟪n k, y⟫_ℝ = c k} :=
      image_product_key_boundary_plane_uncentered b (f j)
    rw [hbeq] at hb ⊢
    exact hDplane x hx k hb
  refine ⟨D, hDG, hDC, hneighbor, ?_⟩
  intro x hx j hj b hb
  have hxC : x ∈ f i '' C := hDC ▸ subset_closure hx
  have hxbody : x ∈ placedPolygonProductKeyBody (f i) := image_mono hbody hxC
  exact hneighbor x hx j ⟨x, hj, hxbody⟩ b hb

theorem baseGeneric_crossPlacement {ι : Type*}
    (f : ι → EFour ≃ᵢ EFour)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedPolygonProductKeyBody (f i)))
        (interior (placedPolygonProductKeyBody (f j))))
    (i : ι) (u : ProductKeySite) (b : ProductKeySide) :
    ∃ D : Set EFour, D ⊆ f i '' baseGeneric u b ∧
      closure D = f i '' baseCrease u b ∧
      ∀ x ∈ D, ∀ j, x ∈ placedPolygonProductKeyBody (f j) →
        ∀ k : ProductKeyBoundaryPlaneIndex, x ∈ f j '' productKeyBoundaryPlane k →
          f i '' baseCrease u b ⊆ f j '' productKeyBoundaryPlane k := by
  have hbody : baseCrease u b ⊆ polygonProductKeyBody := by
    intro x hx
    exact product_key_graph_window_subset_body u (sideFace_subset_graphWindow u b hx.1)
  obtain ⟨D,hDG,hDC,_,hD⟩ := placed_crease_crossPlacement_genericity f hdisjoint i
    (baseCrease u b) (baseGeneric u b) (baseCrease_convex u b)
    (baseCrease_isCompact u b) (closure_baseGeneric u b) hbody
  exact ⟨D,hDG,hDC,hD⟩

theorem sideGeneric_crossPlacement {ι : Type*}
    (f : ι → EFour ≃ᵢ EFour)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedPolygonProductKeyBody (f i)))
        (interior (placedPolygonProductKeyBody (f j))))
    (i : ι) (u : ProductKeySite) (b c : ProductKeySide) (hbc : b.1 ≠ c.1) :
    ∃ D : Set EFour, D ⊆ f i '' sideGeneric u b c ∧
      closure D = f i '' sideCrease u b c ∧
      ∀ x ∈ D, ∀ j, x ∈ placedPolygonProductKeyBody (f j) →
        ∀ k : ProductKeyBoundaryPlaneIndex, x ∈ f j '' productKeyBoundaryPlane k →
          f i '' sideCrease u b c ⊆ f j '' productKeyBoundaryPlane k := by
  have hbody : sideCrease u b c ⊆ polygonProductKeyBody := by
    intro x hx
    exact product_key_graph_window_subset_body u (sideFace_subset_graphWindow u b hx.1)
  obtain ⟨D,hDG,hDC,_,hD⟩ := placed_crease_crossPlacement_genericity f hdisjoint i
    (sideCrease u b c) (sideGeneric u b c) (sideCrease_convex u b c)
    (sideCrease_isCompact u b c) (closure_sideGeneric u b c hbc) hbody
  exact ⟨D,hDG,hDC,hD⟩

end
end SpectreGeometry.ProductCrease
