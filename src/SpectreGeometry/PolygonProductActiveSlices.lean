module

public import SpectreGeometry.PolygonProductActiveComponents
public import SpectreGeometry.PolygonProductRawLocalFiniteness
public import Mathlib.Topology.Compactness.SigmaCompact

@[expose] public section


/-! Literal planar slices of active-edge components. Compact incidence and
closedness follow from actual physical packing. Planar interior disjointness
is transported from the raw-carrier packing supplied by global flattening. -/
namespace SpectreGeometry
noncomputable section
open Set

def productFactorHomeomorph (b : Fin 2) : (RealPoint × RealPoint) ≃ₜ EFour :=
  if b = 0 then productCoordinates.toHomeomorph
  else (Homeomorph.prodComm RealPoint RealPoint).trans productCoordinates.toHomeomorph

theorem product_factor_homeomorph_apply (b : Fin 2) (a p : RealPoint) :
    productFactorHomeomorph b (a,p) = productFactorPoint b a p := by
  by_cases hb : b = 0 <;> simp [productFactorHomeomorph,productFactorPoint,hb]

theorem product_factor_mem_raw (b : Fin 2) (a p : RealPoint) :
    productFactorPoint b a p ∈ polygonProductBody ↔ a ∈ polygonBody ∧ p ∈ polygonBody := by
  rw [polygon_product_body_mem]
  fin_cases b <;> simp [productFactorPoint,productCoordinates,productCoordinateLinearEquiv,and_comm]

theorem product_factor_homeomorph_raw (b : Fin 2) :
    productFactorHomeomorph b '' (polygonBody ×ˢ polygonBody) = polygonProductBody := by
  ext x
  obtain ⟨⟨a,p⟩,rfl⟩ := (productFactorHomeomorph b).surjective x
  rw [(productFactorHomeomorph b).injective.mem_set_image,
    product_factor_homeomorph_apply,product_factor_mem_raw]
  rfl

theorem product_factor_mem_raw_interior (b : Fin 2) (a p : RealPoint) :
    productFactorPoint b a p ∈ interior polygonProductBody ↔
      a ∈ interior polygonBody ∧ p ∈ interior polygonBody := by
  have he : productFactorHomeomorph b '' interior (polygonBody ×ˢ polygonBody) =
      interior polygonProductBody := by
    rw [(productFactorHomeomorph b).image_interior,product_factor_homeomorph_raw]
  rw [← product_factor_homeomorph_apply,← he,
    (productFactorHomeomorph b).injective.mem_set_image,interior_prod_eq]
  rfl

def productPlaneSlice (f : EFour ≃ᵢ EFour) (b : Fin 2) (p : RealPoint) (x : EPlane) : EFour :=
  f (productFactorPoint b (euclideanCoordinates.symm x) p)

theorem product_plane_slice_continuous (f : EFour ≃ᵢ EFour) (b : Fin 2) (p : RealPoint) :
    Continuous (productPlaneSlice f b p) := by
  have he : productPlaneSlice f b p = fun x =>
      f (productFactorHomeomorph b (euclideanCoordinates.symm x,p)) := by
    funext x; rw [product_factor_homeomorph_apply]; rfl
  rw [he]
  exact f.continuous.comp ((productFactorHomeomorph b).continuous.comp
    (euclideanCoordinates.symm.continuous.prodMk continuous_const))

private theorem planar_source_body_iff (A : EPlane ≃ᵢ EPlane) (x : EPlane) :
    x ∈ A '' euclideanBody ↔ euclideanCoordinates.symm (A.symm x) ∈ polygonBody := by
  constructor
  · rintro ⟨y,⟨a,ha,rfl⟩,he⟩
    rw [← he,IsometryEquiv.symm_apply_apply,Homeomorph.symm_apply_apply]
    exact ha
  · intro ha
    exact ⟨A.symm x,⟨euclideanCoordinates.symm (A.symm x),ha,
      Homeomorph.apply_symm_apply _ _⟩,A.apply_symm_apply x⟩

private theorem planar_source_interior_iff (A : EPlane ≃ᵢ EPlane) (x : EPlane) :
    x ∈ interior (A '' euclideanBody) ↔
      euclideanCoordinates.symm (A.symm x) ∈ interior polygonBody := by
  have he : A '' interior euclideanBody = interior (A '' euclideanBody) :=
    A.toHomeomorph.image_interior _
  rw [← he,euclideanBody,← euclideanCoordinates.image_interior]
  constructor
  · rintro ⟨y,⟨a,ha,rfl⟩,he⟩
    rw [← he,IsometryEquiv.symm_apply_apply,Homeomorph.symm_apply_apply]
    exact ha
  · intro ha
    exact ⟨A.symm x,⟨euclideanCoordinates.symm (A.symm x),ha,
      Homeomorph.apply_symm_apply _ _⟩,A.apply_symm_apply x⟩

theorem product_active_component_slice_eq {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (P : ProductKeyPairing f) (b : Fin 2) (root : ι) (i : ProductActiveComponent P b root)
    (p : RealPoint) (x : EPlane) :
    productPlaneSlice (f root) b p x = f i.val (productFactorPoint b
      (euclideanCoordinates.symm ((productActiveComponentPlacement P b root i).symm x)) p) := by
  have he := product_active_component_placement_spec P b root i
    (euclideanCoordinates.symm ((productActiveComponentPlacement P b root i).symm x)) p
  simpa only [Homeomorph.apply_symm_apply,IsometryEquiv.apply_symm_apply,productPlaneSlice] using he.symm

theorem product_active_component_slice_mem_raw {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (P : ProductKeyPairing f) (b : Fin 2) (root : ι) (i : ProductActiveComponent P b root)
    (p : RealPoint) (x : EPlane) :
    productPlaneSlice (f root) b p x ∈ f i.val '' polygonProductBody ↔
      x ∈ productActiveComponentPlacement P b root i '' euclideanBody ∧ p ∈ polygonBody := by
  rw [product_active_component_slice_eq,(f i.val).injective.mem_set_image,
    product_factor_mem_raw,planar_source_body_iff]

theorem product_active_component_slice_mem_raw_interior {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (P : ProductKeyPairing f) (b : Fin 2) (root : ι) (i : ProductActiveComponent P b root)
    (p : RealPoint) (x : EPlane) :
    productPlaneSlice (f root) b p x ∈ interior (f i.val '' polygonProductBody) ↔
      x ∈ interior (productActiveComponentPlacement P b root i '' euclideanBody) ∧
        p ∈ interior polygonBody := by
  have he : f i.val '' interior polygonProductBody = interior (f i.val '' polygonProductBody) :=
    (f i.val).toHomeomorph.image_interior _
  rw [product_active_component_slice_eq,← he,(f i.val).injective.mem_set_image,
    product_factor_mem_raw_interior,planar_source_interior_iff]

theorem product_active_component_locallyFinite {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : PolygonProductPhysicalTiling f) (P : ProductKeyPairing f) (b : Fin 2) (root : ι) :
    LocallyFinite (fun i : ProductActiveComponent P b root =>
      productActiveComponentPlacement P b root i '' euclideanBody) := by
  obtain ⟨p,hp⟩ := polygonBody_interior_nonempty
  have hl := (physical_raw_product_locallyFinite T).comp_injective
    (Subtype.val_injective : Function.Injective (Subtype.val : ProductActiveComponent P b root → ι))
  have hpull := hl.preimage_continuous (product_plane_slice_continuous (f root) b p)
  apply hpull.subset
  intro i x hx
  exact (product_active_component_slice_mem_raw P b root i p x).mpr ⟨hx,interior_subset hp⟩

theorem product_active_component_union_closed {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : PolygonProductPhysicalTiling f) (P : ProductKeyPairing f) (b : Fin 2) (root : ι) :
    IsClosed (⋃ i : ProductActiveComponent P b root,
      productActiveComponentPlacement P b root i '' euclideanBody) :=
  (product_active_component_locallyFinite T P b root).isClosed_iUnion
    (fun i => (euclideanBody_compact.image (productActiveComponentPlacement P b root i).continuous).isClosed)

theorem product_active_component_countable {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : PolygonProductPhysicalTiling f) (P : ProductKeyPairing f) (b : Fin 2) (root : ι) :
    (univ : Set (ProductActiveComponent P b root)).Countable :=
  (product_active_component_locallyFinite T P b root).countable_univ
    (fun i => (euclideanBody_interior_nonempty.mono interior_subset).image _)

theorem product_active_component_interiors_disjoint {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (P : ProductKeyPairing f) (b : Fin 2) (root : ι)
    (hd : Pairwise fun i j => Disjoint (interior (f i '' polygonProductBody))
      (interior (f j '' polygonProductBody))) :
    Pairwise fun i j : ProductActiveComponent P b root =>
      Disjoint (interior (productActiveComponentPlacement P b root i '' euclideanBody))
        (interior (productActiveComponentPlacement P b root j '' euclideanBody)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  obtain ⟨p,hp⟩ := polygonBody_interior_nonempty
  have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  exact Set.disjoint_left.mp (hd hne)
    ((product_active_component_slice_mem_raw_interior P b root i p x).mpr ⟨hi,hp⟩)
    ((product_active_component_slice_mem_raw_interior P b root j p x).mpr ⟨hj,hp⟩)

end
end SpectreGeometry
