module

public import SpectreGeometry.PolygonProductGlobalBlocks
public import SpectreGeometry.PolygonProductRawExistence

@[expose] public section


/-! Coordinate formulas for the forced global splitting and its complete
transverse columns. No equality of distinct factor arrangements is assumed. -/
namespace SpectreGeometry
noncomputable section
open Set

def productWorldCoordinates (g : EFour ≃ᵢ EFour) : (EPlane × EPlane) ≃ₜ EFour :=
  euclideanProductCoordinates.trans g.toHomeomorph

@[simp] theorem productWorldCoordinates_apply (g : EFour ≃ᵢ EFour) (x y : EPlane) :
    productWorldCoordinates g (x,y) = g (euclideanProductCoordinates (x,y)) := rfl

theorem ProductGlobalBlockSplitting.placement_eq {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    {root : ι} (F : ProductGlobalBlockSplitting f root) (i : ι) :
    f i = (productPlacement (F.left i) (F.right i)).trans (f root) := by
  apply DFunLike.ext
  intro z
  obtain ⟨⟨x,y⟩,rfl⟩ := euclideanProductCoordinates.surjective z
  change f i (productFactorPoint 0 (euclideanCoordinates.symm x) (euclideanCoordinates.symm y)) =
    f root (productPlacement (F.left i) (F.right i) (euclideanProductCoordinates (x,y)))
  rw [productPlacement_apply,F.placement]
  simp only [Homeomorph.apply_symm_apply]
  rfl

theorem ProductGlobalBlockSplitting.image_body {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    {root : ι} (F : ProductGlobalBlockSplitting f root) (i : ι) :
    f i '' polygonProductBody = productWorldCoordinates (f root) ''
      ((F.left i '' euclideanBody) ×ˢ (F.right i '' euclideanBody)) := by
  rw [F.placement_eq i]
  change (fun x => f root (productPlacement (F.left i) (F.right i) x)) '' polygonProductBody = _
  rw [← Set.image_image,productPlacement_image_body,Set.image_image]
  rfl

theorem ProductGlobalBlockSplitting.mem_raw {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    {root : ι} (F : ProductGlobalBlockSplitting f root) (i : ι) (x y : EPlane) :
    productWorldCoordinates (f root) (x,y) ∈ f i '' polygonProductBody ↔
      x ∈ F.left i '' euclideanBody ∧ y ∈ F.right i '' euclideanBody := by
  rw [F.image_body,(productWorldCoordinates (f root)).injective.mem_set_image]
  rfl

theorem ProductGlobalBlockSplitting.mem_raw_interior {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    {root : ι} (F : ProductGlobalBlockSplitting f root) (i : ι) (x y : EPlane) :
    productWorldCoordinates (f root) (x,y) ∈ interior (f i '' polygonProductBody) ↔
      x ∈ interior (F.left i '' euclideanBody) ∧ y ∈ interior (F.right i '' euclideanBody) := by
  rw [F.image_body,← (productWorldCoordinates (f root)).image_interior,
    (productWorldCoordinates (f root)).injective.mem_set_image,interior_prod_eq]
  rfl

theorem ProductGlobalBlockSplitting.component_zero_coordinates {ι : Type*}
    {f : ι → EFour ≃ᵢ EFour} {root : ι} (F : ProductGlobalBlockSplitting f root)
    (P : ProductKeyPairing f) (i : ι) (j : ProductActiveComponent P 0 i) (x y : EPlane) :
    (F.left j.val x,F.right j.val y) =
      (F.left i (productActiveComponentPlacement P 0 i j x),F.right i y) := by
  have he := product_active_component_placement_spec P 0 i j
    (euclideanCoordinates.symm x) (euclideanCoordinates.symm y)
  simp only [Homeomorph.apply_symm_apply] at he
  change f j.val (euclideanProductCoordinates (x,y)) =
    f i (euclideanProductCoordinates (productActiveComponentPlacement P 0 i j x,y)) at he
  rw [F.placement_eq j.val,F.placement_eq i] at he
  simp only [IsometryEquiv.trans_apply,productPlacement_apply] at he
  exact euclideanProductCoordinates.injective ((f root).injective he)

theorem ProductGlobalBlockSplitting.component_one_coordinates {ι : Type*}
    {f : ι → EFour ≃ᵢ EFour} {root : ι} (F : ProductGlobalBlockSplitting f root)
    (P : ProductKeyPairing f) (i : ι) (j : ProductActiveComponent P 1 i) (x y : EPlane) :
    (F.left j.val x,F.right j.val y) =
      (F.left i x,F.right i (productActiveComponentPlacement P 1 i j y)) := by
  have he := product_active_component_placement_spec P 1 i j
    (euclideanCoordinates.symm y) (euclideanCoordinates.symm x)
  simp only [Homeomorph.apply_symm_apply] at he
  change f j.val (euclideanProductCoordinates (x,y)) =
    f i (euclideanProductCoordinates (x,productActiveComponentPlacement P 1 i j y)) at he
  rw [F.placement_eq j.val,F.placement_eq i] at he
  simp only [IsometryEquiv.trans_apply,productPlacement_apply] at he
  exact euclideanProductCoordinates.injective ((f root).injective he)

theorem ProductGlobalBlockSplitting.component_zero_right {ι : Type*}
    {f : ι → EFour ≃ᵢ EFour} {root : ι} (F : ProductGlobalBlockSplitting f root)
    (P : ProductKeyPairing f) (i : ι) (j : ProductActiveComponent P 0 i) :
    F.right j.val = F.right i := by
  apply DFunLike.ext
  intro y
  exact congrArg Prod.snd (F.component_zero_coordinates P i j 0 y)

theorem ProductGlobalBlockSplitting.component_one_left {ι : Type*}
    {f : ι → EFour ≃ᵢ EFour} {root : ι} (F : ProductGlobalBlockSplitting f root)
    (P : ProductKeyPairing f) (i : ι) (j : ProductActiveComponent P 1 i) :
    F.left j.val = F.left i := by
  apply DFunLike.ext
  intro x
  exact congrArg Prod.fst (F.component_one_coordinates P i j x 0)

theorem ProductGlobalBlockSplitting.component_zero_covers_slab {ι : Type*}
    {f : ι → EFour ≃ᵢ EFour} {root : ι} (F : ProductGlobalBlockSplitting f root)
    (T : PolygonProductPhysicalTiling f) (P : ProductKeyPairing f) (i : ι)
    (x y : EPlane) (hy : y ∈ F.right i '' euclideanBody) :
    ∃ j : ProductActiveComponent P 0 i,
      productWorldCoordinates (f root) (x,y) ∈ f j.val '' polygonProductBody := by
  obtain ⟨j,a,ha,he⟩ := product_active_component_covers T P 0 i ((F.left i).symm x)
  refine ⟨j,(F.mem_raw j.val x y).mpr ⟨?_,?_⟩⟩
  · refine ⟨a,ha,?_⟩
    have hh := congrArg Prod.fst (F.component_zero_coordinates P i j a 0)
    simpa only [he,IsometryEquiv.apply_symm_apply] using hh
  · rwa [F.component_zero_right P i j]

theorem ProductGlobalBlockSplitting.component_one_covers_slab {ι : Type*}
    {f : ι → EFour ≃ᵢ EFour} {root : ι} (F : ProductGlobalBlockSplitting f root)
    (T : PolygonProductPhysicalTiling f) (P : ProductKeyPairing f) (i : ι)
    (x y : EPlane) (hx : x ∈ F.left i '' euclideanBody) :
    ∃ j : ProductActiveComponent P 1 i,
      productWorldCoordinates (f root) (x,y) ∈ f j.val '' polygonProductBody := by
  obtain ⟨j,a,ha,he⟩ := product_active_component_covers T P 1 i ((F.right i).symm y)
  refine ⟨j,(F.mem_raw j.val x y).mpr ⟨?_,?_⟩⟩
  · rwa [F.component_one_left P i j]
  · refine ⟨a,ha,?_⟩
    have hh := congrArg Prod.snd (F.component_one_coordinates P i j 0 a)
    simpa only [he,IsometryEquiv.apply_symm_apply] using hh

end
end SpectreGeometry
