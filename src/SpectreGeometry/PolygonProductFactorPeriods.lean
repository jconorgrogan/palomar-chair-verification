module

public import SpectreGeometry.PolygonProductFactorTilings
public import SpectreGeometry.PolygonProductRawRangeSymmetry
public import SpectreGeometry.ProductTranslationComponents
public import SpectreGeometry.CartesianFamilyProjection
public import SpectreGeometry.TileFamilyConjugation

@[expose] public section


/-! Ordinary unmarked physical translation periods descend to genuine planar
factor-carrier collection periods. A nonzero ambient period has a nonzero
factor component. No hierarchy or ParentOccurrence input is assumed here. -/
namespace SpectreGeometry
noncomputable section
open Set

theorem range_over_range {I A B : Type*} (G : I → A) (Q : A → B) :
    Set.range (fun x : Set.range G => Q x.val) = Set.range (fun i => Q (G i)) := by
  ext b
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨i,hi⟩ := x.property
    exact ⟨i,congrArg Q hi⟩
  · rintro ⟨i,rfl⟩
    exact ⟨⟨G i,⟨i,rfl⟩⟩,rfl⟩

theorem physical_product_factor_periods {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    {root : ι} (F : ProductGlobalBlockSplitting f root)
    (T : PolygonProductPhysicalTiling f) (P : ProductKeyPairing f) (v : EFour)
    (hperiod : Set.range (fun i => (fun z : EFour => z+v) '' (f i '' polygonProductKeyBody)) =
      Set.range (fun i => f i '' polygonProductKeyBody)) :
    ∃ a b : EPlane,
      (a = 0 ∧ b = 0 ↔ v = 0) ∧
      (Set.range (fun A : ProductLeftFactors F =>
        (fun x : EPlane => x+a) '' (productLeftFactorPlacement F A '' euclideanBody)) =
        Set.range (fun A : ProductLeftFactors F => productLeftFactorPlacement F A '' euclideanBody)) ∧
      (Set.range (fun B : ProductRightFactors F =>
        (fun x : EPlane => x+b) '' (productRightFactorPlacement F B '' euclideanBody)) =
        Set.range (fun B : ProductRightFactors F => productRightFactorPlacement F B '' euclideanBody)) := by
  letI : Nonempty ι := ⟨root⟩
  obtain ⟨a,b,hab,hzero⟩ := ambient_translation_product_components (f root) v
  let H := productWorldCoordinates (f root)
  let s : EPlane × EPlane → EPlane × EPlane := fun p => (p.1+a,p.2+b)
  let A : ι → Set EPlane := fun i => F.left i '' euclideanBody
  let B : ι → Set EPlane := fun i => F.right i '' euclideanBody
  let C : ι → Set (EPlane × EPlane) := fun i => A i ×ˢ B i
  have hcomm : ∀ p, H (s p) = (fun z : EFour => z+v) (H p) := by
    rintro ⟨x,y⟩
    simpa only [H,s,productWorldCoordinates_apply,add_comm] using hab x y
  have hfamily : Set.range (fun i => H '' C i) = Set.range (fun i => f i '' polygonProductBody) := by
    congr 1
    funext i
    exact (F.image_body i).symm
  have hraw := physical_keyed_range_symmetry_preserves_raw f T (IsometryEquiv.addRight v) hperiod
  have hdiag := tile_family_symmetry_conjugate H H.injective s (fun z : EFour => z+v)
    C (fun i => f i '' polygonProductBody) hcomm hfamily hraw
  have hcart : Set.range C = cartesianTileFamily A B := F.cartesian_family T P
  have hcartperiod : Set.range (fun ij : ι × ι => s '' (A ij.1 ×ˢ B ij.2)) =
      cartesianTileFamily A B := by
    calc
      _ = (fun S : Set (EPlane × EPlane) => s '' S) '' cartesianTileFamily A B := Set.range_comp' _ _
      _ = (fun S : Set (EPlane × EPlane) => s '' S) '' Set.range C := by rw [hcart]
      _ = Set.range (fun i => s '' C i) := (Set.range_comp' _ _).symm
      _ = Set.range C := hdiag
      _ = cartesianTileFamily A B := hcart
  obtain ⟨hleft,hright⟩ := cartesian_family_symmetry_projects A B
    (fun i => (euclideanBody_interior_nonempty.mono interior_subset).image (F.left i))
    (fun i => (euclideanBody_interior_nonempty.mono interior_subset).image (F.right i))
    (fun x : EPlane => x+a) (fun y : EPlane => y+b) hcartperiod
  refine ⟨a,b,hzero,?_,?_⟩
  · change Set.range (fun A : Set.range F.left => (fun x : EPlane => x+a) '' (A.val '' euclideanBody)) =
      Set.range (fun A : Set.range F.left => A.val '' euclideanBody)
    exact (range_over_range F.left (fun L : EPlane ≃ᵢ EPlane =>
      (fun x : EPlane => x+a) '' (L '' euclideanBody))).trans
      (hleft.trans (range_over_range F.left (fun L : EPlane ≃ᵢ EPlane => L '' euclideanBody)).symm)
  · change Set.range (fun B : Set.range F.right => (fun x : EPlane => x+b) '' (B.val '' euclideanBody)) =
      Set.range (fun B : Set.range F.right => B.val '' euclideanBody)
    exact (range_over_range F.right (fun L : EPlane ≃ᵢ EPlane =>
      (fun x : EPlane => x+b) '' (L '' euclideanBody))).trans
      (hright.trans (range_over_range F.right (fun L : EPlane ≃ᵢ EPlane => L '' euclideanBody)).symm)

/-- A nonzero translation period of the actual keyed body forces a nonzero
ordinary carrier period of an actual proper planar P tiling. -/
theorem physical_nonzero_product_period_has_planar_factor {ι : Type*}
    {f : ι → EFour ≃ᵢ EFour} (T : PolygonProductPhysicalTiling f) (v : EFour) (hv : v ≠ 0)
    (hperiod : Set.range (fun i => (fun z : EFour => z+v) '' (f i '' polygonProductKeyBody)) =
      Set.range (fun i => f i '' polygonProductKeyBody)) :
    ∃ (κ : Type) (g : κ → EPlane ≃ᵢ EPlane) (w : EPlane),
      w ≠ 0 ∧ (∀ k, DirectPlacement (g k)) ∧
      (Pairwise fun i j => Disjoint (interior (g i '' euclideanBody))
        (interior (g j '' euclideanBody))) ∧
      (∀ x, ∃ k, x ∈ g k '' euclideanBody) ∧
      (Set.range (fun k => (fun x : EPlane => x+w) '' (g k '' euclideanBody)) =
        Set.range (fun k => g k '' euclideanBody)) := by
  obtain ⟨root,_⟩ := T.covers 0
  obtain ⟨P⟩ := exists_productKeyPairing T
  obtain ⟨F⟩ := physical_product_global_block_splitting T P root
  obtain ⟨a,b,hzero,hleft,hright⟩ := physical_product_factor_periods F T P v hperiod
  by_cases ha : a = 0
  · have hb : b ≠ 0 := fun hb => hv (hzero.mp ⟨ha,hb⟩)
    exact ⟨ProductRightFactors F,productRightFactorPlacement F,b,hb,
      product_right_factor_direct F,product_right_factors_pack F T P,
      product_right_factors_cover F T P,hright⟩
  · exact ⟨ProductLeftFactors F,productLeftFactorPlacement F,a,ha,
      product_left_factor_direct F,product_left_factors_pack F T P,
      product_left_factors_cover F T P,hleft⟩

end
end SpectreGeometry
