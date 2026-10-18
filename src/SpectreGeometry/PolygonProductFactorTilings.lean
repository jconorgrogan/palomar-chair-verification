module

public import SpectreGeometry.PolygonProductCartesianConsistency

@[expose] public section


/-! Genuine homochiral planar tilings indexed by the distinct forced factor
placements. Duplicate occurrences in transverse columns are removed by exact
placement equality, whose consistency was proved from actual raw packing. -/
namespace SpectreGeometry
noncomputable section
open Set

abbrev ProductLeftFactors {ι : Type*} {f : ι → EFour ≃ᵢ EFour} {root : ι}
    (F : ProductGlobalBlockSplitting f root) := Set.range F.left

abbrev ProductRightFactors {ι : Type*} {f : ι → EFour ≃ᵢ EFour} {root : ι}
    (F : ProductGlobalBlockSplitting f root) := Set.range F.right

def productLeftFactorPlacement {ι : Type*} {f : ι → EFour ≃ᵢ EFour} {root : ι}
    (F : ProductGlobalBlockSplitting f root) (i : ProductLeftFactors F) : EPlane ≃ᵢ EPlane := i.val

def productRightFactorPlacement {ι : Type*} {f : ι → EFour ≃ᵢ EFour} {root : ι}
    (F : ProductGlobalBlockSplitting f root) (i : ProductRightFactors F) : EPlane ≃ᵢ EPlane := i.val

theorem product_left_factor_direct {ι : Type*} {f : ι → EFour ≃ᵢ EFour} {root : ι}
    (F : ProductGlobalBlockSplitting f root) (A : ProductLeftFactors F) :
    DirectPlacement (productLeftFactorPlacement F A) := by
  obtain ⟨i,hi⟩ := A.property
  change DirectPlacement A.val
  rw [← hi]
  exact F.left_direct i

theorem product_right_factor_direct {ι : Type*} {f : ι → EFour ≃ᵢ EFour} {root : ι}
    (F : ProductGlobalBlockSplitting f root) (A : ProductRightFactors F) :
    DirectPlacement (productRightFactorPlacement F A) := by
  obtain ⟨i,hi⟩ := A.property
  change DirectPlacement A.val
  rw [← hi]
  exact F.right_direct i

theorem product_left_factors_pack {ι : Type*} {f : ι → EFour ≃ᵢ EFour} {root : ι}
    (F : ProductGlobalBlockSplitting f root) (T : PolygonProductPhysicalTiling f)
    (P : ProductKeyPairing f) :
    Pairwise fun A B : ProductLeftFactors F =>
      Disjoint (interior (productLeftFactorPlacement F A '' euclideanBody))
        (interior (productLeftFactorPlacement F B '' euclideanBody)) := by
  intro A B hne
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i,hi⟩ := A.property
  obtain ⟨j,hj⟩ := B.property
  have hx' : x ∈ interior (F.left i '' euclideanBody) := by simpa only [hi,productLeftFactorPlacement] using hx
  have hy' : x ∈ interior (F.left j '' euclideanBody) := by simpa only [hj,productLeftFactorPlacement] using hy
  apply hne
  apply Subtype.ext
  exact hi.symm.trans ((F.left_eq_of_interior_overlap T P i j ⟨x,hx',hy'⟩).trans hj)

theorem product_right_factors_pack {ι : Type*} {f : ι → EFour ≃ᵢ EFour} {root : ι}
    (F : ProductGlobalBlockSplitting f root) (T : PolygonProductPhysicalTiling f)
    (P : ProductKeyPairing f) :
    Pairwise fun A B : ProductRightFactors F =>
      Disjoint (interior (productRightFactorPlacement F A '' euclideanBody))
        (interior (productRightFactorPlacement F B '' euclideanBody)) := by
  intro A B hne
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i,hi⟩ := A.property
  obtain ⟨j,hj⟩ := B.property
  have hx' : x ∈ interior (F.right i '' euclideanBody) := by simpa only [hi,productRightFactorPlacement] using hx
  have hy' : x ∈ interior (F.right j '' euclideanBody) := by simpa only [hj,productRightFactorPlacement] using hy
  apply hne
  apply Subtype.ext
  exact hi.symm.trans ((F.right_eq_of_interior_overlap T P i j ⟨x,hx',hy'⟩).trans hj)

theorem product_left_factors_cover {ι : Type*} {f : ι → EFour ≃ᵢ EFour} {root : ι}
    (F : ProductGlobalBlockSplitting f root) (T : PolygonProductPhysicalTiling f)
    (P : ProductKeyPairing f) (x : EPlane) :
    ∃ A : ProductLeftFactors F, x ∈ productLeftFactorPlacement F A '' euclideanBody := by
  obtain ⟨i,hi⟩ := raw_product_carriers_cover_of_pairing T P (productWorldCoordinates (f root) (x,0))
  exact ⟨⟨F.left i,⟨i,rfl⟩⟩,((F.mem_raw i x 0).mp hi).1⟩

theorem product_right_factors_cover {ι : Type*} {f : ι → EFour ≃ᵢ EFour} {root : ι}
    (F : ProductGlobalBlockSplitting f root) (T : PolygonProductPhysicalTiling f)
    (P : ProductKeyPairing f) (x : EPlane) :
    ∃ A : ProductRightFactors F, x ∈ productRightFactorPlacement F A '' euclideanBody := by
  obtain ⟨i,hi⟩ := raw_product_carriers_cover_of_pairing T P (productWorldCoordinates (f root) (0,x))
  exact ⟨⟨F.right i,⟨i,rfl⟩⟩,((F.mem_raw i 0 x).mp hi).2⟩

theorem product_factor_pair_realized {ι : Type*} {f : ι → EFour ≃ᵢ EFour} {root : ι}
    (F : ProductGlobalBlockSplitting f root) (T : PolygonProductPhysicalTiling f)
    (P : ProductKeyPairing f) (A : ProductLeftFactors F) (B : ProductRightFactors F) :
    ∃ k, f k '' polygonProductBody = productWorldCoordinates (f root) ''
      ((productLeftFactorPlacement F A '' euclideanBody) ×ˢ
        (productRightFactorPlacement F B '' euclideanBody)) := by
  obtain ⟨i,hi⟩ := A.property
  obtain ⟨j,hj⟩ := B.property
  obtain ⟨k,hki,hkj⟩ := F.every_factor_pair T P i j
  refine ⟨k,?_⟩
  rw [F.image_body,hki,hkj,hi,hj]
  rfl

/-- The physical tiling determines two actual complete homochiral planar
factor tilings, and every pair of their factors occurs as a raw tile. -/
theorem physical_product_complete_cartesian_factors {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : PolygonProductPhysicalTiling f) (root : ι) :
    ∃ (P : ProductKeyPairing f) (F : ProductGlobalBlockSplitting f root),
      (∀ A : ProductLeftFactors F, DirectPlacement (productLeftFactorPlacement F A)) ∧
      (Pairwise fun A B : ProductLeftFactors F =>
        Disjoint (interior (productLeftFactorPlacement F A '' euclideanBody))
          (interior (productLeftFactorPlacement F B '' euclideanBody))) ∧
      (∀ x, ∃ A : ProductLeftFactors F, x ∈ productLeftFactorPlacement F A '' euclideanBody) ∧
      (∀ A : ProductRightFactors F, DirectPlacement (productRightFactorPlacement F A)) ∧
      (Pairwise fun A B : ProductRightFactors F =>
        Disjoint (interior (productRightFactorPlacement F A '' euclideanBody))
          (interior (productRightFactorPlacement F B '' euclideanBody))) ∧
      (∀ x, ∃ A : ProductRightFactors F, x ∈ productRightFactorPlacement F A '' euclideanBody) ∧
      (∀ (A : ProductLeftFactors F) (B : ProductRightFactors F),
        ∃ k, f k '' polygonProductBody = productWorldCoordinates (f root) ''
          ((productLeftFactorPlacement F A '' euclideanBody) ×ˢ
            (productRightFactorPlacement F B '' euclideanBody))) := by
  obtain ⟨P⟩ := exists_productKeyPairing T
  obtain ⟨F⟩ := physical_product_global_block_splitting T P root
  exact ⟨P,F,product_left_factor_direct F,product_left_factors_pack F T P,
    product_left_factors_cover F T P,product_right_factor_direct F,
    product_right_factors_pack F T P,product_right_factors_cover F T P,
    product_factor_pair_realized F T P⟩

end
end SpectreGeometry
