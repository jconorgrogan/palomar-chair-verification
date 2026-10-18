module

public import SpectreGeometry.PolygonProductActiveCompleteness

@[expose] public section


/-! Global, labeled, proper two-block splitting is forced by two transverse
complete active columns. No connectivity or Cartesian-product premise is
assumed. A full raw subcover contains every tile by finite frontier avoidance
and raw interior packing. -/
namespace SpectreGeometry
noncomputable section
open Set

/-- Every full subcover of a locally finite raw packing contains every tile. -/
theorem physical_raw_subcover_contains_all {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : PolygonProductPhysicalTiling f) (P : ProductKeyPairing f)
    (S : Set ι) (hcover : ∀ x, ∃ i ∈ S, x ∈ f i '' polygonProductBody) :
    ∀ j, j ∈ S := by
  classical
  intro j
  let K := f j '' polygonProductBody
  have hK : IsCompact K := polygon_product_body_isCompact.image (f j).continuous
  let J : Set ι := {i | (f i '' polygonProductBody ∩ K).Nonempty}
  have hJ : J.Finite := physical_raw_product_finite_inter_compact T K hK
  letI : Fintype J := hJ.fintype
  have hne : (interior K).Nonempty := by
    obtain ⟨p,hp⟩ := polygonBody_interior_nonempty
    have hx : productFactorPoint 0 p p ∈ interior polygonProductBody :=
      (product_factor_mem_raw_interior 0 p p).mpr ⟨hp,hp⟩
    exact ⟨f j (productFactorPoint 0 p p),
      (f j).toHomeomorph.isOpenMap.image_interior_subset _ ⟨_,hx,rfl⟩⟩
  obtain ⟨x,hx,ha⟩ := FiniteMaterialAvoidance.exists_mem_open_avoid_frontiers
    (fun i : J => f i.val '' polygonProductBody)
    (fun i => (polygon_product_body_isCompact.image (f i.val).continuous).isClosed)
    (interior K) isOpen_interior hne
  obtain ⟨i,hi,hxi⟩ := hcover x
  have hiJ : i ∈ J := ⟨x,hxi,interior_subset hx⟩
  have hxi' : x ∈ interior (f i '' polygonProductBody) := by
    by_contra hn
    exact ha ⟨i,hiJ⟩ ⟨subset_closure hxi,hn⟩
  have he : i = j := by
    by_contra hn
    exact Set.disjoint_left.mp (raw_product_interiors_disjoint_of_pairing T P hn) hxi' hx
  exact he ▸ hi

/-- Two complete transverse columns through a root already cover four-space. -/
theorem product_two_step_components_cover {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : PolygonProductPhysicalTiling f) (P : ProductKeyPairing f) (root : ι)
    (z : EFour) :
    ∃ (i : ProductActiveComponent P 0 root) (j : ProductActiveComponent P 1 i.val),
      z ∈ f j.val '' polygonProductBody := by
  obtain ⟨⟨a,p⟩,hz⟩ := productCoordinates.surjective ((f root).symm z)
  have hz' : f root (productFactorPoint 0 a p) = z := by
    simpa [productFactorPoint] using congrArg (f root) hz
  obtain ⟨i,ai,hai,hei⟩ := product_active_component_covers T P 0 root (euclideanCoordinates a)
  obtain ⟨a0,ha0,rfl⟩ := hai
  obtain ⟨j,pj,hpj,hej⟩ := product_active_component_covers T P 1 i.val (euclideanCoordinates p)
  obtain ⟨p0,hp0,rfl⟩ := hpj
  refine ⟨i,j,productFactorPoint 0 a0 p0,(product_factor_mem_raw 0 a0 p0).mpr ⟨ha0,hp0⟩,?_⟩
  have h1 := product_active_component_placement_spec P 1 i.val j p0 a0
  have h0 := product_active_component_placement_spec P 0 root i a0 p
  have hj : f j.val (productFactorPoint 0 a0 p0) = f i.val (productFactorPoint 0 a0 p) := by
    simpa [productFactorPoint,hej] using h1
  have hi : f i.val (productFactorPoint 0 a0 p) = f root (productFactorPoint 0 a p) := by
    simpa only [hei,Homeomorph.symm_apply_apply] using h0
  exact hj.trans (hi.trans hz')

/-- Every placement is reached by a label-0 then label-1 active path. -/
theorem product_every_tile_two_step {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : PolygonProductPhysicalTiling f) (P : ProductKeyPairing f) (root k : ι) :
    ∃ (i : ProductActiveComponent P 0 root) (j : ProductActiveComponent P 1 i.val),
      j.val = k := by
  apply physical_raw_subcover_contains_all T P
    {k | ∃ (i : ProductActiveComponent P 0 root) (j : ProductActiveComponent P 1 i.val),j.val = k}
  intro z
  obtain ⟨i,j,hj⟩ := product_two_step_components_cover T P root z
  exact ⟨j.val,⟨i,j,rfl⟩,hj⟩

structure ProductGlobalBlockSplitting {ι : Type*} (f : ι → EFour ≃ᵢ EFour) (root : ι) where
  left : ι → EPlane ≃ᵢ EPlane
  right : ι → EPlane ≃ᵢ EPlane
  left_direct : ∀ i, DirectPlacement (left i)
  right_direct : ∀ i, DirectPlacement (right i)
  placement : ∀ (i : ι) (a p : RealPoint),
    f i (productFactorPoint 0 a p) = f root (productFactorPoint 0
      (euclideanCoordinates.symm (left i (euclideanCoordinates a)))
      (euclideanCoordinates.symm (right i (euclideanCoordinates p))))

/-- The two factors retain their intrinsic labels and proper orientation globally. -/
theorem physical_product_global_block_splitting {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : PolygonProductPhysicalTiling f) (P : ProductKeyPairing f) (root : ι) :
    Nonempty (ProductGlobalBlockSplitting f root) := by
  classical
  choose i j hj using product_every_tile_two_step T P root
  refine ⟨⟨(fun k => productActiveComponentPlacement P 0 root (i k)),
    (fun k => productActiveComponentPlacement P 1 (i k).val (j k)),
    (fun k => product_active_component_placement_direct P 0 root (i k)),
    (fun k => product_active_component_placement_direct P 1 (i k).val (j k)),?_⟩⟩
  intro k a p
  have h1 := product_active_component_placement_spec P 1 (i k).val (j k) p a
  rw [hj k] at h1
  have h0 := product_active_component_placement_spec P 0 root (i k) a
    (euclideanCoordinates.symm (productActiveComponentPlacement P 1 (i k).val (j k) (euclideanCoordinates p)))
  have hj' : f k (productFactorPoint 0 a p) = f (i k).val (productFactorPoint 0 a
      (euclideanCoordinates.symm (productActiveComponentPlacement P 1 (i k).val (j k) (euclideanCoordinates p)))) := by
    simpa [productFactorPoint] using h1
  exact hj'.trans h0

end
end SpectreGeometry
