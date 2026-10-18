module

public import SpectreGeometry.PolygonProductBlockCoordinates

@[expose] public section


/-! Transverse completeness and raw packing force equal overlapping factor
arrangements and realize every factor pair. Complete columns alone are not
used as a substitute for this Cartesian consistency argument. -/
namespace SpectreGeometry
noncomputable section
open Set

theorem planar_placement_interior_nonempty (A : EPlane ≃ᵢ EPlane) :
    (interior (A '' euclideanBody)).Nonempty := by
  obtain ⟨x,hx⟩ := euclideanBody_interior_nonempty
  exact ⟨A x,A.toHomeomorph.isOpenMap.image_interior_subset _ ⟨x,hx,rfl⟩⟩

theorem physical_raw_open_subcover_has_interior {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : PolygonProductPhysicalTiling f) (S : Set ι) (K U : Set EFour)
    (hK : IsCompact K) (hU : IsOpen U) (hne : U.Nonempty) (hUK : U ⊆ K)
    (hcover : ∀ x ∈ U, ∃ i ∈ S, x ∈ f i '' polygonProductBody) :
    ∃ i ∈ S, (U ∩ interior (f i '' polygonProductBody)).Nonempty := by
  classical
  let J : Set ι := {i | (f i '' polygonProductBody ∩ K).Nonempty}
  have hJ : J.Finite := physical_raw_product_finite_inter_compact T K hK
  letI : Fintype J := hJ.fintype
  obtain ⟨x,hx,ha⟩ := FiniteMaterialAvoidance.exists_mem_open_avoid_frontiers
    (fun i : J => f i.val '' polygonProductBody)
    (fun i => (polygon_product_body_isCompact.image (f i.val).continuous).isClosed) U hU hne
  obtain ⟨i,hi,hxi⟩ := hcover x hx
  have hiJ : i ∈ J := ⟨x,hxi,hUK hx⟩
  refine ⟨i,hi,x,hx,?_⟩
  by_contra hn
  exact ha ⟨i,hiJ⟩ ⟨subset_closure hxi,hn⟩

theorem physical_raw_local_subcover_contains {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : PolygonProductPhysicalTiling f) (P : ProductKeyPairing f)
    (S : Set ι) (j : ι) (U : Set EFour) (hU : IsOpen U) (hne : U.Nonempty)
    (hUj : U ⊆ interior (f j '' polygonProductBody))
    (hcover : ∀ x ∈ U, ∃ i ∈ S, x ∈ f i '' polygonProductBody) : j ∈ S := by
  obtain ⟨i,hi,x,hx,hxi⟩ := physical_raw_open_subcover_has_interior T S
    (f j '' polygonProductBody) U (polygon_product_body_isCompact.image (f j).continuous)
    hU hne (hUj.trans interior_subset) hcover
  have he : i = j := by
    by_contra hn
    exact Set.disjoint_left.mp (raw_product_interiors_disjoint_of_pairing T P hn) hxi (hUj hx)
  exact he ▸ hi

theorem ProductGlobalBlockSplitting.left_eq_of_interior_overlap {ι : Type*}
    {f : ι → EFour ≃ᵢ EFour} {root : ι} (F : ProductGlobalBlockSplitting f root)
    (T : PolygonProductPhysicalTiling f) (P : ProductKeyPairing f) (i j : ι)
    (h : (interior (F.left i '' euclideanBody) ∩ interior (F.left j '' euclideanBody)).Nonempty) :
    F.left i = F.left j := by
  let H := productWorldCoordinates (f root)
  let U := H '' ((interior (F.left i '' euclideanBody) ∩
    interior (F.left j '' euclideanBody)) ×ˢ interior (F.right j '' euclideanBody))
  have hU : IsOpen U := H.isOpenMap _ ((isOpen_interior.inter isOpen_interior).prod isOpen_interior)
  have hne : U.Nonempty := (h.prod (planar_placement_interior_nonempty (F.right j))).image H
  have hj : Relation.EqvGen (ProductActiveStep P 1) i j := by
    apply physical_raw_local_subcover_contains T P
      {k | Relation.EqvGen (ProductActiveStep P 1) i k} j U hU hne
    · rintro _ ⟨⟨x,y⟩,⟨⟨hxi,hxj⟩,hyj⟩,rfl⟩
      exact (F.mem_raw_interior j x y).mpr ⟨hxj,hyj⟩
    · rintro _ ⟨⟨x,y⟩,⟨⟨hxi,hxj⟩,hyj⟩,rfl⟩
      obtain ⟨k,hk⟩ := F.component_one_covers_slab T P i x y (interior_subset hxi)
      exact ⟨k.val,k.property,hk⟩
  exact (F.component_one_left P i ⟨j,hj⟩).symm

theorem ProductGlobalBlockSplitting.right_eq_of_interior_overlap {ι : Type*}
    {f : ι → EFour ≃ᵢ EFour} {root : ι} (F : ProductGlobalBlockSplitting f root)
    (T : PolygonProductPhysicalTiling f) (P : ProductKeyPairing f) (i j : ι)
    (h : (interior (F.right i '' euclideanBody) ∩ interior (F.right j '' euclideanBody)).Nonempty) :
    F.right i = F.right j := by
  let H := productWorldCoordinates (f root)
  let U := H '' (interior (F.left j '' euclideanBody) ×ˢ
    (interior (F.right i '' euclideanBody) ∩ interior (F.right j '' euclideanBody)))
  have hU : IsOpen U := H.isOpenMap _ (isOpen_interior.prod (isOpen_interior.inter isOpen_interior))
  have hne : U.Nonempty := ((planar_placement_interior_nonempty (F.left j)).prod h).image H
  have hj : Relation.EqvGen (ProductActiveStep P 0) i j := by
    apply physical_raw_local_subcover_contains T P
      {k | Relation.EqvGen (ProductActiveStep P 0) i k} j U hU hne
    · rintro _ ⟨⟨x,y⟩,⟨hxj,⟨hyi,hyj⟩⟩,rfl⟩
      exact (F.mem_raw_interior j x y).mpr ⟨hxj,hyj⟩
    · rintro _ ⟨⟨x,y⟩,⟨hxj,⟨hyi,hyj⟩⟩,rfl⟩
      obtain ⟨k,hk⟩ := F.component_zero_covers_slab T P i x y (interior_subset hyi)
      exact ⟨k.val,k.property,hk⟩
  exact (F.component_zero_right P i ⟨j,hj⟩).symm

theorem ProductGlobalBlockSplitting.every_factor_pair {ι : Type*}
    {f : ι → EFour ≃ᵢ EFour} {root : ι} (F : ProductGlobalBlockSplitting f root)
    (T : PolygonProductPhysicalTiling f) (P : ProductKeyPairing f) (i j : ι) :
    ∃ k, F.left k = F.left i ∧ F.right k = F.right j := by
  let H := productWorldCoordinates (f root)
  let K := H '' ((F.left i '' euclideanBody) ×ˢ (F.right j '' euclideanBody))
  let U := H '' (interior (F.left i '' euclideanBody) ×ˢ interior (F.right j '' euclideanBody))
  have hK : IsCompact K := ((euclideanBody_compact.image (F.left i).continuous).prod
    (euclideanBody_compact.image (F.right j).continuous)).image H.continuous
  have hU : IsOpen U := H.isOpenMap _ (isOpen_interior.prod isOpen_interior)
  have hne : U.Nonempty := ((planar_placement_interior_nonempty (F.left i)).prod
    (planar_placement_interior_nonempty (F.right j))).image H
  have hUK : U ⊆ K := image_mono (Set.prod_mono interior_subset interior_subset)
  obtain ⟨k,_,z,hz,hzk⟩ := physical_raw_open_subcover_has_interior T univ K U hK hU hne hUK
    (fun z _ => by
      obtain ⟨k,hk⟩ := raw_product_carriers_cover_of_pairing T P z
      exact ⟨k,mem_univ k,hk⟩)
  obtain ⟨⟨x,y⟩,⟨hxi,hyj⟩,rfl⟩ := hz
  obtain ⟨hxk,hyk⟩ := (F.mem_raw_interior k x y).mp hzk
  exact ⟨k,F.left_eq_of_interior_overlap T P k i ⟨x,hxk,hxi⟩,
    F.right_eq_of_interior_overlap T P k j ⟨y,hyk,hyj⟩⟩

theorem ProductGlobalBlockSplitting.cartesian_family {ι : Type*}
    {f : ι → EFour ≃ᵢ EFour} {root : ι} (F : ProductGlobalBlockSplitting f root)
    (T : PolygonProductPhysicalTiling f) (P : ProductKeyPairing f) :
    Set.range (fun k => (F.left k '' euclideanBody) ×ˢ (F.right k '' euclideanBody)) =
      Set.range (fun ij : ι × ι => (F.left ij.1 '' euclideanBody) ×ˢ (F.right ij.2 '' euclideanBody)) := by
  ext S
  constructor
  · rintro ⟨k,rfl⟩
    exact ⟨(k,k),rfl⟩
  · rintro ⟨⟨i,j⟩,rfl⟩
    obtain ⟨k,hki,hkj⟩ := F.every_factor_pair T P i j
    refine ⟨k,?_⟩
    change (F.left k '' euclideanBody) ×ˢ (F.right k '' euclideanBody) =
      (F.left i '' euclideanBody) ×ˢ (F.right j '' euclideanBody)
    rw [hki,hkj]

end
end SpectreGeometry
