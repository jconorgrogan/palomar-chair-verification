module

public import SpectreGeometry.PolygonProductKeyCompanionEquality
public import SpectreGeometry.PolygonProductKeyPairedMaterial
public import SpectreGeometry.PolygonProductKeyRawAgreement

@[expose] public section


namespace SpectreGeometry
open Set ProductCrease
noncomputable section

/-- A selected physical whole-key companion, with all geometric data explicit. -/
structure ProductKeyPairing {ι : Type*} (f : ι → EFour ≃ᵢ EFour) where
  partner : ι → ProductKeySite → ι × ProductKeySite
  different : ∀ i u, (partner i u).1 ≠ i
  sameLabel : ∀ i u, u.1 = (partner i u).2.1
  samePose : ∀ i u,
    (productKeySignedAffineIsometry u).toIsometryEquiv.trans (f i) =
      (productKeySignedAffineIsometry (partner i u).2).toIsometryEquiv.trans (f (partner i u).1)
  oppositeSigns : ∀ i u, productKeySign (partner i u).2 = -productKeySign u

theorem exists_productKeyPairing {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : PolygonProductPhysicalTiling f) : Nonempty (ProductKeyPairing f) := by
  classical
  choose j v hd hl hp using physical_key_pose_registration T
  refine ⟨⟨fun i u => (j i u,v i u),hd,hl,hp,?_⟩⟩
  intro i u
  exact coincident_signed_poses_opposite_signs u (v i u) (f i) (f (j i u))
    (T.interiors_disjoint (Ne.symm (hd i u))) (hp i u)

theorem ProductKeyPairing.collars {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (P : ProductKeyPairing f) (i : ι) (u : ProductKeySite) :
    f i '' productKeyCollar u = f (P.partner i u).1 '' productKeyCollar (P.partner i u).2 :=
  coincident_signed_poses_collars _ _ _ _ (P.samePose i u)

theorem ProductKeyPairing.actual_cover {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (P : ProductKeyPairing f) (i : ι) (u : ProductKeySite) :
    f i '' productKeyCollar u ⊆ placedPolygonProductKeyBody (f i) ∪
      placedPolygonProductKeyBody (f (P.partner i u).1) :=
  paired_actual_bodies_cover_collar _ _ _ _ (P.sameLabel i u) (P.oppositeSigns i u) (P.samePose i u)

theorem ProductKeyPairing.raw_cover {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (P : ProductKeyPairing f) (i : ι) (u : ProductKeySite) :
    f i '' productKeyCollar u ⊆ (f i '' polygonProductBody) ∪
      (f (P.partner i u).1 '' polygonProductBody) :=
  paired_raw_bodies_cover_collar _ _ _ _ (P.oppositeSigns i u) (P.samePose i u)

theorem placed_key_change_mem_collar_interior (f : EFour ≃ᵢ EFour) (x : EFour)
    (hne : ¬ (x ∈ f '' polygonProductKeyBody ↔ x ∈ f '' polygonProductBody)) :
    ∃ u, x ∈ f '' interior (productKeyCollar u) := by
  obtain ⟨y,rfl⟩ := f.surjective x
  have hh : ¬ (y ∈ polygonProductKeyBody ↔ y ∈ polygonProductBody) := by
    simpa only [f.injective.mem_set_image] using hne
  obtain ⟨u,hu⟩ := polygon_product_key_change_mem_modification_zone y hh
  exact ⟨u,y,product_key_modification_zone_subset_collar_interior u hu,rfl⟩

theorem raw_product_carriers_cover_of_pairing {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : PolygonProductPhysicalTiling f) (P : ProductKeyPairing f) :
    ∀ x : EFour, ∃ i, x ∈ f i '' polygonProductBody := by
  intro x
  obtain ⟨i,hi⟩ := T.covers x
  by_cases hr : x ∈ f i '' polygonProductBody
  · exact ⟨i,hr⟩
  · have hd : ¬ (x ∈ f i '' polygonProductKeyBody ↔ x ∈ f i '' polygonProductBody) :=
      fun h => hr (h.mp hi)
    obtain ⟨u,hu⟩ := placed_key_change_mem_collar_interior (f i) x hd
    rcases P.raw_cover i u (image_mono interior_subset hu) with h | h
    · exact ⟨i,h⟩
    · exact ⟨(P.partner i u).1,h⟩

theorem physical_raw_product_carriers_cover {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : PolygonProductPhysicalTiling f) : ∀ x : EFour, ∃ i, x ∈ f i '' polygonProductBody := by
  obtain ⟨P⟩ := exists_productKeyPairing T
  exact raw_product_carriers_cover_of_pairing T P

end
end SpectreGeometry
