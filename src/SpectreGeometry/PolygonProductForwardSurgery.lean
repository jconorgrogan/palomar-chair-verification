module

public import SpectreGeometry.PolygonProductKeyPairing
public import SpectreGeometry.PolygonProductKeyRawPoseOpposition
public import SpectreGeometry.FiniteMaterialAvoidance

@[expose] public section


namespace SpectreGeometry
open Set
noncomputable section

/-- A raw product tiling, kept separate from physical keyed-body tilings. -/
structure RawProductTiling {ι : Type*} (f : ι → EFour ≃ᵢ EFour) where
  covers : ∀ x, ∃ i, x ∈ f i '' polygonProductBody
  interiors_disjoint : Pairwise fun i j => Disjoint (interior (f i '' polygonProductBody))
    (interior (f j '' polygonProductBody))

/-- Adding matched complementary keys preserves packing. The pairing remains
an explicit premise until instantiated by the proper plane product construction. -/
theorem keyed_product_interiors_disjoint_of_pairing {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : RawProductTiling f) (P : ProductKeyPairing f) :
    Pairwise fun i j => Disjoint (interior (f i '' polygonProductKeyBody))
      (interior (f j '' polygonProductKeyBody)) := by
  classical
  intro i j hij
  apply Set.disjoint_left.mpr
  intro y hyi hyj
  let U := interior (f i '' polygonProductKeyBody) ∩ interior (f j '' polygonProductKeyBody)
  let idx : Bool × Option ProductKeySite → ι := fun z =>
    let k := if z.1 then j else i
    match z.2 with
    | none => k
    | some u => (P.partner k u).1
  obtain ⟨x,hx,havoid⟩ := FiniteMaterialAvoidance.exists_mem_open_avoid_frontiers
    (fun z => (f (idx z) '' polygonProductBody))
    (fun z => ((f (idx z)).toHomeomorph.isClosedMap _ polygon_product_body_isCompact.isClosed)) U
    (isOpen_interior.inter isOpen_interior) ⟨y,hyi,hyj⟩
  have hxi : x ∈ interior (f i '' polygonProductKeyBody) := hx.1
  have hxj : x ∈ interior (f j '' polygonProductKeyBody) := hx.2
  have avoid_i : x ∉ frontier ((f i '' polygonProductBody)) := by
    simpa [idx] using havoid (false,none)
  have avoid_j : x ∉ frontier ((f j '' polygonProductBody)) := by
    simpa [idx] using havoid (true,none)
  have avoid_pi (u : ProductKeySite) :
      x ∉ frontier ((f (P.partner i u).1 '' polygonProductBody)) := by
    simpa [idx] using havoid (false,some u)
  have avoid_pj (u : ProductKeySite) :
      x ∉ frontier ((f (P.partner j u).1 '' polygonProductBody)) := by
    simpa [idx] using havoid (true,some u)
  have asInterior (k : ι) (ha : x ∉ frontier ((f k '' polygonProductBody)))
      (hm : x ∈ (f k '' polygonProductBody)) :
      x ∈ interior ((f k '' polygonProductBody)) := by
    by_contra hn
    exact ha ⟨subset_closure hm,hn⟩
  have owner_eq (k l : ι) (hk : x ∈ interior ((f k '' polygonProductBody)))
      (hl : x ∈ interior ((f l '' polygonProductBody))) : k = l := by
    by_contra hne
    exact Set.disjoint_left.mp (T.interiors_disjoint hne) hk hl
  have collarInterior (k : ι) (u : ProductKeySite)
      (hu : x ∈ f k '' interior (productKeyCollar u)) :
      x ∈ interior (f k '' productKeyCollar u) := by
    have he : f k '' interior (productKeyCollar u) = interior (f k '' productKeyCollar u) :=
      (f k).toHomeomorph.image_interior (productKeyCollar u)
    rw [← he]
    exact hu
  by_cases hai : x ∈ (f i '' polygonProductBody)
  · by_cases haj : x ∈ (f j '' polygonProductBody)
    · exact hij (owner_eq i j (asInterior i avoid_i hai) (asInterior j avoid_j haj))
    · obtain ⟨v,hv⟩ := placed_key_change_mem_collar_interior (f j) x
        (fun h => haj (h.mp (interior_subset hxj)))
      have hpj := (P.raw_cover j v (image_mono interior_subset hv)).resolve_left haj
      have he := owner_eq (P.partner j v).1 i (asInterior _ (avoid_pj v) hpj) (asInterior i avoid_i hai)
      apply paired_actual_interiors_disjoint_on_collar v (P.partner j v).2
        (f j) (f (P.partner j v).1) (P.sameLabel j v) (P.oppositeSigns j v) (P.samePose j v) x (collarInterior j v hv)
      exact ⟨hxj,by simpa only [he] using hxi⟩
  · obtain ⟨u,hu⟩ := placed_key_change_mem_collar_interior (f i) x
      (fun h => hai (h.mp (interior_subset hxi)))
    have hpi := (P.raw_cover i u (image_mono interior_subset hu)).resolve_left hai
    have hip := asInterior _ (avoid_pi u) hpi
    by_cases haj : x ∈ (f j '' polygonProductBody)
    · have he := owner_eq (P.partner i u).1 j hip (asInterior j avoid_j haj)
      apply paired_actual_interiors_disjoint_on_collar u (P.partner i u).2
        (f i) (f (P.partner i u).1) (P.sameLabel i u) (P.oppositeSigns i u) (P.samePose i u) x (collarInterior i u hu)
      exact ⟨hxi,by simpa only [he] using hxj⟩
    · obtain ⟨v,hv⟩ := placed_key_change_mem_collar_interior (f j) x
        (fun h => haj (h.mp (interior_subset hxj)))
      have hpj := (P.raw_cover j v (image_mono interior_subset hv)).resolve_left haj
      have he := owner_eq (P.partner i u).1 (P.partner j v).1 hip (asInterior _ (avoid_pj v) hpj)
      have hci : x ∈ f (P.partner i u).1 '' productKeyCollar (P.partner i u).2 := by
        rw [←P.collars i u]
        exact image_mono interior_subset hu
      have hcj : x ∈ f (P.partner i u).1 '' productKeyCollar (P.partner j v).2 := by
        rw [he,←P.collars j v]
        exact image_mono interior_subset hv
      have hs : (P.partner i u).2 = (P.partner j v).2 := by
        by_contra hne
        obtain ⟨a,ha,hea⟩ := hci
        obtain ⟨b,hb,heb⟩ := hcj
        have hab : a = b := (f (P.partner i u).1).injective (hea.trans heb.symm)
        subst b
        exact Set.disjoint_left.mp (product_key_collars_disjoint _ _ hne) ha hb
      have hp : (productKeySignedAffineIsometry u).toIsometryEquiv.trans (f i) =
          (productKeySignedAffineIsometry v).toIsometryEquiv.trans (f j) := by
        calc
          _ = (productKeySignedAffineIsometry (P.partner i u).2).toIsometryEquiv.trans
              (f (P.partner i u).1) := P.samePose i u
          _ = (productKeySignedAffineIsometry (P.partner j v).2).toIsometryEquiv.trans
              (f (P.partner j v).1) := by rw [hs,he]
          _ = _ := (P.samePose j v).symm
      have hop := coincident_signed_poses_raw_opposite_signs u v (f i) (f j)
        (T.interiors_disjoint hij) hp
      have hsu := P.oppositeSigns i u
      have hsv := P.oppositeSigns j v
      rw [hs] at hsu
      have hzero : productKeySign u = 0 := by linarith
      cases huSign : u.2.2 <;> simp [productKeySign,huSign] at hzero

/-- A matched surgery also preserves covering. -/
theorem keyed_product_cover_of_pairing {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : RawProductTiling f) (P : ProductKeyPairing f) :
    ∀ x : EFour, ∃ i, x ∈ f i '' polygonProductKeyBody := by
  intro x
  obtain ⟨i,hi⟩ := T.covers x
  by_cases hk : x ∈ f i '' polygonProductKeyBody
  · exact ⟨i,hk⟩
  · obtain ⟨u,hu⟩ := placed_key_change_mem_collar_interior (f i) x
      (fun h => hk (h.mpr hi))
    rcases P.actual_cover i u (image_mono interior_subset hu) with h | h
    · exact ⟨i,h⟩
    · exact ⟨(P.partner i u).1,h⟩

theorem physical_product_tiling_of_raw_and_pairing {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : RawProductTiling f) (P : ProductKeyPairing f) : PolygonProductPhysicalTiling f :=
  ⟨keyed_product_interiors_disjoint_of_pairing T P,keyed_product_cover_of_pairing T P⟩

end
end SpectreGeometry
