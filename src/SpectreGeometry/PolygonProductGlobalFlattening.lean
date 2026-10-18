module

public import SpectreGeometry.PolygonProductKeyPairing
public import SpectreGeometry.PolygonProductKeyPairedRawInteriors
public import SpectreGeometry.FiniteMaterialAvoidance

@[expose] public section


namespace SpectreGeometry
open Set
noncomputable section

/-- Removing every matched key preserves packing. Finite frontier avoidance
uses only the two candidate tiles and their finitely many selected partners. -/
theorem raw_product_interiors_disjoint_of_pairing {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : PolygonProductPhysicalTiling f) (P : ProductKeyPairing f) :
    Pairwise fun i j => Disjoint (interior (f i '' polygonProductBody))
      (interior (f j '' polygonProductBody)) := by
  classical
  intro i j hij
  apply Set.disjoint_left.mpr
  intro y hyi hyj
  let U := interior (f i '' polygonProductBody) ∩ interior (f j '' polygonProductBody)
  let idx : Bool × Option ProductKeySite → ι := fun z =>
    let k := if z.1 then j else i
    match z.2 with
    | none => k
    | some u => (P.partner k u).1
  obtain ⟨x,hx,havoid⟩ := FiniteMaterialAvoidance.exists_mem_open_avoid_frontiers
    (fun z => placedPolygonProductKeyBody (f (idx z)))
    (fun z => placedPolygonProductKeyBody_isClosed _) U
    (isOpen_interior.inter isOpen_interior) ⟨y,hyi,hyj⟩
  have hxi : x ∈ interior (f i '' polygonProductBody) := hx.1
  have hxj : x ∈ interior (f j '' polygonProductBody) := hx.2
  have avoid_i : x ∉ frontier (placedPolygonProductKeyBody (f i)) := by
    simpa [idx] using havoid (false,none)
  have avoid_j : x ∉ frontier (placedPolygonProductKeyBody (f j)) := by
    simpa [idx] using havoid (true,none)
  have avoid_pi (u : ProductKeySite) :
      x ∉ frontier (placedPolygonProductKeyBody (f (P.partner i u).1)) := by
    simpa [idx] using havoid (false,some u)
  have avoid_pj (u : ProductKeySite) :
      x ∉ frontier (placedPolygonProductKeyBody (f (P.partner j u).1)) := by
    simpa [idx] using havoid (true,some u)
  have asInterior (k : ι) (ha : x ∉ frontier (placedPolygonProductKeyBody (f k)))
      (hm : x ∈ placedPolygonProductKeyBody (f k)) :
      x ∈ interior (placedPolygonProductKeyBody (f k)) := by
    by_contra hn
    exact ha ⟨subset_closure hm,hn⟩
  have owner_eq (k l : ι) (hk : x ∈ interior (placedPolygonProductKeyBody (f k)))
      (hl : x ∈ interior (placedPolygonProductKeyBody (f l))) : k = l := by
    by_contra hne
    exact Set.disjoint_left.mp (T.interiors_disjoint hne) hk hl
  have collarInterior (k : ι) (u : ProductKeySite)
      (hu : x ∈ f k '' interior (productKeyCollar u)) :
      x ∈ interior (f k '' productKeyCollar u) := by
    have he : f k '' interior (productKeyCollar u) = interior (f k '' productKeyCollar u) :=
      (f k).toHomeomorph.image_interior (productKeyCollar u)
    rw [← he]
    exact hu
  by_cases hai : x ∈ placedPolygonProductKeyBody (f i)
  · by_cases haj : x ∈ placedPolygonProductKeyBody (f j)
    · exact hij (owner_eq i j (asInterior i avoid_i hai) (asInterior j avoid_j haj))
    · obtain ⟨v,hv⟩ := placed_key_change_mem_collar_interior (f j) x
        (fun h => haj (h.mpr (interior_subset hxj)))
      have hpj := (P.actual_cover j v (image_mono interior_subset hv)).resolve_left haj
      have he := owner_eq (P.partner j v).1 i (asInterior _ (avoid_pj v) hpj) (asInterior i avoid_i hai)
      apply paired_raw_interiors_disjoint_on_collar v (P.partner j v).2
        (f j) (f (P.partner j v).1) (P.oppositeSigns j v) (P.samePose j v) x (collarInterior j v hv)
      exact ⟨hxj,by simpa only [he] using hxi⟩
  · obtain ⟨u,hu⟩ := placed_key_change_mem_collar_interior (f i) x
      (fun h => hai (h.mpr (interior_subset hxi)))
    have hpi := (P.actual_cover i u (image_mono interior_subset hu)).resolve_left hai
    have hip := asInterior _ (avoid_pi u) hpi
    by_cases haj : x ∈ placedPolygonProductKeyBody (f j)
    · have he := owner_eq (P.partner i u).1 j hip (asInterior j avoid_j haj)
      apply paired_raw_interiors_disjoint_on_collar u (P.partner i u).2
        (f i) (f (P.partner i u).1) (P.oppositeSigns i u) (P.samePose i u) x (collarInterior i u hu)
      exact ⟨hxi,by simpa only [he] using hxj⟩
    · obtain ⟨v,hv⟩ := placed_key_change_mem_collar_interior (f j) x
        (fun h => haj (h.mpr (interior_subset hxj)))
      have hpj := (P.actual_cover j v (image_mono interior_subset hv)).resolve_left haj
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
      have hop := coincident_signed_poses_opposite_signs u v (f i) (f j)
        (T.interiors_disjoint hij) hp
      have hsu := P.oppositeSigns i u
      have hsv := P.oppositeSigns j v
      rw [hs] at hsu
      have hzero : productKeySign u = 0 := by linarith
      cases huSign : u.2.2 <;> simp [productKeySign,huSign] at hzero

/-- Every arbitrary physical tiling by the literal keyed body yields a
covering and interior-disjoint tiling by its unchanged raw P×P carriers. -/
theorem physical_raw_product_tiling {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : PolygonProductPhysicalTiling f) :
    (∀ x : EFour, ∃ i, x ∈ f i '' polygonProductBody) ∧
    Pairwise (fun i j => Disjoint (interior (f i '' polygonProductBody))
      (interior (f j '' polygonProductBody))) := by
  obtain ⟨P⟩ := exists_productKeyPairing T
  exact ⟨raw_product_carriers_cover_of_pairing T P,raw_product_interiors_disjoint_of_pairing T P⟩

end
end SpectreGeometry
