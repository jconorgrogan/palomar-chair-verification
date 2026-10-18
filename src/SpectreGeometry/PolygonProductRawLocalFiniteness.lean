module

public import SpectreGeometry.PolygonProductKeyPacking

@[expose] public section


namespace SpectreGeometry
open Set
open scoped Topology
noncomputable section

/-- Packing one body with nonempty interior also bounds compact incidence
for any other fixed compact body carried by the same placements. -/
theorem eFour_packing_target_finite_inter_compact {ι : Type*}
    (S : Set EFour) (hinterior : (interior S).Nonempty)
    (C : Set EFour) (hC : IsCompact C) (f : ι → EFour ≃ᵢ EFour)
    (hdisjoint : Pairwise fun i j => Disjoint (interior (f i '' S)) (interior (f j '' S)))
    (K : Set EFour) (hK : IsCompact K) :
    {i | (f i '' C ∩ K).Nonempty}.Finite := by
  obtain ⟨p,hp⟩ := hinterior
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hp
  obtain ⟨R,hR⟩ := hC.isBounded.subset_closedBall p
  obtain ⟨Q,hQ⟩ := hK.isBounded.subset_closedBall (0 : EFour)
  have hfinite := eFour_packing_finite_centers_mem_compact S p r hr hball f hdisjoint
    (Metric.closedBall (0 : EFour) (R+Q)) (isCompact_closedBall _ _)
  apply hfinite.subset
  intro i hi
  obtain ⟨x,hx,hxK⟩ := hi
  obtain ⟨z,hz,rfl⟩ := hx
  change dist (f i p) 0 ≤ R+Q
  calc
    _ ≤ dist (f i p) (f i z) + dist (f i z) 0 := dist_triangle _ _ _
    _ = dist p z + dist (f i z) 0 := by rw [(f i).dist_eq]
    _ ≤ R+Q := add_le_add
      (by simpa only [Metric.mem_closedBall,dist_comm] using hR hz) (hQ hxK)

theorem physical_raw_product_finite_inter_compact {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : PolygonProductPhysicalTiling f) (K : Set EFour) (hK : IsCompact K) :
    {i | (f i '' polygonProductBody ∩ K).Nonempty}.Finite :=
  eFour_packing_target_finite_inter_compact polygonProductKeyBody
    polygon_product_key_body_interior_nonempty polygonProductBody polygon_product_body_isCompact
    f T.interiors_disjoint K hK

theorem physical_raw_product_locallyFinite {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : PolygonProductPhysicalTiling f) : LocallyFinite (fun i => f i '' polygonProductBody) := by
  intro x
  exact ⟨Metric.closedBall x 1,Metric.closedBall_mem_nhds x (by norm_num),
    physical_raw_product_finite_inter_compact T _ (isCompact_closedBall x 1)⟩

end
end SpectreGeometry
