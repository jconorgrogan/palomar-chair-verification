module

public import SpectreGeometry.PolygonProductKeyFrontier
public import SpectreGeometry.PolygonProductKeyContactExclusion
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.LocallyFinite

@[expose] public section


/-!
# Local finiteness and finite incident germs of the literal product-key body

The placements and index type are arbitrary. Compactness and nonempty interior
of the actual bounded body, together with pairwise disjoint placed interiors,
imply finite compact incidence, local finiteness, and finite neighbor sets.
The retained ball is obtained from the proved nonempty interior; no radius,
diameter, local-finiteness, or registration hypothesis is supplied by a caller.

The final tiling interface has exactly two fields: disjoint actual interiors
and coverage. Finite incident-only covering neighborhoods are consequences.
No native-chair compactness, packing, or tiling theorem is used.
-/

namespace SpectreGeometry
noncomputable section
open Set PhysicalRegistration
open scoped Topology

/-- An interior ball of an arbitrary body survives every isometric placement. -/
theorem eFour_packing_image_interior_ball (S : Set EFour) (p : EFour) (r : ℝ)
    (hball : Metric.ball p r ⊆ interior S) (f : EFour ≃ᵢ EFour) :
    Metric.ball (f p) r ⊆ interior (f '' S) := by
  rw [← f.image_ball]
  exact (Set.image_mono hball).trans
    (f.toHomeomorph.isOpenMap.image_interior_subset S)

/-- Interior-disjoint copies with a retained positive ball have uniformly
separated image centers, without an injectivity assumption on the placements. -/
theorem eFour_packing_centers_separated {ι : Type*}
    (S : Set EFour) (p : EFour) (r : ℝ) (hr : 0 < r)
    (hball : Metric.ball p r ⊆ interior S) (f : ι → EFour ≃ᵢ EFour)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' S)) (interior (f j '' S))) :
    Pairwise fun i j => r ≤ dist (f i p) (f j p) := by
  intro i j hij
  by_contra! hdist
  have hi : f i p ∈ interior (f i '' S) :=
    eFour_packing_image_interior_ball S p r hball (f i)
      (Metric.mem_ball_self hr)
  have hj : f i p ∈ interior (f j '' S) :=
    eFour_packing_image_interior_ball S p r hball (f j) hdist
  exact Set.disjoint_left.mp (hdisjoint hij) hi hj

/-- Only finitely many uniformly separated image centers lie in a compact
set, even when the original index type is arbitrary. -/
theorem eFour_packing_finite_centers_mem_compact {ι : Type*}
    (S : Set EFour) (p : EFour) (r : ℝ) (hr : 0 < r)
    (hball : Metric.ball p r ⊆ interior S) (f : ι → EFour ≃ᵢ EFour)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' S)) (interior (f j '' S)))
    (K : Set EFour) (hK : IsCompact K) :
    {i | f i p ∈ K}.Finite := by
  let : TopologicalSpace ι := ⊥
  let : DiscreteTopology ι := discreteTopology_bot ι
  have hf := Metric.isClosedEmbedding_of_pairwise_le_dist hr
    (eFour_packing_centers_separated S p r hr hball f hdisjoint)
  exact (hf.isCompact_preimage hK).finite_of_discrete

/-- A compact body with nonempty interior has finite compact incidence in
every interior-disjoint isometric packing. Both radius bounds are derived
from compactness, and the retained ball is derived from the actual interior. -/
theorem eFour_packing_finite_inter_compact {ι : Type*}
    (S : Set EFour) (hS : IsCompact S) (hinterior : (interior S).Nonempty)
    (f : ι → EFour ≃ᵢ EFour)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' S)) (interior (f j '' S)))
    (K : Set EFour) (hK : IsCompact K) :
    {i | (f i '' S ∩ K).Nonempty}.Finite := by
  obtain ⟨p, hp⟩ := hinterior
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hp
  obtain ⟨R, hR⟩ := hS.isBounded.subset_closedBall p
  obtain ⟨Q, hQ⟩ := hK.isBounded.subset_closedBall (0 : EFour)
  have hfinite := eFour_packing_finite_centers_mem_compact S p r hr hball f hdisjoint
    (Metric.closedBall (0 : EFour) (R + Q)) (isCompact_closedBall _ _)
  apply hfinite.subset
  intro i hi
  obtain ⟨x, hxbody, hxK⟩ := hi
  obtain ⟨z, hz, rfl⟩ := hxbody
  change dist (f i p) 0 ≤ R + Q
  calc
    dist (f i p) 0 ≤ dist (f i p) (f i z) + dist (f i z) 0 :=
      dist_triangle _ _ _
    _ = dist p z + dist (f i z) 0 := by rw [(f i).dist_eq]
    _ ≤ R + Q := add_le_add
      (by simpa only [Metric.mem_closedBall, dist_comm] using hR hz) (hQ hxK)

/-- Local finiteness follows from compact incidence in four-dimensional
Euclidean space. It is not an additional packing assumption. -/
theorem eFour_packing_locallyFinite {ι : Type*}
    (S : Set EFour) (hS : IsCompact S) (hinterior : (interior S).Nonempty)
    (f : ι → EFour ≃ᵢ EFour)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' S)) (interior (f j '' S))) :
    LocallyFinite (fun i => f i '' S) := by
  intro x
  exact ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x (by norm_num),
    eFour_packing_finite_inter_compact S hS hinterior f hdisjoint _
      (isCompact_closedBall x 1)⟩

/-- The literal body has a retained positive ball, obtained from its proved
nonempty interior with no supplied geometric certificate. -/
theorem polygon_product_key_body_exists_interior_ball :
    ∃ p : EFour, ∃ r : ℝ, 0 < r ∧ Metric.ball p r ⊆ interior polygonProductKeyBody := by
  obtain ⟨p, hp⟩ := polygon_product_key_body_interior_nonempty
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hp
  exact ⟨p, r, hr, hball⟩

/-- Every actual placed body is compact. -/
theorem placedPolygonProductKeyBody_isCompact (f : EFour ≃ᵢ EFour) :
    IsCompact (placedPolygonProductKeyBody f) :=
  polygon_product_key_body_isCompact.image f.continuous

/-- Every actual placed body is closed. -/
theorem placedPolygonProductKeyBody_isClosed (f : EFour ≃ᵢ EFour) :
    IsClosed (placedPolygonProductKeyBody f) :=
  (placedPolygonProductKeyBody_isCompact f).isClosed

/-- A compact set meets only finitely many literal polygon-product keyed
bodies in any arbitrary-index interior-disjoint isometric packing. -/
theorem finite_placedPolygonProductKeyBody_inter_compact {ι : Type*}
    (f : ι → EFour ≃ᵢ EFour)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedPolygonProductKeyBody (f i)))
        (interior (placedPolygonProductKeyBody (f j))))
    (K : Set EFour) (hK : IsCompact K) :
    {i | (placedPolygonProductKeyBody (f i) ∩ K).Nonempty}.Finite :=
  eFour_packing_finite_inter_compact polygonProductKeyBody
    polygon_product_key_body_isCompact polygon_product_key_body_interior_nonempty
    f hdisjoint K hK

/-- Arbitrary pairwise interior-disjoint placements of the literal bounded
56-key body form a genuinely locally finite family. -/
theorem placedPolygonProductKeyBody_locallyFinite {ι : Type*}
    (f : ι → EFour ≃ᵢ EFour)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedPolygonProductKeyBody (f i)))
        (interior (placedPolygonProductKeyBody (f j)))) :
    LocallyFinite (fun i => placedPolygonProductKeyBody (f i)) :=
  eFour_packing_locallyFinite polygonProductKeyBody polygon_product_key_body_isCompact
    polygon_product_key_body_interior_nonempty f hdisjoint

/-- Every fixed actual tile has only finitely many touching neighbors,
including all lower-dimensional contacts and the tile itself. -/
theorem finite_placedPolygonProductKeyBody_neighbors {ι : Type*}
    (f : ι → EFour ≃ᵢ EFour)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedPolygonProductKeyBody (f i)))
        (interior (placedPolygonProductKeyBody (f j)))) (i : ι) :
    {j | (placedPolygonProductKeyBody (f j) ∩
      placedPolygonProductKeyBody (f i)).Nonempty}.Finite :=
  finite_placedPolygonProductKeyBody_inter_compact f hdisjoint _
    (placedPolygonProductKeyBody_isCompact (f i))

/-- A physical tiling by unrestricted isometries of the literal product-key
body. Disjoint interiors and coverage are its entire hypothesis. -/
structure PolygonProductPhysicalTiling {ι : Type*}
    (f : ι → EFour ≃ᵢ EFour) : Prop where
  interiors_disjoint : Pairwise fun i j =>
    Disjoint (interior (placedPolygonProductKeyBody (f i)))
      (interior (placedPolygonProductKeyBody (f j)))
  covers : ∀ x : EFour, ∃ i, x ∈ placedPolygonProductKeyBody (f i)

/-- The actual incident indices at a point; no finiteness is built in. -/
def polygonProductIncidentTiles {ι : Type*}
    (f : ι → EFour ≃ᵢ EFour) (x : EFour) : Set ι :=
  {i | x ∈ placedPolygonProductKeyBody (f i)}

/-- Actual incidence is finite already for packings, before adding coverage. -/
theorem finite_polygonProductIncidentTiles {ι : Type*}
    (f : ι → EFour ≃ᵢ EFour)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedPolygonProductKeyBody (f i)))
        (interior (placedPolygonProductKeyBody (f j))))
    (x : EFour) : (polygonProductIncidentTiles f x).Finite := by
  have hfinite := finite_placedPolygonProductKeyBody_inter_compact f hdisjoint
    {x} isCompact_singleton
  exact hfinite.subset (fun i hi => ⟨x, hi, mem_singleton x⟩)

/-- A locally finite closed family has an open neighborhood meeting only
the members incident at its center. The finite exclusion step is explicit. -/
theorem exists_open_packing_incident_neighborhood
    {X ι : Type*} [TopologicalSpace X] (S : ι → Set X)
    (hlocal : LocallyFinite S) (hclosed : ∀ i, IsClosed (S i)) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ i, x ∉ S i → Disjoint (S i) U := by
  obtain ⟨V, hV, hfinite⟩ := hlocal x
  obtain ⟨W, hWV, hW, hxW⟩ := mem_nhds_iff.mp hV
  let B : Set ι := {i | (S i ∩ V).Nonempty ∧ x ∉ S i}
  have hB : B.Finite := hfinite.subset (fun _ hi => hi.1)
  let U := W ∩ ⋂ i ∈ B, (S i)ᶜ
  refine ⟨U, hW.inter (hB.isOpen_biInter (fun i _ => (hclosed i).isOpen_compl)),
    ⟨hxW, mem_iInter₂.mpr (fun i hi => hi.2)⟩, ?_⟩
  intro i hxi
  apply Set.disjoint_left.mpr
  intro y hy hyU
  have hiB : i ∈ B := ⟨⟨y, hy, hWV hyU.1⟩, hxi⟩
  exact (mem_iInter₂.mp hyU.2 i hiB) hy

/-- All nonincident actual tiles miss one open neighborhood of the point.
This conclusion uses derived local finiteness and actual closedness only. -/
theorem placedPolygonProductKeyBody_open_incident_neighborhood {ι : Type*}
    (f : ι → EFour ≃ᵢ EFour)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedPolygonProductKeyBody (f i)))
        (interior (placedPolygonProductKeyBody (f j))))
    (x : EFour) :
    ∃ U : Set EFour, IsOpen U ∧ x ∈ U ∧
      ∀ i, i ∉ polygonProductIncidentTiles f x →
        Disjoint (placedPolygonProductKeyBody (f i)) U :=
  exists_open_packing_incident_neighborhood (fun i => placedPolygonProductKeyBody (f i))
    (placedPolygonProductKeyBody_locallyFinite f hdisjoint)
    (fun i => placedPolygonProductKeyBody_isClosed (f i)) x

/-- Every actual tiling has a finite incident family covering a genuine open
neighborhood, with inherited disjoint actual interiors. Neither finiteness
nor this neighborhood is a field of the tiling interface. -/
theorem PolygonProductPhysicalTiling.finite_incident_germ {ι : Type*}
    {f : ι → EFour ≃ᵢ EFour} (T : PolygonProductPhysicalTiling f) (x : EFour) :
    (polygonProductIncidentTiles f x).Finite ∧
    ∃ U : Set EFour, IsOpen U ∧ x ∈ U ∧
      (∀ i, i ∉ polygonProductIncidentTiles f x →
        Disjoint (placedPolygonProductKeyBody (f i)) U) ∧
      (∀ y ∈ U, ∃ i ∈ polygonProductIncidentTiles f x,
        y ∈ placedPolygonProductKeyBody (f i)) ∧
      Pairwise (fun (i j : polygonProductIncidentTiles f x) =>
        Disjoint (interior (placedPolygonProductKeyBody (f i.val)))
          (interior (placedPolygonProductKeyBody (f j.val)))) := by
  obtain ⟨U, hU, hxU, havoid⟩ :=
    placedPolygonProductKeyBody_open_incident_neighborhood f T.interiors_disjoint x
  refine ⟨finite_polygonProductIncidentTiles f T.interiors_disjoint x,
    U, hU, hxU, havoid, ?_, ?_⟩
  · intro y hy
    obtain ⟨i, hi⟩ := T.covers y
    refine ⟨i, ?_, hi⟩
    by_contra hxi
    exact Set.disjoint_left.mp (havoid i hxi) hi hy
  · intro i j hij
    exact T.interiors_disjoint (fun h => hij (Subtype.ext h))

end
end SpectreGeometry
