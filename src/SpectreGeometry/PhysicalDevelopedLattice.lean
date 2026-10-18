module

public import SpectreGeometry.DevelopedCenterLattice
public import SpectreGeometry.QuadraticFrameUniqueness
public import SpectreGeometry.PhysicalLatticeEdge

@[expose] public section


/-! Global center-lattice registration of the developed H/T boundary polygons.
The vertex development and all frame/lattice constraints follow from genuine
physical coverage and packing. Real-plane homeomorphism remains separate. -/
namespace SpectreGeometry
noncomputable section

section Tiling
variable {ι : Type*} (f : ι → EPlane ≃ᵢ EPlane)
  (hdirect : ∀ i, DirectPlacement (f i))
  (hdisjoint : Pairwise fun i j =>
    Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
  (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody)

def physicalDevelopedOrigin (root i : ι) : ℚ × ℚ :=
  quadraticDevelopment ⟨sourcePoint (f root) (f i 0),
    homochiral_origin_mem_quadraticPlane f hdirect hdisjoint hcover root i⟩

def physicalDevelopedAnchor (root : ι) (r : ι → Fin 12) (i : ι) : ℚ × ℚ :=
  physicalDevelopedOrigin f hdirect hdisjoint hcover root i+rationalKitePoint (deformedOffset (r i))

theorem physical_developed_contact_lattice (root : ι) (r : ι → Fin 12)
    (hframe : ∀ i q, coordinateAction (f i) q = coordinateAction (f root) (rotate (r i) q))
    {i j : ι}
    (hc : CompactTilingIncidence.ContactAway
      (fun k => f k '' euclideanBody) (CompactTilingIncidence.placedVertices f) i j) :
    physicalDevelopedAnchor f hdirect hdisjoint hcover root r j-
      physicalDevelopedAnchor f hdirect hdisjoint hcover root r i ∈ rationalKiteCenterLattice := by
  by_cases hij : i = j
  · subst j
    rw [sub_self]
    exact rationalKiteCenterLattice.zero_mem
  obtain ⟨x,hxi,hxj,hnot⟩ := hc
  have hvertex : ∀ k : ι, ∀ e : Fin 14, x ≠ f k (euclideanVertex e) := by
    intro k e he
    exact hnot ⟨(k,e),he.symm⟩
  obtain ⟨⟨e,t,ht,ht',hxe⟩,⟨v,u,hu,hu',hxv⟩⟩ :=
    packing_nonvertex_contact_open_edges f hdisjoint hij hxi hxj hvertex
  obtain ⟨k,hk⟩ := homochiral_tiling_cyclic_frames f hdirect hdisjoint hcover i j
  have hrel := relative_frames_compose (f root) (f i) (f j) (r i) (r j) k
    (hframe i) (hframe j) hk
  have hl := physical_contact_deformed_anchor_lattice f hdirect hdisjoint hcover i j
    (Ne.symm hij) e v t u ht ht' hu hu' x hxe hxv k hk (r i)
  rw [←hrel] at hl
  obtain ⟨hs,_⟩ := homochiral_contact_unit_edges_reversed f hdirect hdisjoint hcover i j
    (Ne.symm hij) e v t u ht ht' hu hu' x hxe hxv
  have hd := shared_physical_vertex_development (f root) (f i) (f j) (r i) (r j)
    (hframe i) (hframe j)
    (homochiral_origin_mem_quadraticPlane f hdirect hdisjoint hcover root i)
    (homochiral_origin_mem_quadraticPlane f hdirect hdisjoint hcover root j) e (next v) hs
  change physicalDevelopedOrigin f hdirect hdisjoint hcover root i+
      rationalKitePoint (deformedVertex (r i) e) =
    physicalDevelopedOrigin f hdirect hdisjoint hcover root j+
      rationalKitePoint (deformedVertex (r j) (next v)) at hd
  change (physicalDevelopedOrigin f hdirect hdisjoint hcover root j+rationalKitePoint (deformedOffset (r j)))-
    (physicalDevelopedOrigin f hdirect hdisjoint hcover root i+rationalKitePoint (deformedOffset (r i))) ∈ _
  rw [developed_anchor_difference _ _ (r i) (r j) e v hd]
  exact rationalKitePoint_lattice _ hl

/-- Every developed raw-tile anchor lies in a single translated kite center lattice. -/
theorem homochiral_developed_anchors_lattice (root : ι) (r : ι → Fin 12)
    (hframe : ∀ i q, coordinateAction (f i) q = coordinateAction (f root) (rotate (r i) q))
    (i : ι) :
    physicalDevelopedAnchor f hdirect hdisjoint hcover root r i-
      physicalDevelopedAnchor f hdirect hdisjoint hcover root r root ∈ rationalKiteCenterLattice := by
  have hp := CompactTilingIncidence.polygon_tiling_nonvertex_contact_connected f hdisjoint hcover root i
  induction hp with
  | refl =>
      rw [sub_self]
      exact rationalKiteCenterLattice.zero_mem
  | @tail a b hab hc ih =>
      have hs := physical_developed_contact_lattice f hdirect hdisjoint hcover root r hframe hc
      have hh := rationalKiteCenterLattice.add_mem hs ih
      simpa only [sub_add_sub_cancel] using hh

/-- No finite-pose or lattice-translation premise is required for the global
boundary development's single-lattice conclusion. -/
theorem homochiral_exists_developed_lattice (root : ι) :
    ∃ r : ι → Fin 12,
      (∀ i q, coordinateAction (f i) q = coordinateAction (f root) (rotate (r i) q)) ∧
      ∀ i, physicalDevelopedAnchor f hdirect hdisjoint hcover root r i-
        physicalDevelopedAnchor f hdirect hdisjoint hcover root r root ∈ rationalKiteCenterLattice := by
  choose r hr using fun i => homochiral_tiling_cyclic_frames f hdirect hdisjoint hcover root i
  exact ⟨r,hr,homochiral_developed_anchors_lattice f hdirect hdisjoint hcover root r hr⟩

end Tiling
end
end SpectreGeometry
