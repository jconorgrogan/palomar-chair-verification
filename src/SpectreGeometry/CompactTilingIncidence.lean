module

public import SpectreGeometry.CompactPacking

@[expose] public section


/-! Local incidence facts for actual locally finite closed-set tilings.
The covering and interior-disjointness hypotheses describe the supplied tiling;
no existence of a physical polygon tiling or registration is asserted here. -/
namespace SpectreGeometry.CompactTilingIncidence
noncomputable section
open Set
open scoped Topology

/-- Near a point, no new member of a locally finite closed family appears. -/
theorem local_star_radius {X ι : Type*} [PseudoMetricSpace X] (F : ι → Set X)
    (hlocal : LocallyFinite F) (hclosed : ∀ i, IsClosed (F i)) (x : X) :
    ∃ r : ℝ, 0 < r ∧ ∀ i y, y ∈ Metric.ball x r → y ∈ F i → x ∈ F i := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hlocal.iInter_compl_mem_nhds hclosed x)
  refine ⟨r,hr,?_⟩
  intro i y hy hiy
  by_contra hxi
  exact (Set.mem_iInter₂.mp (hball hy) i hxi) hiy

/-- Every boundary point of one closed tile belongs to a different tile. -/
theorem frontier_has_neighbor {X ι : Type*} [PseudoMetricSpace X] (F : ι → Set X)
    (hlocal : LocallyFinite F) (hclosed : ∀ i, IsClosed (F i))
    (hcover : ∀ x, ∃ i, x ∈ F i) (i : ι) {x : X} (hx : x ∈ frontier (F i)) :
    ∃ j, j ≠ i ∧ x ∈ F j := by
  obtain ⟨r,hr,hstar⟩ := local_star_radius F hlocal hclosed x
  by_contra hnone
  have hone : ∀ j, x ∈ F j → j = i := by
    intro j hj
    by_contra hji
    exact hnone ⟨j,hji,hj⟩
  have hball : Metric.ball x r ⊆ F i := by
    intro y hy
    obtain ⟨j,hj⟩ := hcover y
    have he := hone j (hstar j y hy hj)
    simpa only [he] using hj
  have hi : x ∈ interior (F i) := mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (Metric.ball_mem_nhds x hr) hball)
  exact hx.2 hi

/-- Disjoint interiors of regular-closed tiles exclude any foreign tile
from an interior point, including the foreign tile's boundary. -/
theorem tile_disjoint_other_interior {X ι : Type*} [TopologicalSpace X]
    (F : ι → Set X) (hregular : ∀ i, F i ⊆ closure (interior (F i)))
    (hdisjoint : Pairwise fun i j => Disjoint (interior (F i)) (interior (F j)))
    {i j : ι} (hij : i ≠ j) : Disjoint (F i) (interior (F j)) := by
  have hsub : interior (F i) ⊆ (interior (F j))ᶜ := by
    intro x hx hj
    exact Set.disjoint_left.mp (hdisjoint hij) hx hj
  have hc : closure (interior (F i)) ⊆ (interior (F j))ᶜ :=
    isOpen_interior.isClosed_compl.closure_subset_iff.mpr hsub
  exact Set.disjoint_left.mpr (fun x hi hj => hc (hregular i hi) hj)

/-- Thus common points of distinct regular-closed packing tiles are on both frontiers. -/
theorem common_point_frontiers {X ι : Type*} [TopologicalSpace X]
    (F : ι → Set X) (hclosed : ∀ i, IsClosed (F i))
    (hregular : ∀ i, F i ⊆ closure (interior (F i)))
    (hdisjoint : Pairwise fun i j => Disjoint (interior (F i)) (interior (F j)))
    {i j : ι} (hij : i ≠ j) {x : X} (hi : x ∈ F i) (hj : x ∈ F j) :
    x ∈ frontier (F i) ∧ x ∈ frontier (F j) := by
  constructor
  · exact ⟨subset_closure hi, fun h =>
      Set.disjoint_left.mp (tile_disjoint_other_interior F hregular hdisjoint hij.symm) hj h⟩
  · exact ⟨subset_closure hj, fun h =>
      Set.disjoint_left.mp (tile_disjoint_other_interior F hregular hdisjoint hij) hi h⟩

/-- All boundary points are shared boundary points in a regular-closed tiling. -/
theorem frontier_has_boundary_neighbor {X ι : Type*} [PseudoMetricSpace X]
    (F : ι → Set X) (hlocal : LocallyFinite F) (hclosed : ∀ i, IsClosed (F i))
    (hregular : ∀ i, F i ⊆ closure (interior (F i)))
    (hdisjoint : Pairwise fun i j => Disjoint (interior (F i)) (interior (F j)))
    (hcover : ∀ x, ∃ i, x ∈ F i) (i : ι) {x : X} (hx : x ∈ frontier (F i)) :
    ∃ j, j ≠ i ∧ x ∈ frontier (F j) := by
  obtain ⟨j,hji,hj⟩ := frontier_has_neighbor F hlocal hclosed hcover i hx
  have hi : x ∈ F i := (hclosed i).closure_subset hx.1
  exact ⟨j,hji,(common_point_frontiers F hclosed hregular hdisjoint hji.symm hi hj).2⟩

/-- The finite-star and fixed-radius conclusions apply to arbitrary isometric
packings of the exact compact carrier, without an edge-registration premise. -/
theorem polygon_packing_finite_star {ι : Type*}
    (f : ι → CompactPacking.Space 2 ≃ᵢ CompactPacking.Space 2)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (x : CompactPacking.Space 2) :
    {i | x ∈ f i '' euclideanBody}.Finite ∧
    ∃ r : ℝ, 0 < r ∧ ∀ i y, y ∈ Metric.ball x r → y ∈ f i '' euclideanBody →
      x ∈ f i '' euclideanBody := by
  have hl := CompactPacking.polygon_packing_locallyFinite f hdisjoint
  exact ⟨hl.point_finite x,local_star_radius _ hl
    (fun i => (euclideanBody_compact.image (f i).continuous).isClosed) x⟩

end
end SpectreGeometry.CompactTilingIncidence
