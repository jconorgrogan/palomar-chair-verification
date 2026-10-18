module

public import SpectreGeometry.SegmentEndpointRegistration

@[expose] public section


/-! Every literal unit edge of every tile in an actual homochiral tiling
has a whole-unit-edge neighbor. This is derived from arbitrary direct
Euclidean placements, coverage, and disjoint interiors, not assumed. -/
namespace SpectreGeometry
noncomputable section
open Set

theorem homochiral_contact_unit_edges_whole {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody)
    (root i : ι) (hij : i ≠ root) (e j : Fin 14)
    (t u : ℝ) (ht : 0 < t) (ht' : t < 1) (hu : 0 < u) (hu' : u < 1)
    (x : EPlane)
    (hxe : x = f root (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) t)))
    (hxj : x = f i (euclideanCoordinates (interpolate (realVertex j) (realVertex (next j)) u))) :
    (f root (euclideanVertex e) = f i (euclideanVertex j) ∧
      f root (euclideanVertex (next e)) = f i (euclideanVertex (next j))) ∨
    (f root (euclideanVertex e) = f i (euclideanVertex (next j)) ∧
      f root (euclideanVertex (next e)) = f i (euclideanVertex j)) := by
  have hvec := strict_edge_contact_vectors (f root) (f i) (hdisjoint (Ne.symm hij))
    e j t u ht ht' hu hu' x hxe hxj
  have hxp := hxe.trans (placed_edge_interpolate (f root) e t)
  have hxq := hxj.trans (placed_edge_interpolate (f i) j u)
  apply segment_endpoint_registration _ _ _ _ x t u ht ht' hu hu' hxp hxq hvec
  · intro s hs hs'
    have hn := homochiral_no_vertex_in_unit_edge f hdirect hdisjoint hcover root i hij e j s hs hs'
    rwa [placed_edge_interpolate] at hn
  · intro s hs hs'
    have hn := homochiral_no_vertex_in_unit_edge f hdirect hdisjoint hcover root i hij e (next j) s hs hs'
    rwa [placed_edge_interpolate] at hn
  · intro s hs hs'
    have hn := homochiral_no_vertex_in_unit_edge f hdirect hdisjoint hcover i root (Ne.symm hij) j e s hs hs'
    rwa [placed_edge_interpolate] at hn

theorem homochiral_whole_unit_edge_registration {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody)
    (root : ι) (e : Fin 14) :
    ∃ i, i ≠ root ∧ ∃ j : Fin 14,
      (f root (euclideanVertex e) = f i (euclideanVertex j) ∧
        f root (euclideanVertex (next e)) = f i (euclideanVertex (next j))) ∨
      (f root (euclideanVertex e) = f i (euclideanVertex (next j)) ∧
        f root (euclideanVertex (next e)) = f i (euclideanVertex j)) := by
  let x := f root (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) (1/2)))
  have hx : x ∈ frontier (f root '' euclideanBody) := by
    apply (placed_frontier_mem_iff (f root) x).2
    rw [show x = f root (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) (1/2))) from rfl,
      sourcePoint_image]
    exact outer_open_edge_mem_frontier e (1/2) (by norm_num) (by norm_num)
  have hlocal := CompactPacking.polygon_packing_locallyFinite f hdisjoint
  have hclosed : ∀ a, IsClosed (f a '' euclideanBody) :=
    fun a => (euclideanBody_compact.image (f a).continuous).isClosed
  have hregular : ∀ a, f a '' euclideanBody ⊆ closure (interior (f a '' euclideanBody)) := by
    intro a
    rw [placed_body_closure_interior]
  obtain ⟨i,hi,hxi⟩ := CompactTilingIncidence.frontier_has_boundary_neighbor
    (fun a => f a '' euclideanBody) hlocal hclosed hregular hdisjoint hcover root hx
  have hv : ∀ j : Fin 14, x ≠ f i (euclideanVertex j) := by
    intro j
    exact homochiral_no_vertex_in_unit_edge f hdirect hdisjoint hcover root i hi e j
      (1/2) (by norm_num) (by norm_num)
  obtain ⟨j,u,hu,hu',hxu⟩ := nonvertex_frontier_open_edge (f i) hxi hv
  refine ⟨i,hi,j,?_⟩
  exact homochiral_contact_unit_edges_whole f hdirect hdisjoint hcover root i hi e j
    (1/2) u (by norm_num) (by norm_num) hu hu' x rfl hxu

end
end SpectreGeometry
