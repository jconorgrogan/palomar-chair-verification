module

public import SpectreGeometry.PhysicalBoundaryRays

@[expose] public section


/-! Whole unit-edge registration's geometric obstruction: no placed polygon
vertex can lie strictly inside another tile's unit edge in a genuine
homochiral physical tiling. -/
namespace SpectreGeometry
noncomputable section
open Set

theorem homochiral_no_vertex_in_unit_edge {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody)
    (root i : ι) (hij : i ≠ root) (e j : Fin 14)
    (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    f root (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) t)) ≠
      f i (euclideanVertex j) := by
  intro he
  let x := f root (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) t))
  have hx : x = f root (euclideanVertex e) + t • placedEdgeVector (f root) e :=
    placed_edge_interpolate (f root) e t
  obtain ⟨hl,hr⟩ := physical_vertex_edge_boundary_rays f hdirect hdisjoint hcover
    root i hij e j t ht ht' x rfl he
  obtain ⟨a,q,ha,hqa,hva⟩ := hl
  have hleft : f root (euclideanVertex e) =
      f a (euclideanCoordinates (interpolate (realVertex q) (realVertex (next q)) t)) := by
    rw [placed_edge_interpolate,hva,←hqa,smul_neg,hx]
    abel
  have hsmallleft := physical_vertex_in_edge_corner_constraint f hdirect hdisjoint hcover
    a root (Ne.symm ha) q e t ht ht' (f root (euclideanVertex e)) hleft rfl
  obtain ⟨a',q',ha',hqa',hva'⟩ := hr
  have hstart : f a' (euclideanVertex (previous q')) = x + placedEdgeVector (f root) e := by
    have hh := hva'
    rw [placedEdgeVector,next_previous,←hqa'] at hh
    calc
      f a' (euclideanVertex (previous q')) = x -
          (x - f a' (euclideanVertex (previous q'))) := by abel
      _ = x + placedEdgeVector (f root) e := by rw [hh,sub_neg_eq_add]
  have hright : f root (euclideanVertex (next e)) =
      f a' (euclideanCoordinates (interpolate (realVertex (previous q')) (realVertex (next (previous q'))) t)) := by
    rw [placed_edge_interpolate,hstart,hva',smul_neg,hx]
    unfold placedEdgeVector
    abel
  have hsmallright := physical_vertex_in_edge_corner_constraint f hdirect hdisjoint hcover
    a' root (Ne.symm ha') (previous q') (next e) t ht ht'
    (f root (euclideanVertex (next e))) hright rfl
  exact edge_endpoint_not_both_small e ⟨hsmallleft,hsmallright⟩

end
end SpectreGeometry
