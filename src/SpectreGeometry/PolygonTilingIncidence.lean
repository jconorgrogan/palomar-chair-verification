module

public import SpectreGeometry.CompactTilingIncidence
public import SpectreGeometry.PolygonBoundary

@[expose] public section


/-! The exact polygon frontier and regular-closed property transported to
arbitrary isometric copies. Contact-edge extraction does not presume edge
alignment or restrict the allowed physical placements. -/
namespace SpectreGeometry
noncomputable section
open Set

def euclideanEdge (i : Fin 14) : Set (CompactPacking.Space 2) :=
  euclideanCoordinates '' polygonEdge i

theorem euclideanBody_closure_interior : closure (interior euclideanBody) = euclideanBody := by
  rw [euclideanBody,←euclideanCoordinates.image_interior,←euclideanCoordinates.image_closure,
    polygonBody_closure_interior]

theorem euclideanBody_frontier_eq_edges : frontier euclideanBody = ⋃ i : Fin 14, euclideanEdge i := by
  rw [euclideanBody,←euclideanCoordinates.image_frontier,polygonBody_frontier_eq_edges,Set.image_iUnion]
  rfl

theorem placed_body_closure_interior (f : CompactPacking.Space 2 ≃ᵢ CompactPacking.Space 2) :
    closure (interior (f '' euclideanBody)) = f '' euclideanBody := by
  change closure (interior (f.toHomeomorph '' euclideanBody)) = f.toHomeomorph '' euclideanBody
  rw [←f.toHomeomorph.image_interior,←f.toHomeomorph.image_closure,euclideanBody_closure_interior]

theorem placed_body_frontier_eq_edges (f : CompactPacking.Space 2 ≃ᵢ CompactPacking.Space 2) :
    frontier (f '' euclideanBody) = ⋃ i : Fin 14, f '' euclideanEdge i := by
  change frontier (f.toHomeomorph '' euclideanBody) = ⋃ i : Fin 14, f.toHomeomorph '' euclideanEdge i
  rw [←f.toHomeomorph.image_frontier,euclideanBody_frontier_eq_edges,Set.image_iUnion]

/-- A nonvertex point of the true frontier is strictly inside one of the
fourteen unit segments, including the retained collinear midpoint split. -/
theorem nonvertex_frontier_open_edge
    (f : CompactPacking.Space 2 ≃ᵢ CompactPacking.Space 2) {x : CompactPacking.Space 2}
    (hx : x ∈ frontier (f '' euclideanBody))
    (hvertex : ∀ i : Fin 14, x ≠ f (euclideanVertex i)) :
    ∃ i : Fin 14, ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      x = f (euclideanCoordinates (interpolate (realVertex i) (realVertex (next i)) t)) := by
  rw [placed_body_frontier_eq_edges] at hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  obtain ⟨p,hp,rfl⟩ := hi
  obtain ⟨q,hq,rfl⟩ := hp
  obtain ⟨t,ht0,ht1,rfl⟩ := hq
  have hn0 : t ≠ 0 := by
    intro ht
    apply hvertex i
    simp only [ht,interpolate_zero,euclideanVertex]
  have hn1 : t ≠ 1 := by
    intro ht
    apply hvertex (next i)
    simp only [ht,interpolate_one,euclideanVertex]
  exact ⟨i,t,lt_of_le_of_ne ht0 (Ne.symm hn0),lt_of_le_of_ne ht1 hn1,rfl⟩

/-- The same extraction applies simultaneously to both sides of every
nonvertex contact in an unrestricted-isometry packing. -/
theorem packing_nonvertex_contact_open_edges {ι : Type*}
    (f : ι → CompactPacking.Space 2 ≃ᵢ CompactPacking.Space 2)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    {i j : ι} (hij : i ≠ j) {x : CompactPacking.Space 2}
    (hi : x ∈ f i '' euclideanBody) (hj : x ∈ f j '' euclideanBody)
    (hvertex : ∀ k : ι, ∀ e : Fin 14, x ≠ f k (euclideanVertex e)) :
    (∃ e : Fin 14, ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      x = f i (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) t))) ∧
    (∃ e : Fin 14, ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      x = f j (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) t))) := by
  have hregular : ∀ k, f k '' euclideanBody ⊆ closure (interior (f k '' euclideanBody)) := by
    intro k
    rw [placed_body_closure_interior]
  have hh := CompactTilingIncidence.common_point_frontiers (fun k => f k '' euclideanBody)
    (fun k => (euclideanBody_compact.image (f k).continuous).isClosed)
    hregular hdisjoint hij hi hj
  exact ⟨nonvertex_frontier_open_edge (f i) hh.1 (hvertex i),
    nonvertex_frontier_open_edge (f j) hh.2 (hvertex j)⟩

end
end SpectreGeometry
