module

public import SpectreGeometry.UnitEdgeDirections
public import SpectreGeometry.PlacedEdgeNoncrossing

@[expose] public section


/-! Supporting-line alignment strengthened to equality, up to reversal, of
the actual unit edge vectors. This still does not identify their endpoints. -/
namespace SpectreGeometry
noncomputable section

theorem placedEdgeVector_kernel (f : EPlane ≃ᵢ EPlane) (i : Fin 14) :
    edgeLinearForm f i (placedEdgeVector f i) = 0 := by
  change RealPoint.det (realEdge i) (displacementPullback f (placedEdgeVector f i)) = 0
  rw [displacementPullback_edge]
  simp only [RealPoint.det]
  ring

theorem strict_edge_contact_vectors (f g : EPlane ≃ᵢ EPlane)
    (hdisjoint : Disjoint (interior (f '' euclideanBody)) (interior (g '' euclideanBody)))
    (i j : Fin 14) (t u : ℝ) (ht : 0 < t) (ht' : t < 1) (hu : 0 < u) (hu' : u < 1)
    (x : EPlane)
    (hfx : x = f (euclideanCoordinates (interpolate (realVertex i) (realVertex (next i)) t)))
    (hgx : x = g (euclideanCoordinates (interpolate (realVertex j) (realVertex (next j)) u))) :
    placedEdgeVector f i = placedEdgeVector g j ∨ placedEdgeVector f i = -placedEdgeVector g j := by
  have hk := strict_edge_contact_kernels f g hdisjoint i j t u ht ht' hu hu' x hfx hgx
  exact unit_edge_kernel_vector g j _ (placedEdgeVector_unit f i)
    ((hk _).1 (placedEdgeVector_kernel f i))

theorem packing_nonvertex_contact_unit_vectors {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    {i j : ι} (hij : i ≠ j) {x : EPlane}
    (hi : x ∈ f i '' euclideanBody) (hj : x ∈ f j '' euclideanBody)
    (hvertex : ∀ k : ι, ∀ e : Fin 14, x ≠ f k (euclideanVertex e)) :
    ∃ a b : Fin 14, placedEdgeVector (f i) a = placedEdgeVector (f j) b ∨
      placedEdgeVector (f i) a = -placedEdgeVector (f j) b := by
  obtain ⟨⟨a,t,ht,ht',hxt⟩,⟨b,u,hu,hu',hxu⟩⟩ :=
    packing_nonvertex_contact_open_edges f hdisjoint hij hi hj hvertex
  exact ⟨a,b,strict_edge_contact_vectors (f i) (f j) (hdisjoint hij)
    a b t u ht ht' hu hu' x hxt hxu⟩

end
end SpectreGeometry
