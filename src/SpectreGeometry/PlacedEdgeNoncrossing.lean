module

public import SpectreGeometry.PlacedEdgeForms
public import SpectreGeometry.HalfplaneNoncrossing
public import SpectreGeometry.PolygonTilingIncidence

@[expose] public section


/-! Actual edge-line alignment at nonvertex contacts of arbitrary placed
polygon copies. This uses the proved local half-plane geometry and derives
affine pullback forms from arbitrary isometries. Whole-unit-edge registration
and finite orientation classification are separate later conclusions. -/
namespace SpectreGeometry
noncomputable section
open Set

theorem strict_edge_contact_kernels (f g : EPlane ≃ᵢ EPlane)
    (hdisjoint : Disjoint (interior (f '' euclideanBody)) (interior (g '' euclideanBody)))
    (i j : Fin 14) (t u : ℝ) (ht : 0 < t) (ht' : t < 1) (hu : 0 < u) (hu' : u < 1)
    (x : EPlane)
    (hfx : x = f (euclideanCoordinates (interpolate (realVertex i) (realVertex (next i)) t)))
    (hgx : x = g (euclideanCoordinates (interpolate (realVertex j) (realVertex (next j)) u))) :
    ∀ v, edgeLinearForm f i v = 0 ↔ edgeLinearForm g j v = 0 := by
  obtain ⟨U,hU,hfU,hfI⟩ := placed_open_edge_local_interior f i t ht ht'
  obtain ⟨V,hV,hgV,hgI⟩ := placed_open_edge_local_interior g j u hu hu'
  have hxU : x ∈ U := hfx.symm ▸ hfU
  have hxV : x ∈ V := hgx.symm ▸ hgV
  have hfx0 : placedSide f i x = 0 := by rw [hfx]; exact placedSide_edge_zero f i t
  have hgx0 : placedSide g j x = 0 := by rw [hgx]; exact placedSide_edge_zero g j u
  apply local_positive_disjoint_same_kernel (edgeLinearForm f i) (edgeLinearForm g j)
    (edgeLinearForm_nonzero f i) (edgeLinearForm_nonzero g j) x (U ∩ V) (hU.inter hV) ⟨hxU,hxV⟩
  intro y hy hpos
  have hfy : 0 < placedSide f i y := by
    simpa only [edgeLinearForm_sub,hfx0,sub_zero] using hpos.1
  have hgy : 0 < placedSide g j y := by
    simpa only [edgeLinearForm_sub,hgx0,sub_zero] using hpos.2
  exact Set.disjoint_left.mp hdisjoint ((hfI y hy.1).2 hfy) ((hgI y hy.2).2 hgy)

/-- The entire supporting lines, not only their germs, coincide. -/
theorem strict_edge_contact_supporting_lines (f g : EPlane ≃ᵢ EPlane)
    (hdisjoint : Disjoint (interior (f '' euclideanBody)) (interior (g '' euclideanBody)))
    (i j : Fin 14) (t u : ℝ) (ht : 0 < t) (ht' : t < 1) (hu : 0 < u) (hu' : u < 1)
    (x : EPlane)
    (hfx : x = f (euclideanCoordinates (interpolate (realVertex i) (realVertex (next i)) t)))
    (hgx : x = g (euclideanCoordinates (interpolate (realVertex j) (realVertex (next j)) u))) :
    {y | placedSide f i y = 0} = {y | placedSide g j y = 0} := by
  have hker := strict_edge_contact_kernels f g hdisjoint i j t u ht ht' hu hu' x hfx hgx
  have hfx0 : placedSide f i x = 0 := by rw [hfx]; exact placedSide_edge_zero f i t
  have hgx0 : placedSide g j x = 0 := by rw [hgx]; exact placedSide_edge_zero g j u
  ext y
  have h := hker (y-x)
  simpa only [edgeLinearForm_sub,hfx0,hgx0,sub_zero,Set.mem_setOf_eq] using h

/-- No incidence or relative-pose hypothesis is assumed: ordinary packing,
a shared point, and avoidance of the actual placed vertices suffice. -/
theorem packing_nonvertex_contact_aligned {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    {i j : ι} (hij : i ≠ j) {x : EPlane}
    (hi : x ∈ f i '' euclideanBody) (hj : x ∈ f j '' euclideanBody)
    (hvertex : ∀ k : ι, ∀ e : Fin 14, x ≠ f k (euclideanVertex e)) :
    ∃ a b : Fin 14, {y | placedSide (f i) a y = 0} = {y | placedSide (f j) b y = 0} := by
  obtain ⟨⟨a,t,ht,ht',hxt⟩,⟨b,u,hu,hu',hxu⟩⟩ :=
    packing_nonvertex_contact_open_edges f hdisjoint hij hi hj hvertex
  exact ⟨a,b,strict_edge_contact_supporting_lines (f i) (f j) (hdisjoint hij)
    a b t u ht ht' hu hu' x hxt hxu⟩

end
end SpectreGeometry
