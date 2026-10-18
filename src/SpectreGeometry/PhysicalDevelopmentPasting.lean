module

public import SpectreGeometry.PhysicalBoundaryDevelopment

@[expose] public section


/-! Exact agreement and well-defined pasting of tilewise maps whose edge
formulas use one global vertex assignment. The edge formulas are explicit
hypotheses, to be discharged by the finite triangle-affine construction. -/
namespace SpectreGeometry
noncomputable section
open Set

theorem frontier_closed_edge (f : EPlane ≃ᵢ EPlane) {x : EPlane}
    (hx : x ∈ frontier (f '' euclideanBody)) :
    ∃ e : Fin 14, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      x = f (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) t)) := by
  rw [placed_body_frontier_eq_edges] at hx
  obtain ⟨e,he⟩ := mem_iUnion.mp hx
  obtain ⟨p,hp,rfl⟩ := he
  obtain ⟨q,hq,rfl⟩ := hp
  obtain ⟨t,ht,ht',rfl⟩ := hq
  exact ⟨e,t,ht,ht',rfl⟩

section Tiling
variable {ι : Type*} (f : ι → EPlane ≃ᵢ EPlane)
  (hdirect : ∀ i, DirectPlacement (f i))
  (hdisjoint : Pairwise fun i j =>
    Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
  (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody)

include hdirect hdisjoint hcover in
theorem physical_tilewise_maps_agree (V : EPlane → RealPoint) (F : ι → EPlane → RealPoint)
    (hboundary : ∀ i e t, 0 ≤ t → t ≤ 1 →
      F i (f i (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) t))) =
        interpolate (V (f i (euclideanVertex e))) (V (f i (euclideanVertex (next e)))) t)
    (i j : ι) (x : EPlane) (hi : x ∈ f i '' euclideanBody) (hj : x ∈ f j '' euclideanBody) :
    F i x = F j x := by
  by_cases hij : i = j
  · rw [hij]
  have hregular : ∀ k, f k '' euclideanBody ⊆ closure (interior (f k '' euclideanBody)) := by
    intro k
    rw [placed_body_closure_interior]
  have hfront := CompactTilingIncidence.common_point_frontiers (fun k => f k '' euclideanBody)
    (fun k => (euclideanBody_compact.image (f k).continuous).isClosed)
    hregular hdisjoint hij hi hj
  obtain ⟨e,t,ht,ht',hxe⟩ := frontier_closed_edge (f i) hfront.1
  obtain ⟨v,u,hu,hu',hxv⟩ := frontier_closed_edge (f j) hfront.2
  calc
    F i x = interpolate (V (f i (euclideanVertex e))) (V (f i (euclideanVertex (next e)))) t := by
      rw [hxe,hboundary i e t ht ht']
    _ = interpolate (V (f j (euclideanVertex v))) (V (f j (euclideanVertex (next v)))) u :=
      physical_shared_edge_values f hdirect hdisjoint hcover V i j hij e v t u ht ht' hu hu'
        (hxe.symm.trans hxv)
    _ = F j x := by rw [hxv,hboundary j v u hu hu']

def physicalPastedMap (F : ι → EPlane → RealPoint) (x : EPlane) : RealPoint :=
  F (Classical.choose (hcover x)) x

include hdirect hdisjoint in
theorem physicalPastedMap_on_tile (V : EPlane → RealPoint) (F : ι → EPlane → RealPoint)
    (hboundary : ∀ i e t, 0 ≤ t → t ≤ 1 →
      F i (f i (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) t))) =
        interpolate (V (f i (euclideanVertex e))) (V (f i (euclideanVertex (next e)))) t)
    (i : ι) (x : EPlane) (hi : x ∈ f i '' euclideanBody) :
    physicalPastedMap f hcover F x = F i x := by
  exact physical_tilewise_maps_agree f hdirect hdisjoint hcover V F hboundary
    (Classical.choose (hcover x)) i x (Classical.choose_spec (hcover x)) hi

end Tiling
end
end SpectreGeometry
