module

public import SpectreGeometry.ReverseFinitePLMesh
public import SpectreGeometry.ReverseTrianglePointClassification

@[expose] public section


namespace SpectreGeometry.ReverseFinitePL
noncomputable section
open Set
namespace TriangleMeshPair

/-- Boundary vertex and open-edge neighborhoods suffice; triangle interiors are
transported by the genuine ambient affine homeomorphisms. -/
theorem homeomorph_mem_interior_of_boundary {V ι : Type*} [Finite ι]
    (D : TriangleMeshPair V ι) (x : D.closedCharts.sourceCarrier) (T : Set Plane)
    (hT : D.closedCharts.targetCarrier ⊆ T)
    (hv : ∀ i v, x.val = D.sourceVertex (D.index i v) →
      D.targetVertex (D.index i v) ∈ interior T)
    (he : ∀ i v w, v ≠ w → ∀ t ∈ Ioo (0:ℝ) 1,
      x.val = AffineMap.lineMap (D.sourceVertex (D.index i v))
        (D.sourceVertex (D.index i w)) t →
      AffineMap.lineMap (D.targetVertex (D.index i v))
        (D.targetVertex (D.index i w)) t ∈ interior T) :
    (D.homeomorph x).val ∈ interior T := by
  obtain ⟨i,hi⟩ := mem_iUnion.mp x.property
  rcases triangle_point_classification (D.sourceVertex ∘ D.index i)
    (D.source_nondegenerate i) hi with ⟨v,hx⟩ | ⟨v,w,hvw,t,ht,hx⟩ | hx
  · rw [D.homeomorph_on i x hi,hx]
    simpa only [Function.comp_apply,D.affineChart_vertex] using hv i v hx
  · rw [D.homeomorph_lineMap i v w t ⟨le_of_lt ht.1,le_of_lt ht.2⟩ x hx]
    exact he i v w hvw t ht hx
  · have hm : D.closedCharts.chart i x.val ∈ interior (D.closedCharts.target i) := by
      rw [←D.closedCharts.image_source i,←(D.closedCharts.chart i).image_interior]
      exact mem_image_of_mem _ hx
    have hs : D.closedCharts.target i ⊆ T := by
      intro y hy
      exact hT (mem_iUnion.mpr ⟨i,hy⟩)
    rw [D.homeomorph_on i x hi]
    exact interior_mono hs hm

end TriangleMeshPair
end
end SpectreGeometry.ReverseFinitePL
