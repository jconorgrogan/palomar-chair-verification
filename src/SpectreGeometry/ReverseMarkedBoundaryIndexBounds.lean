module

public import SpectreGeometry.ReverseMarkedBoundaryParameters
public import SpectreGeometry.ReverseClusterTriangulationInjective
public import SpectreGeometry.ReverseClusterTriangulationReal

@[expose] public section


namespace SpectreGeometry.ReverseFinitePL
noncomputable section
open Set SpectreClusters ReverseClusterTriangulation

/-- Every boundary subdivision vertex is genuinely used by an incident mesh
triangle, including the final endpoint of a side. -/
theorem boundary_vertex_has_triangle (k : Fin 9) (d : Fin 6) (j : Nat)
    (hj : j < (boundaryIndices k d).length) :
    ∃ i : Fin (meshTriangles k).length,
      (boundaryIndices k d).getD j 0 ∈ triangleIndices ((meshTriangles k).get i) := by
  have hn := boundary_subdivision_pos k d
  by_cases he : j < (boundaryIndices k d).length-1
  · have ho := all_boundary_edge_owners k d j (List.mem_range.mpr he)
    dsimp only at ho
    refine ⟨⟨boundaryEdgeOwner k d j,ho.1⟩,?_⟩
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ho.1,
      Option.getD_some,List.get_eq_getElem] using ho.2.1
  · have hj0 : 0<j := by omega
    have hprev : j-1 < (boundaryIndices k d).length-1 := by omega
    have ho := all_boundary_edge_owners k d (j-1) (List.mem_range.mpr hprev)
    dsimp only at ho
    refine ⟨⟨boundaryEdgeOwner k d (j-1),ho.1⟩,?_⟩
    have heq : j-1+1=j := by omega
    rw [heq] at ho
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ho.1,
      Option.getD_some,List.get_eq_getElem] using ho.2.2

theorem boundary_vertex_index_bound (k : Fin 9) (d : Fin 6) (j : Nat)
    (hj : j < (boundaryIndices k d).length) :
    (boundaryIndices k d).getD j 0 < (sourceVertices k).length ∧
      (boundaryIndices k d).getD j 0 < (targetVertices k).length := by
  obtain ⟨i,hi⟩ := boundary_vertex_has_triangle k d j hj
  exact all_mesh_indices_bound k _ (List.get_mem _ i) _ hi

end
end SpectreGeometry.ReverseFinitePL
