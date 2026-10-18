module

public import SpectreGeometry.ReverseClusterTriangulationSource00Injective
public import SpectreGeometry.ReverseClusterTriangulationSource01Injective
public import SpectreGeometry.ReverseClusterTriangulationSource02Injective
public import SpectreGeometry.ReverseClusterTriangulationSource03Injective
public import SpectreGeometry.ReverseClusterTriangulationSource04Injective
public import SpectreGeometry.ReverseClusterTriangulationSource05Injective
public import SpectreGeometry.ReverseClusterTriangulationSource06Injective
public import SpectreGeometry.ReverseClusterTriangulationSource07Injective
public import SpectreGeometry.ReverseClusterTriangulationSource08Injective
public import SpectreGeometry.ReverseClusterTriangulationTarget00Injective
public import SpectreGeometry.ReverseClusterTriangulationTarget01Injective

@[expose] public section

namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem all_source_vertices_distinct : ∀ k : Fin 9, (sourceVertices k).Nodup := by
  exact Fin.cases (source0_vertices_distinct) (Fin.cases (source1_vertices_distinct) (Fin.cases (source2_vertices_distinct) (Fin.cases (source3_vertices_distinct) (Fin.cases (source4_vertices_distinct) (Fin.cases (source5_vertices_distinct) (Fin.cases (source6_vertices_distinct) (Fin.cases (source7_vertices_distinct) (Fin.cases (source8_vertices_distinct) (fun i => Fin.elim0 i)))))))))
theorem all_target_vertices_distinct : ∀ k : Fin 9, (targetVertices k).Nodup := by
  exact Fin.cases (target0_vertices_distinct) (Fin.cases (target1_vertices_distinct) (Fin.cases (target1_vertices_distinct) (Fin.cases (target1_vertices_distinct) (Fin.cases (target1_vertices_distinct) (Fin.cases (target1_vertices_distinct) (Fin.cases (target1_vertices_distinct) (Fin.cases (target1_vertices_distinct) (Fin.cases (target1_vertices_distinct) (fun i => Fin.elim0 i)))))))))
theorem t7h_mesh_indices_bound : ∀ t ∈ meshTrianglesT7H, ∀ i ∈ triangleIndices t, i < 127 := by decide
theorem t8h_mesh_indices_bound : ∀ t ∈ meshTrianglesT8H, ∀ i ∈ triangleIndices t, i < 133 := by decide
theorem all_source_lengths : ∀ k : Fin 9, (sourceVertices k).length = if k.val=0 then 127 else 133 := by decide
theorem all_target_lengths : ∀ k : Fin 9, (targetVertices k).length = if k.val=0 then 127 else 133 := by decide
theorem all_mesh_indices_bound : ∀ k : Fin 9, ∀ t ∈ meshTriangles k,
    ∀ i ∈ triangleIndices t, i < (sourceVertices k).length ∧ i < (targetVertices k).length := by
  intro k t ht i hi
  rw [all_source_lengths,all_target_lengths]
  by_cases hk : k.val=0
  · simp only [hk,if_true]
    have h : t ∈ meshTrianglesT7H := by simpa [meshTriangles,hk] using ht
    exact ⟨t7h_mesh_indices_bound t h i hi,t7h_mesh_indices_bound t h i hi⟩
  · simp only [hk,if_false]
    have h : t ∈ meshTrianglesT8H := by simpa [meshTriangles,hk] using ht
    exact ⟨t8h_mesh_indices_bound t h i hi,t8h_mesh_indices_bound t h i hi⟩
end SpectreGeometry.ReverseClusterTriangulation
