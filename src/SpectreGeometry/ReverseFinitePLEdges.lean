module

public import SpectreGeometry.ReverseFinitePLInteger

@[expose] public section


namespace SpectreGeometry.ReverseFinitePL
noncomputable section
open Set

namespace IntegerMeshPair
variable (D : IntegerMeshPair)

theorem index_of_mem (j : Fin D.triangles.length) (n : Fin D.source.length)
    (hn : n.val ∈ SpectreGeometry.ReverseClusterTriangulation.triangleIndices (D.triangles.get j)) :
    ∃ v : Fin 3, D.meshIndex j v = n := by
  obtain ⟨v,hv⟩ := (mem_triangleIndices _ _).mp hn
  exact ⟨v,Fin.ext hv⟩

/-- Exact edge values with vertex-table indices, avoiding any assumption
that the edge is an entire triangle side in the original raw tile mesh. -/
theorem homeomorph_edge (j : Fin D.triangles.length) (n m : Fin D.source.length)
    (hn : n.val ∈ SpectreGeometry.ReverseClusterTriangulation.triangleIndices (D.triangles.get j))
    (hm : m.val ∈ SpectreGeometry.ReverseClusterTriangulation.triangleIndices (D.triangles.get j))
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : D.meshPair.closedCharts.sourceCarrier)
    (hx : x.val = AffineMap.lineMap (D.sourceVertex n) (D.sourceVertex m) t) :
    (D.homeomorph x).val = AffineMap.lineMap (D.targetVertex n) (D.targetVertex m) t := by
  obtain ⟨v,rfl⟩ := D.index_of_mem j n hn
  obtain ⟨w,rfl⟩ := D.index_of_mem j m hm
  exact D.meshPair.homeomorph_lineMap j v w t ht x hx

end IntegerMeshPair
end
end SpectreGeometry.ReverseFinitePL
