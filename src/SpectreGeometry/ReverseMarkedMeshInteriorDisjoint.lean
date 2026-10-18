module

public import SpectreGeometry.ReverseFinitePLMarkedClusterCore

@[expose] public section


namespace SpectreGeometry.ReverseFinitePL
noncomputable section
open Set SpectreClusters ReverseClusterTriangulation

/-- The packet family retains the pairwise interior-disjointness component
which is intentionally not part of the more general TriangleMeshPair API. -/
theorem packet_binding_interiors_disjoint (vs : List Point) (ts : List TriangleCode)
    (ps : List PolygonPacket)
    (hb : ps.map PolygonPacket.vertices = ts.map (triangleVertexList vs))
    (hf : FamilyHasFaces ps) (i j : Fin ts.length) (hij : i ≠ j) :
    Disjoint (interior (integerHull (triangleVertexList vs (ts.get i))))
      (interior (integerHull (triangleVertexList vs (ts.get j)))) := by
  have hi : i.val < ps.length := (packet_binding_length vs ts ps hb).symm ▸ i.isLt
  have hj : j.val < ps.length := (packet_binding_length vs ts ps hb).symm ▸ j.isLt
  have hn : (⟨i.val,hi⟩ : Fin ps.length) ≠ ⟨j.val,hj⟩ := by
    intro h
    exact hij (Fin.ext (congrArg (fun z : Fin ps.length => z.val) h))
  have h := (hf ⟨i.val,hi⟩ ⟨j.val,hj⟩ hn).2
  simpa only [packet_binding_at vs ts ps hb i,packet_binding_at vs ts ps hb j] using h

namespace MarkedMeshCertificate
variable {k : Fin 9} (C : MarkedMeshCertificate k)

theorem target_triangle_interiors_disjoint
    (i j : Fin (meshTriangles k).length) (hij : i ≠ j) :
    Disjoint (interior (C.markedIntegerMesh.meshPair.closedCharts.target i))
      (interior (C.markedIntegerMesh.meshPair.closedCharts.target j)) := by
  change Disjoint (interior (triangleHull (codeTriangle (targetVertices k) ((meshTriangles k).get i))))
    (interior (triangleHull (codeTriangle (targetVertices k) ((meshTriangles k).get j))))
  rw [codeTriangle_hull,codeTriangle_hull]
  exact packet_binding_interiors_disjoint (targetVertices k) (meshTriangles k) (targetFamily k)
    (all_target_family_vertices_bound k) C.target_faces i j hij

end MarkedMeshCertificate
end
end SpectreGeometry.ReverseFinitePL
