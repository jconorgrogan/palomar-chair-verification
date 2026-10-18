module

public import SpectreGeometry.ReverseClusterTriangulationData

@[expose] public section

namespace SpectreGeometry.ReverseClusterTriangulation
open SpectreClusters HalfplaneCertificate

def rawClusterBoxFacets : List Constraint := [(1,0,5),(-1,0,11),(0,1,11),(0,-1,7)]
def rawClusterBoxCheck (kind : ClusterKind) : Bool :=
  (clusterCells kind).all fun c => verticesSatisfyB (cellVertices c) rawClusterBoxFacets

theorem raw_t7h_box_checked : rawClusterBoxCheck .t7h = true := by decide
theorem raw_t8h_box_checked : rawClusterBoxCheck .t8h = true := by decide

theorem all_raw_cluster_boxes_checked (k : Fin 9) :
    rawClusterBoxCheck (SpectreClusters.ReverseExistence.clusterOfMark k) = true := by
  exact Fin.cases raw_t7h_box_checked
    (Fin.cases raw_t8h_box_checked (Fin.cases raw_t8h_box_checked
    (Fin.cases raw_t8h_box_checked (Fin.cases raw_t8h_box_checked
    (Fin.cases raw_t8h_box_checked (Fin.cases raw_t8h_box_checked
    (Fin.cases raw_t8h_box_checked (Fin.cases raw_t8h_box_checked
    (fun i => Fin.elim0 i))))))))) k

end SpectreGeometry.ReverseClusterTriangulation
