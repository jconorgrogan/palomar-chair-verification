module

public import SpectreClusters.ClusterBoundaryFast

@[expose] public section


namespace SpectreClusters

def clusterFilter (kind : ClusterKind) (edges : List Edge) : List Edge :=
  edges.filter (fun e => !((clusterAllEdges kind).any (edgeEqB (reverseEdge e))))

theorem clusterFilter_append (kind : ClusterKind) (a b : List Edge) :
    clusterFilter kind (a ++ b) = clusterFilter kind a ++ clusterFilter kind b := by
  simp only [clusterFilter,List.filter_append]

end SpectreClusters
