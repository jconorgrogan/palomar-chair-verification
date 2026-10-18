module

public import SpectreGeometry.ReversePhysicalClusterInverseMap
public import SpectreGeometry.ReversePhysicalClusterBoundaryOwners
public import SpectreGeometry.ReversePhysicalClusterPathsData

@[expose] public section


namespace SpectreGeometry.ReversePhysicalClusterCharts
noncomputable section
open Set SpectreClusters SpectreClusters.ReverseExistence Deformation ReverseExistence ReversePhysicalCluster
open ReverseClusterTriangulation

/-- The actual inverse cluster map carries each literal marked boundary path
with its exact parameter to the independently constructed physical P path. -/
theorem rawClusterInverseMap_markedBoundary
    (hbinding : ∀ big z, z < (chartFamily big).length → ChartPacketBinding big z)
    (hfaces : ∀ big z, z < (chartFamily big).length → ChartFaceRowCheck big z)
    (k : Fin 9) (d : Fin 6) (t : ℝ) (x : RealPoint)
    (hx : PathParameter (((markedPaths k).getD d.val []).map integerPoint) t x) :
    PathParameter ((physicalPath4 k d).map quarterPoint) t
      (euclideanCoordinates.symm (rawClusterInverseMap (k.val != 0) x)) := by
  have howner (j : Nat) (hj : j < ((markedPaths k).getD d.val []).length-1) :
      ∃ z : Fin (chartFamily (k.val != 0)).length,
        ((markedPaths k).getD d.val []).getD j (0,0) ∈
          ((chartFamily (k.val != 0)).getD z.val default).vertices ∧
        ((markedPaths k).getD d.val []).getD (j+1) (0,0) ∈
          ((chartFamily (k.val != 0)).getD z.val default).vertices := by
    obtain ⟨z,hz,ha,hb⟩ := marked_path_edge_has_chart k d j (by omega)
    exact ⟨⟨z,hz⟩,ha,hb⟩
  have h := rawClusterInverseMap_pathParameter hbinding hfaces (k.val != 0)
    ((markedPaths k).getD d.val []) howner t x hx
  simpa only [physicalPath4,List.map_map,Function.comp_def] using h

end
end SpectreGeometry.ReversePhysicalClusterCharts
