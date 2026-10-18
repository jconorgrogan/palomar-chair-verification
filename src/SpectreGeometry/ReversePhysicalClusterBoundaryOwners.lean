module

public import SpectreGeometry.ReversePhysicalClusterBoundaryOwners0
public import SpectreGeometry.ReversePhysicalClusterBoundaryOwners1
public import SpectreGeometry.ReversePhysicalClusterBoundaryOwners2
public import SpectreGeometry.ReversePhysicalClusterBoundaryOwners3
public import SpectreGeometry.ReversePhysicalClusterBoundaryOwners4
public import SpectreGeometry.ReversePhysicalClusterBoundaryOwners5
public import SpectreGeometry.ReversePhysicalClusterBoundaryOwners6
public import SpectreGeometry.ReversePhysicalClusterBoundaryOwners7
public import SpectreGeometry.ReversePhysicalClusterBoundaryOwners8

@[expose] public section

namespace SpectreGeometry.ReversePhysicalClusterCharts
open SpectreClusters SpectreClusters.ReverseExistence
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem all_physical_boundary_chart_owners : ∀ (k : Fin 9) (d : Fin 6), PhysicalBoundaryChartOwnerCertificate k d := by
  exact Fin.cases physical_boundary_chart_owners_0 (Fin.cases physical_boundary_chart_owners_1 (Fin.cases physical_boundary_chart_owners_2 (Fin.cases physical_boundary_chart_owners_3 (Fin.cases physical_boundary_chart_owners_4 (Fin.cases physical_boundary_chart_owners_5 (Fin.cases physical_boundary_chart_owners_6 (Fin.cases physical_boundary_chart_owners_7 (Fin.cases physical_boundary_chart_owners_8 ((fun i => Fin.elim0 i))))))))))

theorem marked_path_edge_has_chart (k : Fin 9) (d : Fin 6) (j : Nat)
    (hj : j+1 < ((markedPaths k).getD d.val []).length) :
    ∃ z : Nat, z < (chartFamily (k.val != 0)).length ∧
      ((markedPaths k).getD d.val []).getD j (0,0) ∈
        ((chartFamily (k.val != 0)).getD z default).vertices ∧
      ((markedPaths k).getD d.val []).getD (j+1) (0,0) ∈
        ((chartFamily (k.val != 0)).getD z default).vertices := by
  refine ⟨physicalBoundaryChartOwner k d j, ?_⟩
  exact all_physical_boundary_chart_owners k d j (List.mem_range.mpr (by omega))

end SpectreGeometry.ReversePhysicalClusterCharts
