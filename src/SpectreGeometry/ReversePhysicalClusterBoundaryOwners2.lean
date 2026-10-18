module

public import SpectreGeometry.ReversePhysicalClusterBoundaryOwnersData

@[expose] public section

namespace SpectreGeometry.ReversePhysicalClusterCharts
open SpectreClusters SpectreClusters.ReverseExistence
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem physical_boundary_chart_owner_2_0 : PhysicalBoundaryChartOwnerCertificate 2 0 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_2_1 : PhysicalBoundaryChartOwnerCertificate 2 1 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_2_2 : PhysicalBoundaryChartOwnerCertificate 2 2 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_2_3 : PhysicalBoundaryChartOwnerCertificate 2 3 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_2_4 : PhysicalBoundaryChartOwnerCertificate 2 4 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_2_5 : PhysicalBoundaryChartOwnerCertificate 2 5 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owners_2 : ∀ d : Fin 6, PhysicalBoundaryChartOwnerCertificate 2 d := by
  exact Fin.cases physical_boundary_chart_owner_2_0 (Fin.cases physical_boundary_chart_owner_2_1 (Fin.cases physical_boundary_chart_owner_2_2 (Fin.cases physical_boundary_chart_owner_2_3 (Fin.cases physical_boundary_chart_owner_2_4 (Fin.cases physical_boundary_chart_owner_2_5 ((fun i => Fin.elim0 i)))))))

end SpectreGeometry.ReversePhysicalClusterCharts
