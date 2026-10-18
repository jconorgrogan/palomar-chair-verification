module

public import SpectreGeometry.ReversePhysicalClusterBoundaryOwnersData

@[expose] public section

namespace SpectreGeometry.ReversePhysicalClusterCharts
open SpectreClusters SpectreClusters.ReverseExistence
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem physical_boundary_chart_owner_1_0 : PhysicalBoundaryChartOwnerCertificate 1 0 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_1_1 : PhysicalBoundaryChartOwnerCertificate 1 1 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_1_2 : PhysicalBoundaryChartOwnerCertificate 1 2 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_1_3 : PhysicalBoundaryChartOwnerCertificate 1 3 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_1_4 : PhysicalBoundaryChartOwnerCertificate 1 4 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_1_5 : PhysicalBoundaryChartOwnerCertificate 1 5 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owners_1 : ∀ d : Fin 6, PhysicalBoundaryChartOwnerCertificate 1 d := by
  exact Fin.cases physical_boundary_chart_owner_1_0 (Fin.cases physical_boundary_chart_owner_1_1 (Fin.cases physical_boundary_chart_owner_1_2 (Fin.cases physical_boundary_chart_owner_1_3 (Fin.cases physical_boundary_chart_owner_1_4 (Fin.cases physical_boundary_chart_owner_1_5 ((fun i => Fin.elim0 i)))))))

end SpectreGeometry.ReversePhysicalClusterCharts
