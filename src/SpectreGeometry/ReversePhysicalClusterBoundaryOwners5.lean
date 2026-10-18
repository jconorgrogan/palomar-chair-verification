module

public import SpectreGeometry.ReversePhysicalClusterBoundaryOwnersData

@[expose] public section

namespace SpectreGeometry.ReversePhysicalClusterCharts
open SpectreClusters SpectreClusters.ReverseExistence
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem physical_boundary_chart_owner_5_0 : PhysicalBoundaryChartOwnerCertificate 5 0 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_5_1 : PhysicalBoundaryChartOwnerCertificate 5 1 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_5_2 : PhysicalBoundaryChartOwnerCertificate 5 2 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_5_3 : PhysicalBoundaryChartOwnerCertificate 5 3 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_5_4 : PhysicalBoundaryChartOwnerCertificate 5 4 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_5_5 : PhysicalBoundaryChartOwnerCertificate 5 5 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owners_5 : ∀ d : Fin 6, PhysicalBoundaryChartOwnerCertificate 5 d := by
  exact Fin.cases physical_boundary_chart_owner_5_0 (Fin.cases physical_boundary_chart_owner_5_1 (Fin.cases physical_boundary_chart_owner_5_2 (Fin.cases physical_boundary_chart_owner_5_3 (Fin.cases physical_boundary_chart_owner_5_4 (Fin.cases physical_boundary_chart_owner_5_5 ((fun i => Fin.elim0 i)))))))

end SpectreGeometry.ReversePhysicalClusterCharts
