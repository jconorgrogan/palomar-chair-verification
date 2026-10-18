module

public import SpectreGeometry.ReversePhysicalClusterBoundaryOwnersData

@[expose] public section

namespace SpectreGeometry.ReversePhysicalClusterCharts
open SpectreClusters SpectreClusters.ReverseExistence
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem physical_boundary_chart_owner_0_0 : PhysicalBoundaryChartOwnerCertificate 0 0 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_0_1 : PhysicalBoundaryChartOwnerCertificate 0 1 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_0_2 : PhysicalBoundaryChartOwnerCertificate 0 2 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_0_3 : PhysicalBoundaryChartOwnerCertificate 0 3 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_0_4 : PhysicalBoundaryChartOwnerCertificate 0 4 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_0_5 : PhysicalBoundaryChartOwnerCertificate 0 5 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owners_0 : ∀ d : Fin 6, PhysicalBoundaryChartOwnerCertificate 0 d := by
  exact Fin.cases physical_boundary_chart_owner_0_0 (Fin.cases physical_boundary_chart_owner_0_1 (Fin.cases physical_boundary_chart_owner_0_2 (Fin.cases physical_boundary_chart_owner_0_3 (Fin.cases physical_boundary_chart_owner_0_4 (Fin.cases physical_boundary_chart_owner_0_5 ((fun i => Fin.elim0 i)))))))

end SpectreGeometry.ReversePhysicalClusterCharts
