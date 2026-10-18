module

public import SpectreGeometry.ReversePhysicalClusterBoundaryOwnersData

@[expose] public section

namespace SpectreGeometry.ReversePhysicalClusterCharts
open SpectreClusters SpectreClusters.ReverseExistence
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem physical_boundary_chart_owner_4_0 : PhysicalBoundaryChartOwnerCertificate 4 0 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_4_1 : PhysicalBoundaryChartOwnerCertificate 4 1 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_4_2 : PhysicalBoundaryChartOwnerCertificate 4 2 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_4_3 : PhysicalBoundaryChartOwnerCertificate 4 3 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_4_4 : PhysicalBoundaryChartOwnerCertificate 4 4 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owner_4_5 : PhysicalBoundaryChartOwnerCertificate 4 5 := by
  unfold PhysicalBoundaryChartOwnerCertificate
  decide

theorem physical_boundary_chart_owners_4 : ∀ d : Fin 6, PhysicalBoundaryChartOwnerCertificate 4 d := by
  exact Fin.cases physical_boundary_chart_owner_4_0 (Fin.cases physical_boundary_chart_owner_4_1 (Fin.cases physical_boundary_chart_owner_4_2 (Fin.cases physical_boundary_chart_owner_4_3 (Fin.cases physical_boundary_chart_owner_4_4 (Fin.cases physical_boundary_chart_owner_4_5 ((fun i => Fin.elim0 i)))))))

end SpectreGeometry.ReversePhysicalClusterCharts
