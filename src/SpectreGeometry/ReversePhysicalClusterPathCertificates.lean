module

public import SpectreGeometry.ReversePhysicalClusterPaths0
public import SpectreGeometry.ReversePhysicalClusterPaths1
public import SpectreGeometry.ReversePhysicalClusterPaths2
public import SpectreGeometry.ReversePhysicalClusterPaths3
public import SpectreGeometry.ReversePhysicalClusterPaths4
public import SpectreGeometry.ReversePhysicalClusterPaths5
public import SpectreGeometry.ReversePhysicalClusterPaths6
public import SpectreGeometry.ReversePhysicalClusterPaths7
public import SpectreGeometry.ReversePhysicalClusterPaths8

@[expose] public section

namespace SpectreGeometry.ReversePhysicalCluster
set_option maxRecDepth 100000

theorem all_physical_boundary_certificates : ∀ k : Fin 9, PhysicalBoundaryCertificate k := by
  exact Fin.cases physical_boundary_certificate_0 (Fin.cases physical_boundary_certificate_1 (Fin.cases physical_boundary_certificate_2 (Fin.cases physical_boundary_certificate_3 (Fin.cases physical_boundary_certificate_4 (Fin.cases physical_boundary_certificate_5 (Fin.cases physical_boundary_certificate_6 (Fin.cases physical_boundary_certificate_7 (Fin.cases physical_boundary_certificate_8 ((fun i => Fin.elim0 i))))))))))

end SpectreGeometry.ReversePhysicalCluster
