module

public import SpectreGeometry.ReversePhysicalClusterPathRoot00
public import SpectreGeometry.ReversePhysicalClusterPathRoot01
public import SpectreGeometry.ReversePhysicalClusterPathRoot02
public import SpectreGeometry.ReversePhysicalClusterPathRoot03
public import SpectreGeometry.ReversePhysicalClusterPathRoot04
public import SpectreGeometry.ReversePhysicalClusterPathRoot05

@[expose] public section

namespace SpectreGeometry.ReversePhysicalCluster
theorem physical_boundary_certificate_0 : PhysicalBoundaryCertificate 0 :=
  Fin.cases physical_boundary_root_0_0 (Fin.cases physical_boundary_root_0_1 (Fin.cases physical_boundary_root_0_2 (Fin.cases physical_boundary_root_0_3 (Fin.cases physical_boundary_root_0_4 (Fin.cases physical_boundary_root_0_5 (fun i => Fin.elim0 i))))))
end SpectreGeometry.ReversePhysicalCluster
