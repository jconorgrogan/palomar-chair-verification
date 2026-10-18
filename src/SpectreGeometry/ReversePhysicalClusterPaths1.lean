module

public import SpectreGeometry.ReversePhysicalClusterPathRoot10
public import SpectreGeometry.ReversePhysicalClusterPathRoot11
public import SpectreGeometry.ReversePhysicalClusterPathRoot12
public import SpectreGeometry.ReversePhysicalClusterPathRoot13
public import SpectreGeometry.ReversePhysicalClusterPathRoot14
public import SpectreGeometry.ReversePhysicalClusterPathRoot15

@[expose] public section

namespace SpectreGeometry.ReversePhysicalCluster
theorem physical_boundary_certificate_1 : PhysicalBoundaryCertificate 1 :=
  Fin.cases physical_boundary_root_1_0 (Fin.cases physical_boundary_root_1_1 (Fin.cases physical_boundary_root_1_2 (Fin.cases physical_boundary_root_1_3 (Fin.cases physical_boundary_root_1_4 (Fin.cases physical_boundary_root_1_5 (fun i => Fin.elim0 i))))))
end SpectreGeometry.ReversePhysicalCluster
