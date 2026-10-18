module

public import SpectreGeometry.ReversePhysicalClusterPathRoot20
public import SpectreGeometry.ReversePhysicalClusterPathRoot21
public import SpectreGeometry.ReversePhysicalClusterPathRoot22
public import SpectreGeometry.ReversePhysicalClusterPathRoot23
public import SpectreGeometry.ReversePhysicalClusterPathRoot24
public import SpectreGeometry.ReversePhysicalClusterPathRoot25

@[expose] public section

namespace SpectreGeometry.ReversePhysicalCluster
theorem physical_boundary_certificate_2 : PhysicalBoundaryCertificate 2 :=
  Fin.cases physical_boundary_root_2_0 (Fin.cases physical_boundary_root_2_1 (Fin.cases physical_boundary_root_2_2 (Fin.cases physical_boundary_root_2_3 (Fin.cases physical_boundary_root_2_4 (Fin.cases physical_boundary_root_2_5 (fun i => Fin.elim0 i))))))
end SpectreGeometry.ReversePhysicalCluster
