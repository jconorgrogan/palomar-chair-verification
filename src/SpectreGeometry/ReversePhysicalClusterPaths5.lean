module

public import SpectreGeometry.ReversePhysicalClusterPathRoot50
public import SpectreGeometry.ReversePhysicalClusterPathRoot51
public import SpectreGeometry.ReversePhysicalClusterPathRoot52
public import SpectreGeometry.ReversePhysicalClusterPathRoot53
public import SpectreGeometry.ReversePhysicalClusterPathRoot54
public import SpectreGeometry.ReversePhysicalClusterPathRoot55

@[expose] public section

namespace SpectreGeometry.ReversePhysicalCluster
theorem physical_boundary_certificate_5 : PhysicalBoundaryCertificate 5 :=
  Fin.cases physical_boundary_root_5_0 (Fin.cases physical_boundary_root_5_1 (Fin.cases physical_boundary_root_5_2 (Fin.cases physical_boundary_root_5_3 (Fin.cases physical_boundary_root_5_4 (Fin.cases physical_boundary_root_5_5 (fun i => Fin.elim0 i))))))
end SpectreGeometry.ReversePhysicalCluster
