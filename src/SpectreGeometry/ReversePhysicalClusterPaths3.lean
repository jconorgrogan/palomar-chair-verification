module

public import SpectreGeometry.ReversePhysicalClusterPathRoot30
public import SpectreGeometry.ReversePhysicalClusterPathRoot31
public import SpectreGeometry.ReversePhysicalClusterPathRoot32
public import SpectreGeometry.ReversePhysicalClusterPathRoot33
public import SpectreGeometry.ReversePhysicalClusterPathRoot34
public import SpectreGeometry.ReversePhysicalClusterPathRoot35

@[expose] public section

namespace SpectreGeometry.ReversePhysicalCluster
theorem physical_boundary_certificate_3 : PhysicalBoundaryCertificate 3 :=
  Fin.cases physical_boundary_root_3_0 (Fin.cases physical_boundary_root_3_1 (Fin.cases physical_boundary_root_3_2 (Fin.cases physical_boundary_root_3_3 (Fin.cases physical_boundary_root_3_4 (Fin.cases physical_boundary_root_3_5 (fun i => Fin.elim0 i))))))
end SpectreGeometry.ReversePhysicalCluster
