module

public import SpectreGeometry.ReversePhysicalClusterPathRoot80
public import SpectreGeometry.ReversePhysicalClusterPathRoot81
public import SpectreGeometry.ReversePhysicalClusterPathRoot82
public import SpectreGeometry.ReversePhysicalClusterPathRoot83
public import SpectreGeometry.ReversePhysicalClusterPathRoot84
public import SpectreGeometry.ReversePhysicalClusterPathRoot85

@[expose] public section

namespace SpectreGeometry.ReversePhysicalCluster
theorem physical_boundary_certificate_8 : PhysicalBoundaryCertificate 8 :=
  Fin.cases physical_boundary_root_8_0 (Fin.cases physical_boundary_root_8_1 (Fin.cases physical_boundary_root_8_2 (Fin.cases physical_boundary_root_8_3 (Fin.cases physical_boundary_root_8_4 (Fin.cases physical_boundary_root_8_5 (fun i => Fin.elim0 i))))))
end SpectreGeometry.ReversePhysicalCluster
