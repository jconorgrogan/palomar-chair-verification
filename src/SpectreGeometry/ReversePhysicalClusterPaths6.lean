module

public import SpectreGeometry.ReversePhysicalClusterPathRoot60
public import SpectreGeometry.ReversePhysicalClusterPathRoot61
public import SpectreGeometry.ReversePhysicalClusterPathRoot62
public import SpectreGeometry.ReversePhysicalClusterPathRoot63
public import SpectreGeometry.ReversePhysicalClusterPathRoot64
public import SpectreGeometry.ReversePhysicalClusterPathRoot65

@[expose] public section

namespace SpectreGeometry.ReversePhysicalCluster
theorem physical_boundary_certificate_6 : PhysicalBoundaryCertificate 6 :=
  Fin.cases physical_boundary_root_6_0 (Fin.cases physical_boundary_root_6_1 (Fin.cases physical_boundary_root_6_2 (Fin.cases physical_boundary_root_6_3 (Fin.cases physical_boundary_root_6_4 (Fin.cases physical_boundary_root_6_5 (fun i => Fin.elim0 i))))))
end SpectreGeometry.ReversePhysicalCluster
