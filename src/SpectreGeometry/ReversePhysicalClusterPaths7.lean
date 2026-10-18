module

public import SpectreGeometry.ReversePhysicalClusterPathRoot70
public import SpectreGeometry.ReversePhysicalClusterPathRoot71
public import SpectreGeometry.ReversePhysicalClusterPathRoot72
public import SpectreGeometry.ReversePhysicalClusterPathRoot73
public import SpectreGeometry.ReversePhysicalClusterPathRoot74
public import SpectreGeometry.ReversePhysicalClusterPathRoot75

@[expose] public section

namespace SpectreGeometry.ReversePhysicalCluster
theorem physical_boundary_certificate_7 : PhysicalBoundaryCertificate 7 :=
  Fin.cases physical_boundary_root_7_0 (Fin.cases physical_boundary_root_7_1 (Fin.cases physical_boundary_root_7_2 (Fin.cases physical_boundary_root_7_3 (Fin.cases physical_boundary_root_7_4 (Fin.cases physical_boundary_root_7_5 (fun i => Fin.elim0 i))))))
end SpectreGeometry.ReversePhysicalCluster
