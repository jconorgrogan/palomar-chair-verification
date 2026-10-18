module

public import SpectreGeometry.ReversePhysicalClusterPathRoot40
public import SpectreGeometry.ReversePhysicalClusterPathRoot41
public import SpectreGeometry.ReversePhysicalClusterPathRoot42
public import SpectreGeometry.ReversePhysicalClusterPathRoot43
public import SpectreGeometry.ReversePhysicalClusterPathRoot44
public import SpectreGeometry.ReversePhysicalClusterPathRoot45

@[expose] public section

namespace SpectreGeometry.ReversePhysicalCluster
theorem physical_boundary_certificate_4 : PhysicalBoundaryCertificate 4 :=
  Fin.cases physical_boundary_root_4_0 (Fin.cases physical_boundary_root_4_1 (Fin.cases physical_boundary_root_4_2 (Fin.cases physical_boundary_root_4_3 (Fin.cases physical_boundary_root_4_4 (Fin.cases physical_boundary_root_4_5 (fun i => Fin.elim0 i))))))
end SpectreGeometry.ReversePhysicalCluster
