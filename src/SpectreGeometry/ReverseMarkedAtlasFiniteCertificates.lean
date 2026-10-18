module

public import SpectreGeometry.ReverseMarkedAtlasLocalHomeomorphism
public import SpectreGeometry.ReverseFinitePLMarkedCluster
public import SpectreGeometry.ReverseLocalStarRawStarCertificates
public import SpectreGeometry.ReverseLocalStarIncidentRowsCertificates
public import SpectreGeometry.ReverseLocalStarInteriorFastCertificates
public import SpectreGeometry.ReverseMeshEdgeIncidenceCertificates
public import SpectreGeometry.ReverseMeshBoundaryEdgeCertificates
public import SpectreGeometry.ReverseClusterNeighborCellsChecks
public import SpectreGeometry.ReverseClusterNeighborBinding
public import SpectreGeometry.ReverseLocalStarGeometryCertificates
public import SpectreGeometry.ReverseLocalStarGeometryBindings

@[expose] public section


namespace SpectreGeometry.ReverseExistence
open ReverseFinitePL ReverseLocalStarOccurrences ReverseMeshEdgeIncidence
open ReverseClusterNeighborCells ReverseClusterNeighborBinding

/-- Every finite input required by the marked whole-plane construction is
supplied by a literal finite certificate theorem. -/
def markedAtlasFiniteCertificates : MarkedAtlasFiniteInputs where
  mesh := markedMeshCertificate
  raw := all_raw_star_bindings
  rows := all_incident_rows_correct
  interiorStar := all_interior_fast_certificates
  edgeIncidence := all_edge_incidence_certificates
  boundaryEdges := all_boundary_edge_certificates
  neighborChecked := all_configurations_checked
  neighborBinding := all_marked_configuration_certificates
  sideGeometry := all_side_geometry_certificates
  sideBinding := all_side_geometry_bindings
  tripleGeometry := all_triple_geometry_certificates
  tripleBinding := all_triple_geometry_bindings

end SpectreGeometry.ReverseExistence
