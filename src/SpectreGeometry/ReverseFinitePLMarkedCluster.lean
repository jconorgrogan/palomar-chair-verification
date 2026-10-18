module

public import SpectreGeometry.ReverseFinitePLMarkedClusterCore
public import SpectreGeometry.ReverseClusterTriangulationPublic

@[expose] public section


namespace SpectreGeometry.ReverseFinitePL
noncomputable section
open ReverseClusterTriangulation

def markedMeshCertificate (k : Fin 9) : MarkedMeshCertificate k :=
  ⟨all_source_families_have_faces k,all_target_families_have_faces k⟩

def markedIntegerMesh (k : Fin 9) : IntegerMeshPair :=
  (markedMeshCertificate k).markedIntegerMesh

/-- All nine actual closed cluster carriers with the declared source hexagon. -/
def markedClusterHomeomorph (k : Fin 9) : ReverseExistence.sourceHexCarrier (0,0) ≃ₜ
    rawClusterBody (SpectreClusters.ReverseExistence.clusterOfMark k) :=
  (markedMeshCertificate k).markedClusterHomeomorph

theorem markedClusterHomeomorph_boundary_law (k : Fin 9) :
    ReverseExistence.MarkedBoundarySubintervalLaw k (fun x => (markedClusterHomeomorph k x).val) :=
  (markedMeshCertificate k).markedClusterHomeomorph_boundary_law

end
end SpectreGeometry.ReverseFinitePL
