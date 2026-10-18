module

public import SpectreGeometry.ReverseFinitePLPackets
public import SpectreGeometry.ReverseClusterTriangulationCarriers
public import SpectreGeometry.ReverseClusterTriangulationInjective
public import SpectreGeometry.ReverseClusterTriangulationFacesAssemblyReal
public import SpectreGeometry.ReverseClusterTriangulationNormalized
public import SpectreGeometry.ReverseFinitePLMarkedEdges
public import SpectreGeometry.ReverseMarkedBoundaryParameters
public import SpectreGeometry.ReverseMarkedBoundaryPathLaw

@[expose] public section


/-! Binding the genuine PL mesh homeomorphisms to the nine literal marked
cluster carriers. This module does not yet glue different source hexagons. -/
namespace SpectreGeometry.ReverseFinitePL
noncomputable section
open Set SpectreClusters ReverseClusterTriangulation

structure MarkedMeshCertificate (k : Fin 9) : Prop where
  source_faces : FamilyHasFaces (sourceFamily k)
  target_faces : FamilyHasFaces (targetFamily k)

namespace MarkedMeshCertificate
variable {k : Fin 9} (C : MarkedMeshCertificate k)

def markedIntegerMesh : IntegerMeshPair :=
  IntegerMeshPair.ofPackets (sourceVertices k) (targetVertices k) (meshTriangles k)
    (sourceFamily k) (targetFamily k)
    (by rw [all_source_lengths,all_target_lengths])
    (all_source_vertices_distinct k) (all_target_vertices_distinct k)
    (fun t ht n hn => (all_mesh_indices_bound k t ht n hn).1)
    (all_source_family_vertices_bound k) (all_target_family_vertices_bound k)
    (all_source_family_checked k) (all_target_family_checked k)
    C.source_faces C.target_faces

theorem markedIntegerMesh_source :
    (C.markedIntegerMesh).meshPair.closedCharts.sourceCarrier = familyBody (sourceFamily k) :=
  (C.markedIntegerMesh).sourceCarrier_eq.trans
    (packet_binding_familyBody _ _ _ (all_source_family_vertices_bound k)).symm

theorem markedIntegerMesh_target :
    (C.markedIntegerMesh).meshPair.closedCharts.targetCarrier = familyBody (targetFamily k) :=
  (C.markedIntegerMesh).targetCarrier_eq.trans
    (packet_binding_familyBody _ _ _ (all_target_family_vertices_bound k)).symm

def markedIntegerHomeomorph :
    familyBody (sourceFamily k) ≃ₜ familyBody (targetFamily k) :=
  (Homeomorph.setCongr (C.markedIntegerMesh_source).symm).trans
    ((C.markedIntegerMesh).homeomorph.trans (Homeomorph.setCongr (C.markedIntegerMesh_target)))

theorem sourceScale_real_pos (k : Fin 9) : (0:ℝ) < 3*sourceScale k := by
  have h : (0:ℝ) < sourceScale k := by exact_mod_cast all_source_scales_positive k
  positivity


theorem markedNormalizedSource :
    (fun p : Plane => (1/(3*(sourceScale k:ℝ))) • p) ''
      (C.markedIntegerMesh).meshPair.closedCharts.sourceCarrier =
      ReverseExistence.sourceHexCarrier (0,0) := by
  rw [markedIntegerMesh_source]
  exact all_normalized_source_carriers_eq_sourceHexCarrier k

theorem markedNormalizedTarget :
    (fun p : Plane => (1/6:ℝ) • p) ''
      (C.markedIntegerMesh).meshPair.closedCharts.targetCarrier =
      rawClusterBody (SpectreClusters.ReverseExistence.clusterOfMark k) := by
  rw [markedIntegerMesh_target]
  exact all_normalized_target_carriers_exact k

/-- Each of the nine literal raw closed cluster carriers is actually
homeomorphic to the prescribed closed regular hexagon. -/
def markedClusterHomeomorph :
    ReverseExistence.sourceHexCarrier (0,0) ≃ₜ
      rawClusterBody (SpectreClusters.ReverseExistence.clusterOfMark k) :=
  (Homeomorph.setCongr (C.markedNormalizedSource).symm).trans
    (((C.markedIntegerMesh).scaledHomeomorph (1/(3*(sourceScale k:ℝ))) (1/6)
      (one_div_ne_zero (ne_of_gt (sourceScale_real_pos k))) (by norm_num)).trans
        (Homeomorph.setCongr (C.markedNormalizedTarget)))

/-- Exact values on every uniform source-side subinterval. -/
theorem markedClusterHomeomorph_boundary_edge (d : Fin 6)
    (j : Nat) (hj : j < (boundaryIndices k d).length-1)
    (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1)
    (x : ReverseExistence.sourceHexCarrier (0,0))
    (hx : x.val = AffineMap.lineMap (ReverseExistence.sourceHexCorner d)
      (ReverseExistence.sourceHexCorner (d+1))
      (((j:ℝ)+u)/((boundaryIndices k d).length-1))) :
    (C.markedClusterHomeomorph x).val =
      AffineMap.lineMap
        ((1/6:ℝ) • integerPoint (targetVertex k ((boundaryIndices k d).getD j 0)))
        ((1/6:ℝ) • integerPoint (targetVertex k ((boundaryIndices k d).getD (j+1) 0))) u := by
  exact scaledMarkedMesh_boundary_edge (C.markedIntegerMesh) k rfl rfl rfl d j hj u hu
    (one_div_ne_zero (ne_of_gt (sourceScale_real_pos k)))
    ((Homeomorph.setCongr (C.markedNormalizedSource).symm) x) hx

/-- The exact path-parameter interface required by whole-plane chart gluing. -/
theorem markedClusterHomeomorph_boundary_law :
    ReverseExistence.MarkedBoundarySubintervalLaw k (fun x => (C.markedClusterHomeomorph x).val) :=
  C.markedClusterHomeomorph_boundary_edge

end MarkedMeshCertificate
end
end SpectreGeometry.ReverseFinitePL
