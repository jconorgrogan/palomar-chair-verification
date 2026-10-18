module

public import SpectreGeometry.ReverseClusterTriangulationSource00
public import SpectreGeometry.ReverseClusterTriangulationSource01
public import SpectreGeometry.ReverseClusterTriangulationSource02
public import SpectreGeometry.ReverseClusterTriangulationSource03
public import SpectreGeometry.ReverseClusterTriangulationSource04
public import SpectreGeometry.ReverseClusterTriangulationSource05
public import SpectreGeometry.ReverseClusterTriangulationSource06
public import SpectreGeometry.ReverseClusterTriangulationSource07
public import SpectreGeometry.ReverseClusterTriangulationSource08
public import SpectreGeometry.ReverseClusterTriangulationTarget00
public import SpectreGeometry.ReverseClusterTriangulationTarget01
public import SpectreGeometry.ReverseClusterTriangulationScaleReal

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
noncomputable section
open Set SpectreClusters
set_option maxRecDepth 100000

def sourceFamilyTable : List (List PolygonPacket) := [sourceFamily0,sourceFamily1,sourceFamily2,sourceFamily3,sourceFamily4,sourceFamily5,sourceFamily6,sourceFamily7,sourceFamily8]
def sourceFamily (k : Fin 9) : List PolygonPacket := sourceFamilyTable.getD k.val []
def targetFamily (k : Fin 9) : List PolygonPacket := if k.val=0 then targetMeshFamily0 else targetMeshFamily1
def sourceHexFacetTable : List (List HalfplaneCertificate.Constraint) := [sourceHexFacets0,sourceHexFacets1,sourceHexFacets2,sourceHexFacets3,sourceHexFacets4,sourceHexFacets5,sourceHexFacets6,sourceHexFacets7,sourceHexFacets8]
def sourceHexFacets (k : Fin 9) : List HalfplaneCertificate.Constraint := sourceHexFacetTable.getD k.val []

theorem all_source_family_checked : ∀ k : Fin 9, familyCheckedB (sourceFamily k) = true := by
  exact Fin.cases (sourceFamily0_checked) (Fin.cases (sourceFamily1_checked) (Fin.cases (sourceFamily2_checked) (Fin.cases (sourceFamily3_checked) (Fin.cases (sourceFamily4_checked) (Fin.cases (sourceFamily5_checked) (Fin.cases (sourceFamily6_checked) (Fin.cases (sourceFamily7_checked) (Fin.cases (sourceFamily8_checked) (fun i => Fin.elim0 i)))))))))
theorem all_target_family_checked : ∀ k : Fin 9, familyCheckedB (targetFamily k) = true := by
  exact Fin.cases (targetMeshFamily0_checked) (Fin.cases (targetMeshFamily1_checked) (Fin.cases (targetMeshFamily1_checked) (Fin.cases (targetMeshFamily1_checked) (Fin.cases (targetMeshFamily1_checked) (Fin.cases (targetMeshFamily1_checked) (Fin.cases (targetMeshFamily1_checked) (Fin.cases (targetMeshFamily1_checked) (Fin.cases (targetMeshFamily1_checked) (fun i => Fin.elim0 i)))))))))
theorem all_source_family_vertices_bound : ∀ k : Fin 9, (sourceFamily k).map PolygonPacket.vertices =
    (meshTriangles k).map (triangleVertexList (sourceVertices k)) := by
  exact Fin.cases (sourceFamily0_vertices_bound) (Fin.cases (sourceFamily1_vertices_bound) (Fin.cases (sourceFamily2_vertices_bound) (Fin.cases (sourceFamily3_vertices_bound) (Fin.cases (sourceFamily4_vertices_bound) (Fin.cases (sourceFamily5_vertices_bound) (Fin.cases (sourceFamily6_vertices_bound) (Fin.cases (sourceFamily7_vertices_bound) (Fin.cases (sourceFamily8_vertices_bound) (fun i => Fin.elim0 i)))))))))
theorem all_target_family_vertices_bound : ∀ k : Fin 9, (targetFamily k).map PolygonPacket.vertices =
    (meshTriangles k).map (triangleVertexList (targetVertices k)) := by
  exact Fin.cases (targetMeshFamily0_vertices_bound) (Fin.cases (targetMeshFamily1_vertices_bound) (Fin.cases (targetMeshFamily1_vertices_bound) (Fin.cases (targetMeshFamily1_vertices_bound) (Fin.cases (targetMeshFamily1_vertices_bound) (Fin.cases (targetMeshFamily1_vertices_bound) (Fin.cases (targetMeshFamily1_vertices_bound) (Fin.cases (targetMeshFamily1_vertices_bound) (Fin.cases (targetMeshFamily1_vertices_bound) (fun i => Fin.elim0 i)))))))))

theorem all_source_carriers_exact : ∀ k : Fin 9, familyBody (sourceFamily k) = facetBody (sourceHexFacets k) := by
  exact Fin.cases (checked_hex_cover sourceFamily0 sourceHexFacets0 sourceHexTree0 sourceFamily0_checked sourceFamily0_covered sourceFamily0_within) (Fin.cases (checked_hex_cover sourceFamily1 sourceHexFacets1 sourceHexTree1 sourceFamily1_checked sourceFamily1_covered sourceFamily1_within) (Fin.cases (checked_hex_cover sourceFamily2 sourceHexFacets2 sourceHexTree2 sourceFamily2_checked sourceFamily2_covered sourceFamily2_within) (Fin.cases (checked_hex_cover sourceFamily3 sourceHexFacets3 sourceHexTree3 sourceFamily3_checked sourceFamily3_covered sourceFamily3_within) (Fin.cases (checked_hex_cover sourceFamily4 sourceHexFacets4 sourceHexTree4 sourceFamily4_checked sourceFamily4_covered sourceFamily4_within) (Fin.cases (checked_hex_cover sourceFamily5 sourceHexFacets5 sourceHexTree5 sourceFamily5_checked sourceFamily5_covered sourceFamily5_within) (Fin.cases (checked_hex_cover sourceFamily6 sourceHexFacets6 sourceHexTree6 sourceFamily6_checked sourceFamily6_covered sourceFamily6_within) (Fin.cases (checked_hex_cover sourceFamily7 sourceHexFacets7 sourceHexTree7 sourceFamily7_checked sourceFamily7_covered sourceFamily7_within) (Fin.cases (checked_hex_cover sourceFamily8 sourceHexFacets8 sourceHexTree8 sourceFamily8_checked sourceFamily8_covered sourceFamily8_within) (fun i => Fin.elim0 i)))))))))

theorem target0_carrier_eq_closed_kites : familyBody targetMeshFamily0 = scaledClusterBody 6 .t7h := by
  calc familyBody targetMeshFamily0 = familyBody targetKiteFamily0 :=
         FamilyCover.antisymm targetMeshFamily0_checked targetKiteFamily0_checked
           target0_backward_covered target0_forward_covered
       _ = scaledClusterBody 6 .t7h :=
         familyBody_eq_scaledClusterBody targetKiteFamily0 6 .t7h targetKiteFamily0_vertices_bound

theorem target1_carrier_eq_closed_kites : familyBody targetMeshFamily1 = scaledClusterBody 6 .t8h := by
  calc familyBody targetMeshFamily1 = familyBody targetKiteFamily1 :=
         FamilyCover.antisymm targetMeshFamily1_checked targetKiteFamily1_checked
           target1_backward_covered target1_forward_covered
       _ = scaledClusterBody 6 .t8h :=
         familyBody_eq_scaledClusterBody targetKiteFamily1 6 .t8h targetKiteFamily1_vertices_bound

theorem all_target_carriers_exact : ∀ k : Fin 9, familyBody (targetFamily k) =
    scaledClusterBody 6 (SpectreClusters.ReverseExistence.clusterOfMark k) := by
  exact Fin.cases (target0_carrier_eq_closed_kites) (Fin.cases (target1_carrier_eq_closed_kites) (Fin.cases (target1_carrier_eq_closed_kites) (Fin.cases (target1_carrier_eq_closed_kites) (Fin.cases (target1_carrier_eq_closed_kites) (Fin.cases (target1_carrier_eq_closed_kites) (Fin.cases (target1_carrier_eq_closed_kites) (Fin.cases (target1_carrier_eq_closed_kites) (Fin.cases (target1_carrier_eq_closed_kites) (fun i => Fin.elim0 i)))))))))

/-- Genuine equality with the finite union of actual closed raw grid kites. -/
theorem all_normalized_target_carriers_exact (k : Fin 9) :
    (fun x : RealPoint => (1/6 : ℝ) • x) '' familyBody (targetFamily k) =
      rawClusterBody (SpectreClusters.ReverseExistence.clusterOfMark k) := by
  rw [all_target_carriers_exact,normalize_scaledClusterBody]

end
end SpectreGeometry.ReverseClusterTriangulation
