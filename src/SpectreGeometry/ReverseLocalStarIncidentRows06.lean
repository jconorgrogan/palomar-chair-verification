module

public import SpectreGeometry.ReverseLocalStarIncidentData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem incident_row_0_96 :
    96 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 96 =
      (if false then incidentRows1 else incidentRows0).getD 96 [] := by decide
theorem incident_row_0_97 :
    97 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 97 =
      (if false then incidentRows1 else incidentRows0).getD 97 [] := by decide
theorem incident_row_0_98 :
    98 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 98 =
      (if false then incidentRows1 else incidentRows0).getD 98 [] := by decide
theorem incident_row_0_99 :
    99 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 99 =
      (if false then incidentRows1 else incidentRows0).getD 99 [] := by decide
theorem incident_row_0_100 :
    100 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 100 =
      (if false then incidentRows1 else incidentRows0).getD 100 [] := by decide
theorem incident_row_0_101 :
    101 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 101 =
      (if false then incidentRows1 else incidentRows0).getD 101 [] := by decide
theorem incident_row_0_102 :
    102 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 102 =
      (if false then incidentRows1 else incidentRows0).getD 102 [] := by decide
theorem incident_row_0_103 :
    103 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 103 =
      (if false then incidentRows1 else incidentRows0).getD 103 [] := by decide
theorem incident_row_0_104 :
    104 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 104 =
      (if false then incidentRows1 else incidentRows0).getD 104 [] := by decide
theorem incident_row_0_105 :
    105 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 105 =
      (if false then incidentRows1 else incidentRows0).getD 105 [] := by decide
theorem incident_row_0_106 :
    106 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 106 =
      (if false then incidentRows1 else incidentRows0).getD 106 [] := by decide
theorem incident_row_0_107 :
    107 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 107 =
      (if false then incidentRows1 else incidentRows0).getD 107 [] := by decide
theorem incident_row_0_108 :
    108 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 108 =
      (if false then incidentRows1 else incidentRows0).getD 108 [] := by decide
theorem incident_row_0_109 :
    109 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 109 =
      (if false then incidentRows1 else incidentRows0).getD 109 [] := by decide
theorem incident_row_0_110 :
    110 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 110 =
      (if false then incidentRows1 else incidentRows0).getD 110 [] := by decide
theorem incident_row_0_111 :
    111 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 111 =
      (if false then incidentRows1 else incidentRows0).getD 111 [] := by decide
theorem incident_rows_0_6 : ∀ j : Fin 16,
    96+j.val < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false (96+j.val) =
      (if false then incidentRows1 else incidentRows0).getD (96+j.val) [] := by
  exact Fin.cases incident_row_0_96 (Fin.cases incident_row_0_97 (Fin.cases incident_row_0_98 (Fin.cases incident_row_0_99 (Fin.cases incident_row_0_100 (Fin.cases incident_row_0_101 (Fin.cases incident_row_0_102 (Fin.cases incident_row_0_103 (Fin.cases incident_row_0_104 (Fin.cases incident_row_0_105 (Fin.cases incident_row_0_106 (Fin.cases incident_row_0_107 (Fin.cases incident_row_0_108 (Fin.cases incident_row_0_109 (Fin.cases incident_row_0_110 (Fin.cases incident_row_0_111 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
