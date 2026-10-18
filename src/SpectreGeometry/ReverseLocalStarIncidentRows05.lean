module

public import SpectreGeometry.ReverseLocalStarIncidentData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem incident_row_0_80 :
    80 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 80 =
      (if false then incidentRows1 else incidentRows0).getD 80 [] := by decide
theorem incident_row_0_81 :
    81 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 81 =
      (if false then incidentRows1 else incidentRows0).getD 81 [] := by decide
theorem incident_row_0_82 :
    82 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 82 =
      (if false then incidentRows1 else incidentRows0).getD 82 [] := by decide
theorem incident_row_0_83 :
    83 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 83 =
      (if false then incidentRows1 else incidentRows0).getD 83 [] := by decide
theorem incident_row_0_84 :
    84 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 84 =
      (if false then incidentRows1 else incidentRows0).getD 84 [] := by decide
theorem incident_row_0_85 :
    85 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 85 =
      (if false then incidentRows1 else incidentRows0).getD 85 [] := by decide
theorem incident_row_0_86 :
    86 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 86 =
      (if false then incidentRows1 else incidentRows0).getD 86 [] := by decide
theorem incident_row_0_87 :
    87 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 87 =
      (if false then incidentRows1 else incidentRows0).getD 87 [] := by decide
theorem incident_row_0_88 :
    88 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 88 =
      (if false then incidentRows1 else incidentRows0).getD 88 [] := by decide
theorem incident_row_0_89 :
    89 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 89 =
      (if false then incidentRows1 else incidentRows0).getD 89 [] := by decide
theorem incident_row_0_90 :
    90 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 90 =
      (if false then incidentRows1 else incidentRows0).getD 90 [] := by decide
theorem incident_row_0_91 :
    91 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 91 =
      (if false then incidentRows1 else incidentRows0).getD 91 [] := by decide
theorem incident_row_0_92 :
    92 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 92 =
      (if false then incidentRows1 else incidentRows0).getD 92 [] := by decide
theorem incident_row_0_93 :
    93 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 93 =
      (if false then incidentRows1 else incidentRows0).getD 93 [] := by decide
theorem incident_row_0_94 :
    94 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 94 =
      (if false then incidentRows1 else incidentRows0).getD 94 [] := by decide
theorem incident_row_0_95 :
    95 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 95 =
      (if false then incidentRows1 else incidentRows0).getD 95 [] := by decide
theorem incident_rows_0_5 : ∀ j : Fin 16,
    80+j.val < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false (80+j.val) =
      (if false then incidentRows1 else incidentRows0).getD (80+j.val) [] := by
  exact Fin.cases incident_row_0_80 (Fin.cases incident_row_0_81 (Fin.cases incident_row_0_82 (Fin.cases incident_row_0_83 (Fin.cases incident_row_0_84 (Fin.cases incident_row_0_85 (Fin.cases incident_row_0_86 (Fin.cases incident_row_0_87 (Fin.cases incident_row_0_88 (Fin.cases incident_row_0_89 (Fin.cases incident_row_0_90 (Fin.cases incident_row_0_91 (Fin.cases incident_row_0_92 (Fin.cases incident_row_0_93 (Fin.cases incident_row_0_94 (Fin.cases incident_row_0_95 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
