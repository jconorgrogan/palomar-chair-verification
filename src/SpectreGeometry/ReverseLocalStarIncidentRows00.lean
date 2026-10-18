module

public import SpectreGeometry.ReverseLocalStarIncidentData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem incident_row_0_0 :
    0 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 0 =
      (if false then incidentRows1 else incidentRows0).getD 0 [] := by decide
theorem incident_row_0_1 :
    1 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 1 =
      (if false then incidentRows1 else incidentRows0).getD 1 [] := by decide
theorem incident_row_0_2 :
    2 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 2 =
      (if false then incidentRows1 else incidentRows0).getD 2 [] := by decide
theorem incident_row_0_3 :
    3 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 3 =
      (if false then incidentRows1 else incidentRows0).getD 3 [] := by decide
theorem incident_row_0_4 :
    4 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 4 =
      (if false then incidentRows1 else incidentRows0).getD 4 [] := by decide
theorem incident_row_0_5 :
    5 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 5 =
      (if false then incidentRows1 else incidentRows0).getD 5 [] := by decide
theorem incident_row_0_6 :
    6 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 6 =
      (if false then incidentRows1 else incidentRows0).getD 6 [] := by decide
theorem incident_row_0_7 :
    7 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 7 =
      (if false then incidentRows1 else incidentRows0).getD 7 [] := by decide
theorem incident_row_0_8 :
    8 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 8 =
      (if false then incidentRows1 else incidentRows0).getD 8 [] := by decide
theorem incident_row_0_9 :
    9 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 9 =
      (if false then incidentRows1 else incidentRows0).getD 9 [] := by decide
theorem incident_row_0_10 :
    10 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 10 =
      (if false then incidentRows1 else incidentRows0).getD 10 [] := by decide
theorem incident_row_0_11 :
    11 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 11 =
      (if false then incidentRows1 else incidentRows0).getD 11 [] := by decide
theorem incident_row_0_12 :
    12 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 12 =
      (if false then incidentRows1 else incidentRows0).getD 12 [] := by decide
theorem incident_row_0_13 :
    13 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 13 =
      (if false then incidentRows1 else incidentRows0).getD 13 [] := by decide
theorem incident_row_0_14 :
    14 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 14 =
      (if false then incidentRows1 else incidentRows0).getD 14 [] := by decide
theorem incident_row_0_15 :
    15 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 15 =
      (if false then incidentRows1 else incidentRows0).getD 15 [] := by decide
theorem incident_rows_0_0 : ∀ j : Fin 16,
    0+j.val < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false (0+j.val) =
      (if false then incidentRows1 else incidentRows0).getD (0+j.val) [] := by
  exact Fin.cases incident_row_0_0 (Fin.cases incident_row_0_1 (Fin.cases incident_row_0_2 (Fin.cases incident_row_0_3 (Fin.cases incident_row_0_4 (Fin.cases incident_row_0_5 (Fin.cases incident_row_0_6 (Fin.cases incident_row_0_7 (Fin.cases incident_row_0_8 (Fin.cases incident_row_0_9 (Fin.cases incident_row_0_10 (Fin.cases incident_row_0_11 (Fin.cases incident_row_0_12 (Fin.cases incident_row_0_13 (Fin.cases incident_row_0_14 (Fin.cases incident_row_0_15 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
