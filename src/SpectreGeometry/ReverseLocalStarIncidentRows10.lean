module

public import SpectreGeometry.ReverseLocalStarIncidentData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem incident_row_1_0 :
    0 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 0 =
      (if true then incidentRows1 else incidentRows0).getD 0 [] := by decide
theorem incident_row_1_1 :
    1 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 1 =
      (if true then incidentRows1 else incidentRows0).getD 1 [] := by decide
theorem incident_row_1_2 :
    2 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 2 =
      (if true then incidentRows1 else incidentRows0).getD 2 [] := by decide
theorem incident_row_1_3 :
    3 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 3 =
      (if true then incidentRows1 else incidentRows0).getD 3 [] := by decide
theorem incident_row_1_4 :
    4 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 4 =
      (if true then incidentRows1 else incidentRows0).getD 4 [] := by decide
theorem incident_row_1_5 :
    5 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 5 =
      (if true then incidentRows1 else incidentRows0).getD 5 [] := by decide
theorem incident_row_1_6 :
    6 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 6 =
      (if true then incidentRows1 else incidentRows0).getD 6 [] := by decide
theorem incident_row_1_7 :
    7 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 7 =
      (if true then incidentRows1 else incidentRows0).getD 7 [] := by decide
theorem incident_row_1_8 :
    8 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 8 =
      (if true then incidentRows1 else incidentRows0).getD 8 [] := by decide
theorem incident_row_1_9 :
    9 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 9 =
      (if true then incidentRows1 else incidentRows0).getD 9 [] := by decide
theorem incident_row_1_10 :
    10 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 10 =
      (if true then incidentRows1 else incidentRows0).getD 10 [] := by decide
theorem incident_row_1_11 :
    11 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 11 =
      (if true then incidentRows1 else incidentRows0).getD 11 [] := by decide
theorem incident_row_1_12 :
    12 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 12 =
      (if true then incidentRows1 else incidentRows0).getD 12 [] := by decide
theorem incident_row_1_13 :
    13 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 13 =
      (if true then incidentRows1 else incidentRows0).getD 13 [] := by decide
theorem incident_row_1_14 :
    14 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 14 =
      (if true then incidentRows1 else incidentRows0).getD 14 [] := by decide
theorem incident_row_1_15 :
    15 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 15 =
      (if true then incidentRows1 else incidentRows0).getD 15 [] := by decide
theorem incident_rows_1_0 : ∀ j : Fin 16,
    0+j.val < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true (0+j.val) =
      (if true then incidentRows1 else incidentRows0).getD (0+j.val) [] := by
  exact Fin.cases incident_row_1_0 (Fin.cases incident_row_1_1 (Fin.cases incident_row_1_2 (Fin.cases incident_row_1_3 (Fin.cases incident_row_1_4 (Fin.cases incident_row_1_5 (Fin.cases incident_row_1_6 (Fin.cases incident_row_1_7 (Fin.cases incident_row_1_8 (Fin.cases incident_row_1_9 (Fin.cases incident_row_1_10 (Fin.cases incident_row_1_11 (Fin.cases incident_row_1_12 (Fin.cases incident_row_1_13 (Fin.cases incident_row_1_14 (Fin.cases incident_row_1_15 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
