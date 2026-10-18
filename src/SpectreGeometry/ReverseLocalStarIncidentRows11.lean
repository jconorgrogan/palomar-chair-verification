module

public import SpectreGeometry.ReverseLocalStarIncidentData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem incident_row_1_16 :
    16 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 16 =
      (if true then incidentRows1 else incidentRows0).getD 16 [] := by decide
theorem incident_row_1_17 :
    17 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 17 =
      (if true then incidentRows1 else incidentRows0).getD 17 [] := by decide
theorem incident_row_1_18 :
    18 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 18 =
      (if true then incidentRows1 else incidentRows0).getD 18 [] := by decide
theorem incident_row_1_19 :
    19 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 19 =
      (if true then incidentRows1 else incidentRows0).getD 19 [] := by decide
theorem incident_row_1_20 :
    20 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 20 =
      (if true then incidentRows1 else incidentRows0).getD 20 [] := by decide
theorem incident_row_1_21 :
    21 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 21 =
      (if true then incidentRows1 else incidentRows0).getD 21 [] := by decide
theorem incident_row_1_22 :
    22 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 22 =
      (if true then incidentRows1 else incidentRows0).getD 22 [] := by decide
theorem incident_row_1_23 :
    23 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 23 =
      (if true then incidentRows1 else incidentRows0).getD 23 [] := by decide
theorem incident_row_1_24 :
    24 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 24 =
      (if true then incidentRows1 else incidentRows0).getD 24 [] := by decide
theorem incident_row_1_25 :
    25 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 25 =
      (if true then incidentRows1 else incidentRows0).getD 25 [] := by decide
theorem incident_row_1_26 :
    26 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 26 =
      (if true then incidentRows1 else incidentRows0).getD 26 [] := by decide
theorem incident_row_1_27 :
    27 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 27 =
      (if true then incidentRows1 else incidentRows0).getD 27 [] := by decide
theorem incident_row_1_28 :
    28 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 28 =
      (if true then incidentRows1 else incidentRows0).getD 28 [] := by decide
theorem incident_row_1_29 :
    29 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 29 =
      (if true then incidentRows1 else incidentRows0).getD 29 [] := by decide
theorem incident_row_1_30 :
    30 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 30 =
      (if true then incidentRows1 else incidentRows0).getD 30 [] := by decide
theorem incident_row_1_31 :
    31 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 31 =
      (if true then incidentRows1 else incidentRows0).getD 31 [] := by decide
theorem incident_rows_1_1 : ∀ j : Fin 16,
    16+j.val < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true (16+j.val) =
      (if true then incidentRows1 else incidentRows0).getD (16+j.val) [] := by
  exact Fin.cases incident_row_1_16 (Fin.cases incident_row_1_17 (Fin.cases incident_row_1_18 (Fin.cases incident_row_1_19 (Fin.cases incident_row_1_20 (Fin.cases incident_row_1_21 (Fin.cases incident_row_1_22 (Fin.cases incident_row_1_23 (Fin.cases incident_row_1_24 (Fin.cases incident_row_1_25 (Fin.cases incident_row_1_26 (Fin.cases incident_row_1_27 (Fin.cases incident_row_1_28 (Fin.cases incident_row_1_29 (Fin.cases incident_row_1_30 (Fin.cases incident_row_1_31 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
