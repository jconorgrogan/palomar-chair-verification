module

public import SpectreGeometry.ReverseLocalStarIncidentData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem incident_row_0_16 :
    16 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 16 =
      (if false then incidentRows1 else incidentRows0).getD 16 [] := by decide
theorem incident_row_0_17 :
    17 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 17 =
      (if false then incidentRows1 else incidentRows0).getD 17 [] := by decide
theorem incident_row_0_18 :
    18 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 18 =
      (if false then incidentRows1 else incidentRows0).getD 18 [] := by decide
theorem incident_row_0_19 :
    19 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 19 =
      (if false then incidentRows1 else incidentRows0).getD 19 [] := by decide
theorem incident_row_0_20 :
    20 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 20 =
      (if false then incidentRows1 else incidentRows0).getD 20 [] := by decide
theorem incident_row_0_21 :
    21 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 21 =
      (if false then incidentRows1 else incidentRows0).getD 21 [] := by decide
theorem incident_row_0_22 :
    22 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 22 =
      (if false then incidentRows1 else incidentRows0).getD 22 [] := by decide
theorem incident_row_0_23 :
    23 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 23 =
      (if false then incidentRows1 else incidentRows0).getD 23 [] := by decide
theorem incident_row_0_24 :
    24 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 24 =
      (if false then incidentRows1 else incidentRows0).getD 24 [] := by decide
theorem incident_row_0_25 :
    25 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 25 =
      (if false then incidentRows1 else incidentRows0).getD 25 [] := by decide
theorem incident_row_0_26 :
    26 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 26 =
      (if false then incidentRows1 else incidentRows0).getD 26 [] := by decide
theorem incident_row_0_27 :
    27 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 27 =
      (if false then incidentRows1 else incidentRows0).getD 27 [] := by decide
theorem incident_row_0_28 :
    28 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 28 =
      (if false then incidentRows1 else incidentRows0).getD 28 [] := by decide
theorem incident_row_0_29 :
    29 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 29 =
      (if false then incidentRows1 else incidentRows0).getD 29 [] := by decide
theorem incident_row_0_30 :
    30 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 30 =
      (if false then incidentRows1 else incidentRows0).getD 30 [] := by decide
theorem incident_row_0_31 :
    31 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 31 =
      (if false then incidentRows1 else incidentRows0).getD 31 [] := by decide
theorem incident_rows_0_1 : ∀ j : Fin 16,
    16+j.val < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false (16+j.val) =
      (if false then incidentRows1 else incidentRows0).getD (16+j.val) [] := by
  exact Fin.cases incident_row_0_16 (Fin.cases incident_row_0_17 (Fin.cases incident_row_0_18 (Fin.cases incident_row_0_19 (Fin.cases incident_row_0_20 (Fin.cases incident_row_0_21 (Fin.cases incident_row_0_22 (Fin.cases incident_row_0_23 (Fin.cases incident_row_0_24 (Fin.cases incident_row_0_25 (Fin.cases incident_row_0_26 (Fin.cases incident_row_0_27 (Fin.cases incident_row_0_28 (Fin.cases incident_row_0_29 (Fin.cases incident_row_0_30 (Fin.cases incident_row_0_31 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
