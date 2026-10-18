module

public import SpectreGeometry.ReverseLocalStarIncidentData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem incident_row_1_32 :
    32 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 32 =
      (if true then incidentRows1 else incidentRows0).getD 32 [] := by decide
theorem incident_row_1_33 :
    33 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 33 =
      (if true then incidentRows1 else incidentRows0).getD 33 [] := by decide
theorem incident_row_1_34 :
    34 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 34 =
      (if true then incidentRows1 else incidentRows0).getD 34 [] := by decide
theorem incident_row_1_35 :
    35 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 35 =
      (if true then incidentRows1 else incidentRows0).getD 35 [] := by decide
theorem incident_row_1_36 :
    36 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 36 =
      (if true then incidentRows1 else incidentRows0).getD 36 [] := by decide
theorem incident_row_1_37 :
    37 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 37 =
      (if true then incidentRows1 else incidentRows0).getD 37 [] := by decide
theorem incident_row_1_38 :
    38 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 38 =
      (if true then incidentRows1 else incidentRows0).getD 38 [] := by decide
theorem incident_row_1_39 :
    39 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 39 =
      (if true then incidentRows1 else incidentRows0).getD 39 [] := by decide
theorem incident_row_1_40 :
    40 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 40 =
      (if true then incidentRows1 else incidentRows0).getD 40 [] := by decide
theorem incident_row_1_41 :
    41 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 41 =
      (if true then incidentRows1 else incidentRows0).getD 41 [] := by decide
theorem incident_row_1_42 :
    42 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 42 =
      (if true then incidentRows1 else incidentRows0).getD 42 [] := by decide
theorem incident_row_1_43 :
    43 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 43 =
      (if true then incidentRows1 else incidentRows0).getD 43 [] := by decide
theorem incident_row_1_44 :
    44 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 44 =
      (if true then incidentRows1 else incidentRows0).getD 44 [] := by decide
theorem incident_row_1_45 :
    45 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 45 =
      (if true then incidentRows1 else incidentRows0).getD 45 [] := by decide
theorem incident_row_1_46 :
    46 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 46 =
      (if true then incidentRows1 else incidentRows0).getD 46 [] := by decide
theorem incident_row_1_47 :
    47 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 47 =
      (if true then incidentRows1 else incidentRows0).getD 47 [] := by decide
theorem incident_rows_1_2 : ∀ j : Fin 16,
    32+j.val < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true (32+j.val) =
      (if true then incidentRows1 else incidentRows0).getD (32+j.val) [] := by
  exact Fin.cases incident_row_1_32 (Fin.cases incident_row_1_33 (Fin.cases incident_row_1_34 (Fin.cases incident_row_1_35 (Fin.cases incident_row_1_36 (Fin.cases incident_row_1_37 (Fin.cases incident_row_1_38 (Fin.cases incident_row_1_39 (Fin.cases incident_row_1_40 (Fin.cases incident_row_1_41 (Fin.cases incident_row_1_42 (Fin.cases incident_row_1_43 (Fin.cases incident_row_1_44 (Fin.cases incident_row_1_45 (Fin.cases incident_row_1_46 (Fin.cases incident_row_1_47 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
