module

public import SpectreGeometry.ReverseLocalStarIncidentData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem incident_row_1_48 :
    48 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 48 =
      (if true then incidentRows1 else incidentRows0).getD 48 [] := by decide
theorem incident_row_1_49 :
    49 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 49 =
      (if true then incidentRows1 else incidentRows0).getD 49 [] := by decide
theorem incident_row_1_50 :
    50 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 50 =
      (if true then incidentRows1 else incidentRows0).getD 50 [] := by decide
theorem incident_row_1_51 :
    51 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 51 =
      (if true then incidentRows1 else incidentRows0).getD 51 [] := by decide
theorem incident_row_1_52 :
    52 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 52 =
      (if true then incidentRows1 else incidentRows0).getD 52 [] := by decide
theorem incident_row_1_53 :
    53 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 53 =
      (if true then incidentRows1 else incidentRows0).getD 53 [] := by decide
theorem incident_row_1_54 :
    54 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 54 =
      (if true then incidentRows1 else incidentRows0).getD 54 [] := by decide
theorem incident_row_1_55 :
    55 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 55 =
      (if true then incidentRows1 else incidentRows0).getD 55 [] := by decide
theorem incident_row_1_56 :
    56 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 56 =
      (if true then incidentRows1 else incidentRows0).getD 56 [] := by decide
theorem incident_row_1_57 :
    57 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 57 =
      (if true then incidentRows1 else incidentRows0).getD 57 [] := by decide
theorem incident_row_1_58 :
    58 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 58 =
      (if true then incidentRows1 else incidentRows0).getD 58 [] := by decide
theorem incident_row_1_59 :
    59 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 59 =
      (if true then incidentRows1 else incidentRows0).getD 59 [] := by decide
theorem incident_row_1_60 :
    60 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 60 =
      (if true then incidentRows1 else incidentRows0).getD 60 [] := by decide
theorem incident_row_1_61 :
    61 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 61 =
      (if true then incidentRows1 else incidentRows0).getD 61 [] := by decide
theorem incident_row_1_62 :
    62 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 62 =
      (if true then incidentRows1 else incidentRows0).getD 62 [] := by decide
theorem incident_row_1_63 :
    63 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 63 =
      (if true then incidentRows1 else incidentRows0).getD 63 [] := by decide
theorem incident_rows_1_3 : ∀ j : Fin 16,
    48+j.val < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true (48+j.val) =
      (if true then incidentRows1 else incidentRows0).getD (48+j.val) [] := by
  exact Fin.cases incident_row_1_48 (Fin.cases incident_row_1_49 (Fin.cases incident_row_1_50 (Fin.cases incident_row_1_51 (Fin.cases incident_row_1_52 (Fin.cases incident_row_1_53 (Fin.cases incident_row_1_54 (Fin.cases incident_row_1_55 (Fin.cases incident_row_1_56 (Fin.cases incident_row_1_57 (Fin.cases incident_row_1_58 (Fin.cases incident_row_1_59 (Fin.cases incident_row_1_60 (Fin.cases incident_row_1_61 (Fin.cases incident_row_1_62 (Fin.cases incident_row_1_63 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
