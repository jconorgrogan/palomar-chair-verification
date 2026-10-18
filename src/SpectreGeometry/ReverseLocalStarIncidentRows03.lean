module

public import SpectreGeometry.ReverseLocalStarIncidentData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem incident_row_0_48 :
    48 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 48 =
      (if false then incidentRows1 else incidentRows0).getD 48 [] := by decide
theorem incident_row_0_49 :
    49 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 49 =
      (if false then incidentRows1 else incidentRows0).getD 49 [] := by decide
theorem incident_row_0_50 :
    50 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 50 =
      (if false then incidentRows1 else incidentRows0).getD 50 [] := by decide
theorem incident_row_0_51 :
    51 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 51 =
      (if false then incidentRows1 else incidentRows0).getD 51 [] := by decide
theorem incident_row_0_52 :
    52 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 52 =
      (if false then incidentRows1 else incidentRows0).getD 52 [] := by decide
theorem incident_row_0_53 :
    53 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 53 =
      (if false then incidentRows1 else incidentRows0).getD 53 [] := by decide
theorem incident_row_0_54 :
    54 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 54 =
      (if false then incidentRows1 else incidentRows0).getD 54 [] := by decide
theorem incident_row_0_55 :
    55 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 55 =
      (if false then incidentRows1 else incidentRows0).getD 55 [] := by decide
theorem incident_row_0_56 :
    56 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 56 =
      (if false then incidentRows1 else incidentRows0).getD 56 [] := by decide
theorem incident_row_0_57 :
    57 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 57 =
      (if false then incidentRows1 else incidentRows0).getD 57 [] := by decide
theorem incident_row_0_58 :
    58 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 58 =
      (if false then incidentRows1 else incidentRows0).getD 58 [] := by decide
theorem incident_row_0_59 :
    59 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 59 =
      (if false then incidentRows1 else incidentRows0).getD 59 [] := by decide
theorem incident_row_0_60 :
    60 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 60 =
      (if false then incidentRows1 else incidentRows0).getD 60 [] := by decide
theorem incident_row_0_61 :
    61 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 61 =
      (if false then incidentRows1 else incidentRows0).getD 61 [] := by decide
theorem incident_row_0_62 :
    62 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 62 =
      (if false then incidentRows1 else incidentRows0).getD 62 [] := by decide
theorem incident_row_0_63 :
    63 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 63 =
      (if false then incidentRows1 else incidentRows0).getD 63 [] := by decide
theorem incident_rows_0_3 : ∀ j : Fin 16,
    48+j.val < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false (48+j.val) =
      (if false then incidentRows1 else incidentRows0).getD (48+j.val) [] := by
  exact Fin.cases incident_row_0_48 (Fin.cases incident_row_0_49 (Fin.cases incident_row_0_50 (Fin.cases incident_row_0_51 (Fin.cases incident_row_0_52 (Fin.cases incident_row_0_53 (Fin.cases incident_row_0_54 (Fin.cases incident_row_0_55 (Fin.cases incident_row_0_56 (Fin.cases incident_row_0_57 (Fin.cases incident_row_0_58 (Fin.cases incident_row_0_59 (Fin.cases incident_row_0_60 (Fin.cases incident_row_0_61 (Fin.cases incident_row_0_62 (Fin.cases incident_row_0_63 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
