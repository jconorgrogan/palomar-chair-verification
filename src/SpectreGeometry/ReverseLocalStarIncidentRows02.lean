module

public import SpectreGeometry.ReverseLocalStarIncidentData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem incident_row_0_32 :
    32 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 32 =
      (if false then incidentRows1 else incidentRows0).getD 32 [] := by decide
theorem incident_row_0_33 :
    33 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 33 =
      (if false then incidentRows1 else incidentRows0).getD 33 [] := by decide
theorem incident_row_0_34 :
    34 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 34 =
      (if false then incidentRows1 else incidentRows0).getD 34 [] := by decide
theorem incident_row_0_35 :
    35 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 35 =
      (if false then incidentRows1 else incidentRows0).getD 35 [] := by decide
theorem incident_row_0_36 :
    36 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 36 =
      (if false then incidentRows1 else incidentRows0).getD 36 [] := by decide
theorem incident_row_0_37 :
    37 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 37 =
      (if false then incidentRows1 else incidentRows0).getD 37 [] := by decide
theorem incident_row_0_38 :
    38 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 38 =
      (if false then incidentRows1 else incidentRows0).getD 38 [] := by decide
theorem incident_row_0_39 :
    39 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 39 =
      (if false then incidentRows1 else incidentRows0).getD 39 [] := by decide
theorem incident_row_0_40 :
    40 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 40 =
      (if false then incidentRows1 else incidentRows0).getD 40 [] := by decide
theorem incident_row_0_41 :
    41 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 41 =
      (if false then incidentRows1 else incidentRows0).getD 41 [] := by decide
theorem incident_row_0_42 :
    42 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 42 =
      (if false then incidentRows1 else incidentRows0).getD 42 [] := by decide
theorem incident_row_0_43 :
    43 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 43 =
      (if false then incidentRows1 else incidentRows0).getD 43 [] := by decide
theorem incident_row_0_44 :
    44 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 44 =
      (if false then incidentRows1 else incidentRows0).getD 44 [] := by decide
theorem incident_row_0_45 :
    45 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 45 =
      (if false then incidentRows1 else incidentRows0).getD 45 [] := by decide
theorem incident_row_0_46 :
    46 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 46 =
      (if false then incidentRows1 else incidentRows0).getD 46 [] := by decide
theorem incident_row_0_47 :
    47 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 47 =
      (if false then incidentRows1 else incidentRows0).getD 47 [] := by decide
theorem incident_rows_0_2 : ∀ j : Fin 16,
    32+j.val < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false (32+j.val) =
      (if false then incidentRows1 else incidentRows0).getD (32+j.val) [] := by
  exact Fin.cases incident_row_0_32 (Fin.cases incident_row_0_33 (Fin.cases incident_row_0_34 (Fin.cases incident_row_0_35 (Fin.cases incident_row_0_36 (Fin.cases incident_row_0_37 (Fin.cases incident_row_0_38 (Fin.cases incident_row_0_39 (Fin.cases incident_row_0_40 (Fin.cases incident_row_0_41 (Fin.cases incident_row_0_42 (Fin.cases incident_row_0_43 (Fin.cases incident_row_0_44 (Fin.cases incident_row_0_45 (Fin.cases incident_row_0_46 (Fin.cases incident_row_0_47 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
