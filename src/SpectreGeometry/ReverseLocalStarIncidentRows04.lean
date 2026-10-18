module

public import SpectreGeometry.ReverseLocalStarIncidentData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem incident_row_0_64 :
    64 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 64 =
      (if false then incidentRows1 else incidentRows0).getD 64 [] := by decide
theorem incident_row_0_65 :
    65 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 65 =
      (if false then incidentRows1 else incidentRows0).getD 65 [] := by decide
theorem incident_row_0_66 :
    66 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 66 =
      (if false then incidentRows1 else incidentRows0).getD 66 [] := by decide
theorem incident_row_0_67 :
    67 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 67 =
      (if false then incidentRows1 else incidentRows0).getD 67 [] := by decide
theorem incident_row_0_68 :
    68 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 68 =
      (if false then incidentRows1 else incidentRows0).getD 68 [] := by decide
theorem incident_row_0_69 :
    69 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 69 =
      (if false then incidentRows1 else incidentRows0).getD 69 [] := by decide
theorem incident_row_0_70 :
    70 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 70 =
      (if false then incidentRows1 else incidentRows0).getD 70 [] := by decide
theorem incident_row_0_71 :
    71 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 71 =
      (if false then incidentRows1 else incidentRows0).getD 71 [] := by decide
theorem incident_row_0_72 :
    72 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 72 =
      (if false then incidentRows1 else incidentRows0).getD 72 [] := by decide
theorem incident_row_0_73 :
    73 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 73 =
      (if false then incidentRows1 else incidentRows0).getD 73 [] := by decide
theorem incident_row_0_74 :
    74 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 74 =
      (if false then incidentRows1 else incidentRows0).getD 74 [] := by decide
theorem incident_row_0_75 :
    75 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 75 =
      (if false then incidentRows1 else incidentRows0).getD 75 [] := by decide
theorem incident_row_0_76 :
    76 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 76 =
      (if false then incidentRows1 else incidentRows0).getD 76 [] := by decide
theorem incident_row_0_77 :
    77 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 77 =
      (if false then incidentRows1 else incidentRows0).getD 77 [] := by decide
theorem incident_row_0_78 :
    78 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 78 =
      (if false then incidentRows1 else incidentRows0).getD 78 [] := by decide
theorem incident_row_0_79 :
    79 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 79 =
      (if false then incidentRows1 else incidentRows0).getD 79 [] := by decide
theorem incident_rows_0_4 : ∀ j : Fin 16,
    64+j.val < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false (64+j.val) =
      (if false then incidentRows1 else incidentRows0).getD (64+j.val) [] := by
  exact Fin.cases incident_row_0_64 (Fin.cases incident_row_0_65 (Fin.cases incident_row_0_66 (Fin.cases incident_row_0_67 (Fin.cases incident_row_0_68 (Fin.cases incident_row_0_69 (Fin.cases incident_row_0_70 (Fin.cases incident_row_0_71 (Fin.cases incident_row_0_72 (Fin.cases incident_row_0_73 (Fin.cases incident_row_0_74 (Fin.cases incident_row_0_75 (Fin.cases incident_row_0_76 (Fin.cases incident_row_0_77 (Fin.cases incident_row_0_78 (Fin.cases incident_row_0_79 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
