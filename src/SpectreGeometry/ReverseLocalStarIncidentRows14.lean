module

public import SpectreGeometry.ReverseLocalStarIncidentData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem incident_row_1_64 :
    64 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 64 =
      (if true then incidentRows1 else incidentRows0).getD 64 [] := by decide
theorem incident_row_1_65 :
    65 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 65 =
      (if true then incidentRows1 else incidentRows0).getD 65 [] := by decide
theorem incident_row_1_66 :
    66 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 66 =
      (if true then incidentRows1 else incidentRows0).getD 66 [] := by decide
theorem incident_row_1_67 :
    67 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 67 =
      (if true then incidentRows1 else incidentRows0).getD 67 [] := by decide
theorem incident_row_1_68 :
    68 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 68 =
      (if true then incidentRows1 else incidentRows0).getD 68 [] := by decide
theorem incident_row_1_69 :
    69 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 69 =
      (if true then incidentRows1 else incidentRows0).getD 69 [] := by decide
theorem incident_row_1_70 :
    70 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 70 =
      (if true then incidentRows1 else incidentRows0).getD 70 [] := by decide
theorem incident_row_1_71 :
    71 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 71 =
      (if true then incidentRows1 else incidentRows0).getD 71 [] := by decide
theorem incident_row_1_72 :
    72 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 72 =
      (if true then incidentRows1 else incidentRows0).getD 72 [] := by decide
theorem incident_row_1_73 :
    73 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 73 =
      (if true then incidentRows1 else incidentRows0).getD 73 [] := by decide
theorem incident_row_1_74 :
    74 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 74 =
      (if true then incidentRows1 else incidentRows0).getD 74 [] := by decide
theorem incident_row_1_75 :
    75 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 75 =
      (if true then incidentRows1 else incidentRows0).getD 75 [] := by decide
theorem incident_row_1_76 :
    76 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 76 =
      (if true then incidentRows1 else incidentRows0).getD 76 [] := by decide
theorem incident_row_1_77 :
    77 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 77 =
      (if true then incidentRows1 else incidentRows0).getD 77 [] := by decide
theorem incident_row_1_78 :
    78 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 78 =
      (if true then incidentRows1 else incidentRows0).getD 78 [] := by decide
theorem incident_row_1_79 :
    79 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 79 =
      (if true then incidentRows1 else incidentRows0).getD 79 [] := by decide
theorem incident_rows_1_4 : ∀ j : Fin 16,
    64+j.val < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true (64+j.val) =
      (if true then incidentRows1 else incidentRows0).getD (64+j.val) [] := by
  exact Fin.cases incident_row_1_64 (Fin.cases incident_row_1_65 (Fin.cases incident_row_1_66 (Fin.cases incident_row_1_67 (Fin.cases incident_row_1_68 (Fin.cases incident_row_1_69 (Fin.cases incident_row_1_70 (Fin.cases incident_row_1_71 (Fin.cases incident_row_1_72 (Fin.cases incident_row_1_73 (Fin.cases incident_row_1_74 (Fin.cases incident_row_1_75 (Fin.cases incident_row_1_76 (Fin.cases incident_row_1_77 (Fin.cases incident_row_1_78 (Fin.cases incident_row_1_79 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
