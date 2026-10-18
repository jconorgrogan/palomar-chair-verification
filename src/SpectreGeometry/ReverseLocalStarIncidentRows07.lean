module

public import SpectreGeometry.ReverseLocalStarIncidentData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem incident_row_0_112 :
    112 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 112 =
      (if false then incidentRows1 else incidentRows0).getD 112 [] := by decide
theorem incident_row_0_113 :
    113 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 113 =
      (if false then incidentRows1 else incidentRows0).getD 113 [] := by decide
theorem incident_row_0_114 :
    114 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 114 =
      (if false then incidentRows1 else incidentRows0).getD 114 [] := by decide
theorem incident_row_0_115 :
    115 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 115 =
      (if false then incidentRows1 else incidentRows0).getD 115 [] := by decide
theorem incident_row_0_116 :
    116 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 116 =
      (if false then incidentRows1 else incidentRows0).getD 116 [] := by decide
theorem incident_row_0_117 :
    117 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 117 =
      (if false then incidentRows1 else incidentRows0).getD 117 [] := by decide
theorem incident_row_0_118 :
    118 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 118 =
      (if false then incidentRows1 else incidentRows0).getD 118 [] := by decide
theorem incident_row_0_119 :
    119 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 119 =
      (if false then incidentRows1 else incidentRows0).getD 119 [] := by decide
theorem incident_row_0_120 :
    120 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 120 =
      (if false then incidentRows1 else incidentRows0).getD 120 [] := by decide
theorem incident_row_0_121 :
    121 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 121 =
      (if false then incidentRows1 else incidentRows0).getD 121 [] := by decide
theorem incident_row_0_122 :
    122 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 122 =
      (if false then incidentRows1 else incidentRows0).getD 122 [] := by decide
theorem incident_row_0_123 :
    123 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 123 =
      (if false then incidentRows1 else incidentRows0).getD 123 [] := by decide
theorem incident_row_0_124 :
    124 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 124 =
      (if false then incidentRows1 else incidentRows0).getD 124 [] := by decide
theorem incident_row_0_125 :
    125 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 125 =
      (if false then incidentRows1 else incidentRows0).getD 125 [] := by decide
theorem incident_row_0_126 :
    126 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 126 =
      (if false then incidentRows1 else incidentRows0).getD 126 [] := by decide
theorem incident_row_0_127 :
    127 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false 127 =
      (if false then incidentRows1 else incidentRows0).getD 127 [] := by decide
theorem incident_rows_0_7 : ∀ j : Fin 16,
    112+j.val < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark false)).length →
    calculatedIncidentRow false (112+j.val) =
      (if false then incidentRows1 else incidentRows0).getD (112+j.val) [] := by
  exact Fin.cases incident_row_0_112 (Fin.cases incident_row_0_113 (Fin.cases incident_row_0_114 (Fin.cases incident_row_0_115 (Fin.cases incident_row_0_116 (Fin.cases incident_row_0_117 (Fin.cases incident_row_0_118 (Fin.cases incident_row_0_119 (Fin.cases incident_row_0_120 (Fin.cases incident_row_0_121 (Fin.cases incident_row_0_122 (Fin.cases incident_row_0_123 (Fin.cases incident_row_0_124 (Fin.cases incident_row_0_125 (Fin.cases incident_row_0_126 (Fin.cases incident_row_0_127 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
