module

public import SpectreGeometry.ReverseLocalStarIncidentRows17Part0
public import SpectreGeometry.ReverseLocalStarIncidentRows17Part1
public import SpectreGeometry.ReverseLocalStarIncidentRows17Part2
public import SpectreGeometry.ReverseLocalStarIncidentRows17Part3

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem incident_rows_1_7 : ∀ j : Fin 16,
    112+j.val < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true (112+j.val) =
      (if true then incidentRows1 else incidentRows0).getD (112+j.val) [] := by
  exact Fin.cases incident_row_1_112 (Fin.cases incident_row_1_113 (Fin.cases incident_row_1_114 (Fin.cases incident_row_1_115 (Fin.cases incident_row_1_116 (Fin.cases incident_row_1_117 (Fin.cases incident_row_1_118 (Fin.cases incident_row_1_119 (Fin.cases incident_row_1_120 (Fin.cases incident_row_1_121 (Fin.cases incident_row_1_122 (Fin.cases incident_row_1_123 (Fin.cases incident_row_1_124 (Fin.cases incident_row_1_125 (Fin.cases incident_row_1_126 (Fin.cases incident_row_1_127 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
