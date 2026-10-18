module

public import SpectreGeometry.ReverseLocalStarIncidentRows18Part0
public import SpectreGeometry.ReverseLocalStarIncidentRows18Part1
public import SpectreGeometry.ReverseLocalStarIncidentRows18Part2
public import SpectreGeometry.ReverseLocalStarIncidentRows18Part3

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem incident_rows_1_8 : ∀ j : Fin 16,
    128+j.val < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true (128+j.val) =
      (if true then incidentRows1 else incidentRows0).getD (128+j.val) [] := by
  exact Fin.cases incident_row_1_128 (Fin.cases incident_row_1_129 (Fin.cases incident_row_1_130 (Fin.cases incident_row_1_131 (Fin.cases incident_row_1_132 (Fin.cases incident_row_1_133 (Fin.cases incident_row_1_134 (Fin.cases incident_row_1_135 (Fin.cases incident_row_1_136 (Fin.cases incident_row_1_137 (Fin.cases incident_row_1_138 (Fin.cases incident_row_1_139 (Fin.cases incident_row_1_140 (Fin.cases incident_row_1_141 (Fin.cases incident_row_1_142 (Fin.cases incident_row_1_143 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
