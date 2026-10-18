module

public import SpectreGeometry.ReverseLocalStarIncidentRows15Part0
public import SpectreGeometry.ReverseLocalStarIncidentRows15Part1
public import SpectreGeometry.ReverseLocalStarIncidentRows15Part2
public import SpectreGeometry.ReverseLocalStarIncidentRows15Part3

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem incident_rows_1_5 : ∀ j : Fin 16,
    80+j.val < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true (80+j.val) =
      (if true then incidentRows1 else incidentRows0).getD (80+j.val) [] := by
  exact Fin.cases incident_row_1_80 (Fin.cases incident_row_1_81 (Fin.cases incident_row_1_82 (Fin.cases incident_row_1_83 (Fin.cases incident_row_1_84 (Fin.cases incident_row_1_85 (Fin.cases incident_row_1_86 (Fin.cases incident_row_1_87 (Fin.cases incident_row_1_88 (Fin.cases incident_row_1_89 (Fin.cases incident_row_1_90 (Fin.cases incident_row_1_91 (Fin.cases incident_row_1_92 (Fin.cases incident_row_1_93 (Fin.cases incident_row_1_94 (Fin.cases incident_row_1_95 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
