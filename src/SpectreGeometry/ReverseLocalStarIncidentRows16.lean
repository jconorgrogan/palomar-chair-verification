module

public import SpectreGeometry.ReverseLocalStarIncidentRows16Part0
public import SpectreGeometry.ReverseLocalStarIncidentRows16Part1
public import SpectreGeometry.ReverseLocalStarIncidentRows16Part2
public import SpectreGeometry.ReverseLocalStarIncidentRows16Part3

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem incident_rows_1_6 : ∀ j : Fin 16,
    96+j.val < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true (96+j.val) =
      (if true then incidentRows1 else incidentRows0).getD (96+j.val) [] := by
  exact Fin.cases incident_row_1_96 (Fin.cases incident_row_1_97 (Fin.cases incident_row_1_98 (Fin.cases incident_row_1_99 (Fin.cases incident_row_1_100 (Fin.cases incident_row_1_101 (Fin.cases incident_row_1_102 (Fin.cases incident_row_1_103 (Fin.cases incident_row_1_104 (Fin.cases incident_row_1_105 (Fin.cases incident_row_1_106 (Fin.cases incident_row_1_107 (Fin.cases incident_row_1_108 (Fin.cases incident_row_1_109 (Fin.cases incident_row_1_110 (Fin.cases incident_row_1_111 (fun i => Fin.elim0 i))))))))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
