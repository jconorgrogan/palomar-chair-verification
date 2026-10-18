module

public import SpectreGeometry.ReverseLocalStarIncidentData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem incident_row_1_80 :
    80 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 80 =
      (if true then incidentRows1 else incidentRows0).getD 80 [] := by decide
theorem incident_row_1_81 :
    81 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 81 =
      (if true then incidentRows1 else incidentRows0).getD 81 [] := by decide
theorem incident_row_1_82 :
    82 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 82 =
      (if true then incidentRows1 else incidentRows0).getD 82 [] := by decide
theorem incident_row_1_83 :
    83 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 83 =
      (if true then incidentRows1 else incidentRows0).getD 83 [] := by decide
end SpectreGeometry.ReverseLocalStarOccurrences
