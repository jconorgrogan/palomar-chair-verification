module

public import SpectreGeometry.ReverseLocalStarIncidentData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem incident_row_1_120 :
    120 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 120 =
      (if true then incidentRows1 else incidentRows0).getD 120 [] := by decide
theorem incident_row_1_121 :
    121 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 121 =
      (if true then incidentRows1 else incidentRows0).getD 121 [] := by decide
theorem incident_row_1_122 :
    122 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 122 =
      (if true then incidentRows1 else incidentRows0).getD 122 [] := by decide
theorem incident_row_1_123 :
    123 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 123 =
      (if true then incidentRows1 else incidentRows0).getD 123 [] := by decide
end SpectreGeometry.ReverseLocalStarOccurrences
