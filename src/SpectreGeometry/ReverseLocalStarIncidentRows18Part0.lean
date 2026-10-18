module

public import SpectreGeometry.ReverseLocalStarIncidentData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem incident_row_1_128 :
    128 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 128 =
      (if true then incidentRows1 else incidentRows0).getD 128 [] := by decide
theorem incident_row_1_129 :
    129 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 129 =
      (if true then incidentRows1 else incidentRows0).getD 129 [] := by decide
theorem incident_row_1_130 :
    130 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 130 =
      (if true then incidentRows1 else incidentRows0).getD 130 [] := by decide
theorem incident_row_1_131 :
    131 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 131 =
      (if true then incidentRows1 else incidentRows0).getD 131 [] := by decide
end SpectreGeometry.ReverseLocalStarOccurrences
