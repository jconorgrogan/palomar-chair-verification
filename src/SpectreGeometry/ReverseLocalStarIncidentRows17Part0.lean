module

public import SpectreGeometry.ReverseLocalStarIncidentData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem incident_row_1_112 :
    112 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 112 =
      (if true then incidentRows1 else incidentRows0).getD 112 [] := by decide
theorem incident_row_1_113 :
    113 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 113 =
      (if true then incidentRows1 else incidentRows0).getD 113 [] := by decide
theorem incident_row_1_114 :
    114 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 114 =
      (if true then incidentRows1 else incidentRows0).getD 114 [] := by decide
theorem incident_row_1_115 :
    115 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 115 =
      (if true then incidentRows1 else incidentRows0).getD 115 [] := by decide
end SpectreGeometry.ReverseLocalStarOccurrences
