module

public import SpectreGeometry.ReverseLocalStarIncidentData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem incident_row_1_100 :
    100 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 100 =
      (if true then incidentRows1 else incidentRows0).getD 100 [] := by decide
theorem incident_row_1_101 :
    101 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 101 =
      (if true then incidentRows1 else incidentRows0).getD 101 [] := by decide
theorem incident_row_1_102 :
    102 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 102 =
      (if true then incidentRows1 else incidentRows0).getD 102 [] := by decide
theorem incident_row_1_103 :
    103 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 103 =
      (if true then incidentRows1 else incidentRows0).getD 103 [] := by decide
end SpectreGeometry.ReverseLocalStarOccurrences
