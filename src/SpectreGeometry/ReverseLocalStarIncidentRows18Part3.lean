module

public import SpectreGeometry.ReverseLocalStarIncidentData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem incident_row_1_140 :
    140 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 140 =
      (if true then incidentRows1 else incidentRows0).getD 140 [] := by decide
theorem incident_row_1_141 :
    141 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 141 =
      (if true then incidentRows1 else incidentRows0).getD 141 [] := by decide
theorem incident_row_1_142 :
    142 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 142 =
      (if true then incidentRows1 else incidentRows0).getD 142 [] := by decide
theorem incident_row_1_143 :
    143 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 143 =
      (if true then incidentRows1 else incidentRows0).getD 143 [] := by decide
end SpectreGeometry.ReverseLocalStarOccurrences
