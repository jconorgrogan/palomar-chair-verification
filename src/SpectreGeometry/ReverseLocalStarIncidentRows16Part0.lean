module

public import SpectreGeometry.ReverseLocalStarIncidentData

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem incident_row_1_96 :
    96 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 96 =
      (if true then incidentRows1 else incidentRows0).getD 96 [] := by decide
theorem incident_row_1_97 :
    97 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 97 =
      (if true then incidentRows1 else incidentRows0).getD 97 [] := by decide
theorem incident_row_1_98 :
    98 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 98 =
      (if true then incidentRows1 else incidentRows0).getD 98 [] := by decide
theorem incident_row_1_99 :
    99 < (SpectreGeometry.ReverseClusterTriangulation.targetVertices (kindMark true)).length →
    calculatedIncidentRow true 99 =
      (if true then incidentRows1 else incidentRows0).getD 99 [] := by decide
end SpectreGeometry.ReverseLocalStarOccurrences
