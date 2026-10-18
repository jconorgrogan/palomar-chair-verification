module

public import SpectreGeometry.ReverseClusterTriangulationData
public import SpectreGeometry.ReverseClusterTriangulationCoverAssembly

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open SpectreClusters HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def targetKiteFamily0Chunk0 : List PolygonPacket := [
  ⟨[(-12,-12),(0,-18),(0,-12),(-6,-6)],[(1,2,36),(-1,0,0),(-1,-1,-12),(1,-1,0)],[6,6,6,6]⟩,
  ⟨[(-12,-12),(-6,-6),(-12,0),(-18,0)],[(-1,1,0),(-1,-1,-12),(0,-1,0),(2,1,36)],[6,6,6,6]⟩,
  ⟨[(0,0),(12,-6),(12,0),(6,6)],[(1,2,0),(-1,0,12),(-1,-1,12),(1,-1,0)],[6,6,6,6]⟩,
  ⟨[(0,0),(-12,6),(-12,0),(-6,-6)],[(-1,-2,0),(1,0,12),(1,1,12),(-1,1,0)],[6,6,6,6]⟩,
  ⟨[(0,0),(-6,-6),(0,-12),(6,-12)],[(1,-1,0),(1,1,12),(0,1,12),(-2,-1,0)],[6,6,6,6]⟩,
  ⟨[(0,0),(6,-12),(12,-12),(12,-6)],[(2,1,0),(0,1,12),(-1,0,12),(-1,-2,0)],[6,6,6,6]⟩,
  ⟨[(12,-24),(18,-18),(12,-12),(6,-12)],[(-1,1,36),(-1,-1,0),(0,-1,-12),(2,1,0)],[6,6,6,6]⟩,
  ⟨[(12,-24),(6,-12),(0,-12),(0,-18)],[(-2,-1,0),(0,-1,-12),(1,0,0),(1,2,36)],[6,6,6,6]⟩
]
theorem targetKiteFamily0Chunk0_checked : familyCheckedB targetKiteFamily0Chunk0 = true := by decide

def targetKiteFamily0Chunk1 : List PolygonPacket := [
  ⟨[(24,-12),(12,-6),(12,-12),(18,-18)],[(-1,-2,0),(1,0,-12),(1,1,0),(-1,1,36)],[6,6,6,6]⟩,
  ⟨[(24,-12),(18,-18),(24,-24),(30,-24)],[(1,-1,-36),(1,1,0),(0,1,24),(-2,-1,36)],[6,6,6,6]⟩,
  ⟨[(24,-12),(18,0),(12,0),(12,-6)],[(-2,-1,36),(0,-1,0),(1,0,-12),(1,2,0)],[6,6,6,6]⟩,
  ⟨[(24,-12),(30,-24),(36,-24),(36,-18)],[(2,1,-36),(0,1,24),(-1,0,36),(-1,-2,0)],[6,6,6,6]⟩,
  ⟨[(24,-12),(36,-18),(36,-12),(30,-6)],[(1,2,0),(-1,0,36),(-1,-1,24),(1,-1,-36)],[6,6,6,6]⟩,
  ⟨[(24,-12),(30,-6),(24,0),(18,0)],[(-1,1,36),(-1,-1,24),(0,-1,0),(2,1,-36)],[6,6,6,6]⟩,
  ⟨[(36,0),(30,12),(24,12),(24,6)],[(-2,-1,72),(0,-1,12),(1,0,-24),(1,2,-36)],[6,6,6,6]⟩,
  ⟨[(36,0),(24,6),(24,0),(30,-6)],[(-1,-2,36),(1,0,-24),(1,1,-24),(-1,1,36)],[6,6,6,6]⟩
]
theorem targetKiteFamily0Chunk1_checked : familyCheckedB targetKiteFamily0Chunk1 = true := by decide

def targetKiteFamily0Chunk2 : List PolygonPacket := [
  ⟨[(12,12),(6,6),(12,0),(18,0)],[(1,-1,0),(1,1,-12),(0,1,0),(-2,-1,36)],[6,6,6,6]⟩,
  ⟨[(12,12),(18,0),(24,0),(24,6)],[(2,1,-36),(0,1,0),(-1,0,24),(-1,-2,36)],[6,6,6,6]⟩,
  ⟨[(12,12),(0,18),(0,12),(6,6)],[(-1,-2,36),(1,0,0),(1,1,-12),(-1,1,0)],[6,6,6,6]⟩,
  ⟨[(12,12),(24,6),(24,12),(18,18)],[(1,2,-36),(-1,0,24),(-1,-1,36),(1,-1,0)],[6,6,6,6]⟩,
  ⟨[(12,12),(18,18),(12,24),(6,24)],[(-1,1,0),(-1,-1,36),(0,-1,24),(2,1,-36)],[6,6,6,6]⟩,
  ⟨[(12,12),(6,24),(0,24),(0,18)],[(-2,-1,36),(0,-1,24),(1,0,0),(1,2,-36)],[6,6,6,6]⟩,
  ⟨[(0,36),(-12,42),(-12,36),(-6,30)],[(-1,-2,72),(1,0,12),(1,1,-24),(-1,1,-36)],[6,6,6,6]⟩,
  ⟨[(0,36),(-6,30),(0,24),(6,24)],[(1,-1,36),(1,1,-24),(0,1,-24),(-2,-1,36)],[6,6,6,6]⟩
]
theorem targetKiteFamily0Chunk2_checked : familyCheckedB targetKiteFamily0Chunk2 = true := by decide

def targetKiteFamily0Chunk3 : List PolygonPacket := [
  ⟨[(-12,24),(-6,12),(0,12),(0,18)],[(2,1,0),(0,1,-12),(-1,0,0),(-1,-2,36)],[6,6,6,6]⟩,
  ⟨[(-12,24),(0,18),(0,24),(-6,30)],[(1,2,-36),(-1,0,0),(-1,-1,24),(1,-1,36)],[6,6,6,6]⟩,
  ⟨[(-24,12),(-18,18),(-24,24),(-30,24)],[(-1,1,-36),(-1,-1,0),(0,-1,24),(2,1,36)],[6,6,6,6]⟩,
  ⟨[(-24,12),(-30,6),(-24,0),(-18,0)],[(1,-1,36),(1,1,24),(0,1,0),(-2,-1,-36)],[6,6,6,6]⟩,
  ⟨[(-24,12),(-18,0),(-12,0),(-12,6)],[(2,1,36),(0,1,0),(-1,0,-12),(-1,-2,0)],[6,6,6,6]⟩,
  ⟨[(-24,12),(-12,6),(-12,12),(-18,18)],[(1,2,0),(-1,0,-12),(-1,-1,0),(1,-1,36)],[6,6,6,6]⟩,
  ⟨[(0,0),(6,6),(0,12),(-6,12)],[(-1,1,0),(-1,-1,12),(0,-1,12),(2,1,0)],[6,6,6,6]⟩,
  ⟨[(0,0),(-6,12),(-12,12),(-12,6)],[(-2,-1,0),(0,-1,12),(1,0,12),(1,2,0)],[6,6,6,6]⟩
]
theorem targetKiteFamily0Chunk3_checked : familyCheckedB targetKiteFamily0Chunk3 = true := by decide

def targetKiteFamily0Chunk4 : List PolygonPacket := [
  ⟨[(-12,24),(-24,30),(-24,24),(-18,18)],[(-1,-2,36),(1,0,24),(1,1,0),(-1,1,-36)],[6,6,6,6]⟩,
  ⟨[(-12,24),(-18,18),(-12,12),(-6,12)],[(1,-1,36),(1,1,0),(0,1,-12),(-2,-1,0)],[6,6,6,6]⟩,
  ⟨[(-12,-12),(-6,-24),(0,-24),(0,-18)],[(2,1,36),(0,1,24),(-1,0,0),(-1,-2,-36)],[6,6,6,6]⟩,
  ⟨[(-12,-12),(-18,0),(-24,0),(-24,-6)],[(-2,-1,-36),(0,-1,0),(1,0,24),(1,2,36)],[6,6,6,6]⟩,
  ⟨[(-12,-12),(-24,-6),(-24,-12),(-18,-18)],[(-1,-2,-36),(1,0,24),(1,1,36),(-1,1,0)],[6,6,6,6]⟩,
  ⟨[(-12,-12),(-18,-18),(-12,-24),(-6,-24)],[(1,-1,0),(1,1,36),(0,1,24),(-2,-1,-36)],[6,6,6,6]⟩,
  ⟨[(-24,-24),(-18,-36),(-12,-36),(-12,-30)],[(2,1,72),(0,1,36),(-1,0,-12),(-1,-2,-72)],[6,6,6,6]⟩,
  ⟨[(-24,-24),(-12,-30),(-12,-24),(-18,-18)],[(1,2,72),(-1,0,-12),(-1,-1,-36),(1,-1,0)],[6,6,6,6]⟩
]
theorem targetKiteFamily0Chunk4_checked : familyCheckedB targetKiteFamily0Chunk4 = true := by decide

def targetKiteFamily0Chunk5 : List PolygonPacket := [
  ⟨[(0,-36),(6,-30),(0,-24),(-6,-24)],[(-1,1,36),(-1,-1,-24),(0,-1,-24),(2,1,36)],[6,6,6,6]⟩,
  ⟨[(0,-36),(-6,-24),(-12,-24),(-12,-30)],[(-2,-1,-36),(0,-1,-24),(1,0,12),(1,2,72)],[6,6,6,6]⟩,
  ⟨[(12,-24),(24,-30),(24,-24),(18,-18)],[(1,2,36),(-1,0,24),(-1,-1,0),(1,-1,-36)],[6,6,6,6]⟩,
  ⟨[(12,-24),(0,-18),(0,-24),(6,-30)],[(-1,-2,-36),(1,0,0),(1,1,24),(-1,1,36)],[6,6,6,6]⟩,
  ⟨[(12,-24),(6,-30),(12,-36),(18,-36)],[(1,-1,-36),(1,1,24),(0,1,36),(-2,-1,0)],[6,6,6,6]⟩,
  ⟨[(12,-24),(18,-36),(24,-36),(24,-30)],[(2,1,0),(0,1,36),(-1,0,24),(-1,-2,-36)],[6,6,6,6]⟩,
  ⟨[(24,-48),(36,-54),(36,-48),(30,-42)],[(1,2,72),(-1,0,36),(-1,-1,-12),(1,-1,-72)],[6,6,6,6]⟩,
  ⟨[(24,-48),(30,-42),(24,-36),(18,-36)],[(-1,1,72),(-1,-1,-12),(0,-1,-36),(2,1,0)],[6,6,6,6]⟩
]
theorem targetKiteFamily0Chunk5_checked : familyCheckedB targetKiteFamily0Chunk5 = true := by decide

def targetKiteFamily0Chunk6 : List PolygonPacket := [
  ⟨[(36,-36),(30,-24),(24,-24),(24,-30)],[(-2,-1,36),(0,-1,-24),(1,0,-24),(1,2,36)],[6,6,6,6]⟩,
  ⟨[(36,-36),(24,-30),(24,-36),(30,-42)],[(-1,-2,-36),(1,0,-24),(1,1,12),(-1,1,72)],[6,6,6,6]⟩,
  ⟨[(0,-36),(12,-42),(12,-36),(6,-30)],[(1,2,72),(-1,0,12),(-1,-1,-24),(1,-1,-36)],[6,6,6,6]⟩,
  ⟨[(0,-36),(-12,-30),(-12,-36),(-6,-42)],[(-1,-2,-72),(1,0,12),(1,1,48),(-1,1,36)],[6,6,6,6]⟩,
  ⟨[(0,-36),(-6,-42),(0,-48),(6,-48)],[(1,-1,-36),(1,1,48),(0,1,48),(-2,-1,-36)],[6,6,6,6]⟩,
  ⟨[(0,-36),(6,-48),(12,-48),(12,-42)],[(2,1,36),(0,1,48),(-1,0,12),(-1,-2,-72)],[6,6,6,6]⟩,
  ⟨[(12,-60),(24,-66),(24,-60),(18,-54)],[(1,2,108),(-1,0,24),(-1,-1,-36),(1,-1,-72)],[6,6,6,6]⟩,
  ⟨[(12,-60),(18,-54),(12,-48),(6,-48)],[(-1,1,72),(-1,-1,-36),(0,-1,-48),(2,1,36)],[6,6,6,6]⟩
]
theorem targetKiteFamily0Chunk6_checked : familyCheckedB targetKiteFamily0Chunk6 = true := by decide

def targetKiteFamily0Chunk7 : List PolygonPacket := [
  ⟨[(24,-48),(18,-36),(12,-36),(12,-42)],[(-2,-1,0),(0,-1,-36),(1,0,-12),(1,2,72)],[6,6,6,6]⟩,
  ⟨[(24,-48),(12,-42),(12,-48),(18,-54)],[(-1,-2,-72),(1,0,-12),(1,1,36),(-1,1,72)],[6,6,6,6]⟩,
  ⟨[(36,-36),(42,-30),(36,-24),(30,-24)],[(-1,1,72),(-1,-1,12),(0,-1,-24),(2,1,-36)],[6,6,6,6]⟩,
  ⟨[(36,-36),(30,-42),(36,-48),(42,-48)],[(1,-1,-72),(1,1,12),(0,1,48),(-2,-1,36)],[6,6,6,6]⟩,
  ⟨[(36,-36),(42,-48),(48,-48),(48,-42)],[(2,1,-36),(0,1,48),(-1,0,48),(-1,-2,-36)],[6,6,6,6]⟩,
  ⟨[(36,-36),(48,-42),(48,-36),(42,-30)],[(1,2,36),(-1,0,48),(-1,-1,12),(1,-1,-72)],[6,6,6,6]⟩,
  ⟨[(60,-48),(66,-42),(60,-36),(54,-36)],[(-1,1,108),(-1,-1,24),(0,-1,-36),(2,1,-72)],[6,6,6,6]⟩,
  ⟨[(60,-48),(54,-36),(48,-36),(48,-42)],[(-2,-1,72),(0,-1,-36),(1,0,-48),(1,2,36)],[6,6,6,6]⟩
]
theorem targetKiteFamily0Chunk7_checked : familyCheckedB targetKiteFamily0Chunk7 = true := by decide

def targetKiteFamily0Chunk8 : List PolygonPacket := [
  ⟨[(48,-24),(36,-18),(36,-24),(42,-30)],[(-1,-2,0),(1,0,-36),(1,1,-12),(-1,1,72)],[6,6,6,6]⟩,
  ⟨[(48,-24),(42,-30),(48,-36),(54,-36)],[(1,-1,-72),(1,1,-12),(0,1,36),(-2,-1,72)],[6,6,6,6]⟩
]
theorem targetKiteFamily0Chunk8_checked : familyCheckedB targetKiteFamily0Chunk8 = true := by decide

def targetKiteFamily0 : List PolygonPacket := targetKiteFamily0Chunk0 ++ targetKiteFamily0Chunk1 ++ targetKiteFamily0Chunk2 ++ targetKiteFamily0Chunk3 ++ targetKiteFamily0Chunk4 ++ targetKiteFamily0Chunk5 ++ targetKiteFamily0Chunk6 ++ targetKiteFamily0Chunk7 ++ targetKiteFamily0Chunk8
theorem targetKiteFamily0_checked : familyCheckedB targetKiteFamily0 = true := by
  have h : familyCheckedB targetKiteFamily0Chunk0 = true ∧ familyCheckedB targetKiteFamily0Chunk1 = true ∧ familyCheckedB targetKiteFamily0Chunk2 = true ∧ familyCheckedB targetKiteFamily0Chunk3 = true ∧ familyCheckedB targetKiteFamily0Chunk4 = true ∧ familyCheckedB targetKiteFamily0Chunk5 = true ∧ familyCheckedB targetKiteFamily0Chunk6 = true ∧ familyCheckedB targetKiteFamily0Chunk7 = true ∧ familyCheckedB targetKiteFamily0Chunk8 = true := by
    exact ⟨targetKiteFamily0Chunk0_checked, targetKiteFamily0Chunk1_checked, targetKiteFamily0Chunk2_checked, targetKiteFamily0Chunk3_checked, targetKiteFamily0Chunk4_checked, targetKiteFamily0Chunk5_checked, targetKiteFamily0Chunk6_checked, targetKiteFamily0Chunk7_checked, targetKiteFamily0Chunk8_checked⟩
  simpa only [targetKiteFamily0,familyCheckedB,List.all_append,Bool.and_eq_true,and_assoc] using h

def targetMeshFamily0Chunk0 : List PolygonPacket := [
  ⟨[(-18,-18),(-24,-24),(-20,-26)],[(1,-1,0),(1,2,72),(-4,1,-54)],[6,2,2]⟩,
  ⟨[(-24,-24),(-18,-36),(-20,-26)],[(2,1,72),(-5,-1,-126),(-1,-2,-72)],[6,2,2]⟩,
  ⟨[(-18,-36),(-18,-27),(-20,-26)],[(-1,0,-18),(-1,-2,-72),(5,1,126)],[9,1,2]⟩,
  ⟨[(-18,-27),(-18,-18),(-20,-26)],[(-1,0,-18),(4,-1,54),(1,2,72)],[9,2,1]⟩,
  ⟨[(-18,-18),(-18,-27),(-16,-30)],[(1,0,18),(3,2,108),(-6,-1,-126)],[9,1,2]⟩,
  ⟨[(-18,-27),(-18,-36),(-16,-30)],[(1,0,18),(-3,1,-18),(-3,-2,-108)],[9,2,1]⟩,
  ⟨[(-18,-36),(-12,-36),(-16,-30)],[(0,1,36),(-3,-2,-108),(3,-1,18)],[6,2,2]⟩,
  ⟨[(-12,-36),(-15,-27),(-16,-30)],[(-3,-1,-72),(3,-1,18),(3,2,108)],[3,1,2]⟩
]
theorem targetMeshFamily0Chunk0_checked : familyCheckedB targetMeshFamily0Chunk0 = true := by decide

def targetMeshFamily0Chunk0Codes : List TriangleCode := [(4,5,85),(5,6,85),(6,49,85),(49,4,85),(4,49,86),(49,6,86),(6,7,86),(7,50,86)]
theorem targetMeshFamily0Chunk0_bound : targetMeshFamily0Chunk0.map PolygonPacket.vertices =
    targetMeshFamily0Chunk0Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0Chunk1 : List PolygonPacket := [
  ⟨[(-15,-27),(-18,-18),(-16,-30)],[(-3,-1,-72),(6,1,126),(-3,1,-18)],[3,2,1]⟩,
  ⟨[(6,-48),(12,-60),(14,-58)],[(2,1,36),(-1,1,72),(-5,-4,-162)],[6,2,2]⟩,
  ⟨[(12,-60),(24,-66),(14,-58)],[(1,2,108),(-4,-5,-234),(1,-1,-72)],[6,2,2]⟩,
  ⟨[(24,-66),(15,-57),(14,-58)],[(-1,-1,-42),(1,-1,-72),(4,5,234)],[9,1,2]⟩,
  ⟨[(15,-57),(6,-48),(14,-58)],[(-1,-1,-42),(5,4,162),(-1,1,72)],[9,2,1]⟩,
  ⟨[(6,-48),(15,-57),(18,-58)],[(1,1,42),(1,3,156),(-5,-6,-258)],[9,1,2]⟩,
  ⟨[(15,-57),(24,-66),(18,-58)],[(1,1,42),(-4,-3,-102),(-1,-3,-156)],[9,2,1]⟩,
  ⟨[(24,-66),(24,-60),(18,-58)],[(-1,0,24),(-1,-3,-156),(4,3,102)],[6,2,2]⟩
]
theorem targetMeshFamily0Chunk1_checked : familyCheckedB targetMeshFamily0Chunk1 = true := by decide

def targetMeshFamily0Chunk1Codes : List TriangleCode := [(50,4,86),(10,11,87),(11,12,87),(12,55,87),(55,10,87),(10,55,88),(55,12,88),(12,13,88)]
theorem targetMeshFamily0Chunk1_bound : targetMeshFamily0Chunk1.map PolygonPacket.vertices =
    targetMeshFamily0Chunk1Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0Chunk2 : List PolygonPacket := [
  ⟨[(24,-60),(15,-54),(18,-58)],[(-2,-3,-132),(4,3,102),(1,3,156)],[3,1,2]⟩,
  ⟨[(15,-54),(6,-48),(18,-58)],[(-2,-3,-132),(5,6,258),(-4,-3,-102)],[3,2,1]⟩,
  ⟨[(48,-42),(60,-48),(58,-44)],[(1,2,36),(-2,-1,72),(-1,-5,-162)],[6,2,2]⟩,
  ⟨[(60,-48),(66,-42),(58,-44)],[(-1,1,108),(1,-4,-234),(2,1,-72)],[6,2,2]⟩,
  ⟨[(66,-42),(57,-42),(58,-44)],[(0,-1,-42),(2,1,-72),(-1,4,234)],[9,1,2]⟩,
  ⟨[(57,-42),(48,-42),(58,-44)],[(0,-1,-42),(1,5,162),(-2,-1,72)],[9,2,1]⟩,
  ⟨[(48,-42),(57,-42),(58,-40)],[(0,1,42),(-2,1,156),(1,-5,-258)],[9,1,2]⟩,
  ⟨[(57,-42),(66,-42),(58,-40)],[(0,1,42),(-1,-4,-102),(2,-1,-156)],[9,2,1]⟩
]
theorem targetMeshFamily0Chunk2_checked : familyCheckedB targetMeshFamily0Chunk2 = true := by decide

def targetMeshFamily0Chunk2Codes : List TriangleCode := [(13,56,88),(56,10,88),(20,21,89),(21,22,89),(22,65,89),(65,20,89),(20,65,90),(65,22,90)]
theorem targetMeshFamily0Chunk2_bound : targetMeshFamily0Chunk2.map PolygonPacket.vertices =
    targetMeshFamily0Chunk2Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0Chunk3 : List PolygonPacket := [
  ⟨[(66,-42),(60,-36),(58,-40)],[(-1,-1,24),(2,-1,-156),(1,4,102)],[6,2,2]⟩,
  ⟨[(60,-36),(54,-39),(58,-40)],[(1,-2,-132),(1,4,102),(-2,1,156)],[3,1,2]⟩,
  ⟨[(54,-39),(48,-42),(58,-40)],[(1,-2,-132),(-1,5,258),(-1,-4,-102)],[3,2,1]⟩,
  ⟨[(54,-36),(48,-24),(46,-26)],[(-2,-1,72),(1,-1,-72),(5,4,-126)],[6,2,2]⟩,
  ⟨[(48,-24),(36,-18),(46,-26)],[(-1,-2,0),(4,5,-54),(-1,1,72)],[6,2,2]⟩,
  ⟨[(36,-18),(45,-27),(46,-26)],[(1,1,-18),(-1,1,72),(-4,-5,54)],[9,1,2]⟩,
  ⟨[(45,-27),(54,-36),(46,-26)],[(1,1,-18),(-5,-4,126),(1,-1,-72)],[9,2,1]⟩,
  ⟨[(30,-6),(36,0),(32,2)],[(-1,1,36),(-1,-2,36),(4,-1,-126)],[6,2,2]⟩
]
theorem targetMeshFamily0Chunk3_checked : familyCheckedB targetMeshFamily0Chunk3 = true := by decide

def targetMeshFamily0Chunk3Codes : List TriangleCode := [(22,23,90),(23,66,90),(66,20,90),(24,25,91),(25,26,91),(26,70,91),(70,24,91),(28,29,92)]
theorem targetMeshFamily0Chunk3_bound : targetMeshFamily0Chunk3.map PolygonPacket.vertices =
    targetMeshFamily0Chunk3Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0Chunk4 : List PolygonPacket := [
  ⟨[(36,0),(30,12),(32,2)],[(-2,-1,72),(5,1,-162),(1,2,-36)],[6,2,2]⟩,
  ⟨[(30,12),(30,3),(32,2)],[(1,0,-30),(1,2,-36),(-5,-1,162)],[9,1,2]⟩,
  ⟨[(30,3),(30,-6),(32,2)],[(1,0,-30),(-4,1,126),(-1,-2,36)],[9,2,1]⟩,
  ⟨[(30,-6),(30,3),(28,6)],[(-1,0,30),(-3,-2,96),(6,1,-174)],[9,1,2]⟩,
  ⟨[(30,3),(30,12),(28,6)],[(-1,0,30),(3,-1,-78),(3,2,-96)],[9,2,1]⟩,
  ⟨[(30,12),(24,12),(28,6)],[(0,-1,12),(3,2,-96),(-3,1,78)],[6,2,2]⟩,
  ⟨[(24,12),(27,3),(28,6)],[(3,1,-84),(-3,1,78),(-3,-2,96)],[3,1,2]⟩,
  ⟨[(27,3),(30,-6),(28,6)],[(3,1,-84),(-6,-1,174),(3,-1,-78)],[3,2,1]⟩
]
theorem targetMeshFamily0Chunk4_checked : familyCheckedB targetMeshFamily0Chunk4 = true := by decide

def targetMeshFamily0Chunk4Codes : List TriangleCode := [(29,30,92),(30,73,92),(73,28,92),(28,73,93),(73,30,93),(30,31,93),(31,74,93),(74,28,93)]
theorem targetMeshFamily0Chunk4_bound : targetMeshFamily0Chunk4.map PolygonPacket.vertices =
    targetMeshFamily0Chunk4Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0Chunk5 : List PolygonPacket := [
  ⟨[(6,24),(0,36),(-2,34)],[(-2,-1,36),(1,-1,36),(5,4,-126)],[6,2,2]⟩,
  ⟨[(0,36),(-12,42),(-2,34)],[(-1,-2,72),(4,5,-162),(-1,1,-36)],[6,2,2]⟩,
  ⟨[(-12,42),(-3,33),(-2,34)],[(1,1,-30),(-1,1,-36),(-4,-5,162)],[9,1,2]⟩,
  ⟨[(-3,33),(6,24),(-2,34)],[(1,1,-30),(-5,-4,126),(1,-1,36)],[9,2,1]⟩,
  ⟨[(6,24),(-3,33),(-6,34)],[(-1,-1,30),(-1,-3,96),(5,6,-174)],[9,1,2]⟩,
  ⟨[(-3,33),(-12,42),(-6,34)],[(-1,-1,30),(4,3,-78),(1,3,-96)],[9,2,1]⟩,
  ⟨[(-12,42),(-12,36),(-6,34)],[(1,0,12),(1,3,-96),(-4,-3,78)],[6,2,2]⟩,
  ⟨[(-12,36),(-3,30),(-6,34)],[(2,3,-84),(-4,-3,78),(-1,-3,96)],[3,1,2]⟩
]
theorem targetMeshFamily0Chunk5_checked : familyCheckedB targetMeshFamily0Chunk5 = true := by decide

def targetMeshFamily0Chunk5Codes : List TriangleCode := [(34,35,94),(35,36,94),(36,79,94),(79,34,94),(34,79,95),(79,36,95),(36,37,95),(37,80,95)]
theorem targetMeshFamily0Chunk5_bound : targetMeshFamily0Chunk5.map PolygonPacket.vertices =
    targetMeshFamily0Chunk5Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0Chunk6 : List PolygonPacket := [
  ⟨[(-3,30),(6,24),(-6,34)],[(2,3,-84),(-5,-6,174),(4,3,-78)],[3,2,1]⟩,
  ⟨[(-24,12),(-30,6),(-26,6)],[(1,-1,36),(0,1,-6),(-3,1,-84)],[6,4,2]⟩,
  ⟨[(-30,6),(-24,0),(-26,6)],[(1,1,24),(-3,-1,-72),(0,-1,6)],[6,2,4]⟩,
  ⟨[(-24,0),(-24,6),(-26,6)],[(-1,0,-24),(0,-1,6),(3,1,72)],[6,2,2]⟩,
  ⟨[(-24,6),(-24,12),(-26,6)],[(-1,0,-24),(3,-1,84),(0,1,-6)],[6,2,2]⟩,
  ⟨[(-18,-18),(-15,-27),(-12,-32)],[(3,1,72),(5,3,156),(-7,-3,-180)],[3,1,2]⟩,
  ⟨[(-15,-27),(-12,-36),(-12,-32)],[(3,1,72),(-1,0,-12),(-5,-3,-156)],[3,4,1]⟩,
  ⟨[(-12,-36),(-6,-42),(-12,-32)],[(1,1,48),(-5,-3,-156),(1,0,12)],[6,2,4]⟩
]
theorem targetMeshFamily0Chunk6_checked : familyCheckedB targetMeshFamily0Chunk6 = true := by decide

def targetMeshFamily0Chunk6Codes : List TriangleCode := [(80,34,95),(43,0,96),(0,1,96),(1,45,96),(45,43,96),(4,50,97),(50,7,97),(7,8,97)]
theorem targetMeshFamily0Chunk6_bound : targetMeshFamily0Chunk6.map PolygonPacket.vertices =
    targetMeshFamily0Chunk6Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0Chunk7 : List PolygonPacket := [
  ⟨[(-6,-42),(-12,-30),(-12,-32)],[(-2,-1,-54),(1,0,12),(5,3,156)],[6,2,2]⟩,
  ⟨[(-12,-30),(-18,-18),(-12,-32)],[(-2,-1,-54),(7,3,180),(-1,0,-12)],[6,2,2]⟩,
  ⟨[(-18,-18),(-12,-30),(-8,-36)],[(2,1,54),(3,2,96),(-9,-5,-252)],[6,2,2]⟩,
  ⟨[(-12,-30),(-6,-42),(-8,-36)],[(2,1,54),(-3,-1,-60),(-3,-2,-96)],[6,2,2]⟩,
  ⟨[(-6,-42),(0,-48),(-8,-36)],[(1,1,48),(-3,-2,-96),(3,1,60)],[6,4,2]⟩,
  ⟨[(0,-48),(-9,-33),(-8,-36)],[(-5,-3,-144),(3,1,60),(3,2,96)],[3,1,4]⟩,
  ⟨[(-9,-33),(-18,-18),(-8,-36)],[(-5,-3,-144),(9,5,252),(-3,-1,-60)],[3,2,1]⟩,
  ⟨[(-18,-18),(-9,-33),(-4,-38)],[(5,3,144),(1,1,42),(-10,-7,-306)],[3,5,2]⟩
]
theorem targetMeshFamily0Chunk7_checked : familyCheckedB targetMeshFamily0Chunk7 = true := by decide

def targetMeshFamily0Chunk7Codes : List TriangleCode := [(8,51,97),(51,4,97),(4,51,98),(51,8,98),(8,9,98),(9,52,98),(52,4,98),(4,52,99)]
theorem targetMeshFamily0Chunk7_bound : targetMeshFamily0Chunk7.map PolygonPacket.vertices =
    targetMeshFamily0Chunk7Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0Chunk8 : List PolygonPacket := [
  ⟨[(-9,-33),(0,-48),(-4,-38)],[(5,3,144),(-5,-2,-96),(-1,-1,-42)],[3,2,5]⟩,
  ⟨[(0,-48),(6,-48),(-4,-38)],[(0,1,48),(-1,-1,-42),(5,2,96)],[6,10,2]⟩,
  ⟨[(6,-48),(-6,-33),(-4,-38)],[(-5,-4,-162),(5,2,96),(1,1,42)],[3,1,10]⟩,
  ⟨[(-6,-33),(-18,-18),(-4,-38)],[(-5,-4,-162),(10,7,306),(-5,-2,-96)],[3,2,1]⟩,
  ⟨[(24,-48),(36,-54),(32,-50)],[(1,2,72),(-1,-1,-18),(-1,-4,-168)],[6,4,2]⟩,
  ⟨[(36,-54),(36,-48),(32,-50)],[(-1,0,36),(1,-2,-132),(1,1,18)],[6,2,4]⟩,
  ⟨[(36,-48),(30,-48),(32,-50)],[(0,-1,-48),(1,1,18),(-1,2,132)],[6,2,2]⟩,
  ⟨[(30,-48),(24,-48),(32,-50)],[(0,-1,-48),(1,4,168),(-1,-1,-18)],[6,2,2]⟩
]
theorem targetMeshFamily0Chunk8_checked : familyCheckedB targetMeshFamily0Chunk8 = true := by decide

def targetMeshFamily0Chunk8Codes : List TriangleCode := [(52,9,99),(9,10,99),(10,53,99),(53,4,99),(15,16,100),(16,17,100),(17,60,100),(60,15,100)]
theorem targetMeshFamily0Chunk8_bound : targetMeshFamily0Chunk8.map PolygonPacket.vertices =
    targetMeshFamily0Chunk8Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0Chunk9 : List PolygonPacket := [
  ⟨[(30,-6),(27,3),(24,8)],[(-3,-1,84),(-5,-3,144),(7,3,-192)],[3,1,2]⟩,
  ⟨[(27,3),(24,12),(24,8)],[(-3,-1,84),(1,0,-24),(5,3,-144)],[3,4,1]⟩,
  ⟨[(24,12),(18,18),(24,8)],[(-1,-1,36),(5,3,-144),(-1,0,24)],[6,2,4]⟩,
  ⟨[(18,18),(24,6),(24,8)],[(2,1,-54),(-1,0,24),(-5,-3,144)],[6,2,2]⟩,
  ⟨[(24,6),(30,-6),(24,8)],[(2,1,-54),(-7,-3,192),(1,0,-24)],[6,2,2]⟩,
  ⟨[(30,-6),(24,6),(20,12)],[(-2,-1,54),(-3,-2,84),(9,5,-240)],[6,2,2]⟩,
  ⟨[(24,6),(18,18),(20,12)],[(-2,-1,54),(3,1,-72),(3,2,-84)],[6,2,2]⟩,
  ⟨[(18,18),(12,24),(20,12)],[(-1,-1,36),(3,2,-84),(-3,-1,72)],[6,4,2]⟩
]
theorem targetMeshFamily0Chunk9_checked : familyCheckedB targetMeshFamily0Chunk9 = true := by decide

def targetMeshFamily0Chunk9Codes : List TriangleCode := [(28,74,101),(74,31,101),(31,32,101),(32,75,101),(75,28,101),(28,75,102),(75,32,102),(32,33,102)]
theorem targetMeshFamily0Chunk9_bound : targetMeshFamily0Chunk9.map PolygonPacket.vertices =
    targetMeshFamily0Chunk9Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0Chunk10 : List PolygonPacket := [
  ⟨[(12,24),(21,9),(20,12)],[(5,3,-132),(-3,-1,72),(-3,-2,84)],[3,1,4]⟩,
  ⟨[(21,9),(30,-6),(20,12)],[(5,3,-132),(-9,-5,240),(3,1,-72)],[3,2,1]⟩,
  ⟨[(30,-6),(21,9),(16,14)],[(-5,-3,132),(-1,-1,30),(10,7,-258)],[3,5,2]⟩,
  ⟨[(21,9),(12,24),(16,14)],[(-5,-3,132),(5,2,-108),(1,1,-30)],[3,2,5]⟩,
  ⟨[(12,24),(6,24),(16,14)],[(0,-1,24),(1,1,-30),(-5,-2,108)],[6,10,2]⟩,
  ⟨[(6,24),(18,9),(16,14)],[(5,4,-126),(-5,-2,108),(-1,-1,30)],[3,1,10]⟩,
  ⟨[(18,9),(30,-6),(16,14)],[(5,4,-126),(-10,-7,258),(5,2,-108)],[3,2,1]⟩,
  ⟨[(-12,24),(-24,30),(-20,26)],[(-1,-2,36),(1,1,-6),(1,4,-84)],[6,4,2]⟩
]
theorem targetMeshFamily0Chunk10_checked : familyCheckedB targetMeshFamily0Chunk10 = true := by decide

def targetMeshFamily0Chunk10Codes : List TriangleCode := [(33,76,102),(76,28,102),(28,76,103),(76,33,103),(33,34,103),(34,77,103),(77,28,103),(39,40,104)]
theorem targetMeshFamily0Chunk10_bound : targetMeshFamily0Chunk10.map PolygonPacket.vertices =
    targetMeshFamily0Chunk10Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0Chunk11 : List PolygonPacket := [
  ⟨[(-24,30),(-24,24),(-20,26)],[(1,0,24),(-1,2,-72),(-1,-1,6)],[6,2,4]⟩,
  ⟨[(-24,24),(-18,24),(-20,26)],[(0,1,-24),(-1,-1,6),(1,-2,72)],[6,2,2]⟩,
  ⟨[(-18,24),(-12,24),(-20,26)],[(0,1,-24),(-1,-4,84),(1,1,-6)],[6,2,2]⟩,
  ⟨[(-24,24),(-30,24),(-26,20)],[(0,-1,24),(1,1,6),(-2,1,-72)],[6,4,2]⟩,
  ⟨[(-30,24),(-24,12),(-26,20)],[(2,1,36),(-4,-1,-84),(-1,-1,-6)],[6,2,4]⟩,
  ⟨[(-24,12),(-24,18),(-26,20)],[(-1,0,-24),(-1,-1,-6),(4,1,84)],[6,2,2]⟩,
  ⟨[(-24,18),(-24,24),(-26,20)],[(-1,0,-24),(2,-1,72),(1,1,6)],[6,2,2]⟩,
  ⟨[(-12,24),(-18,24),(-20,20)],[(0,-1,24),(2,-1,60),(-1,2,-60)],[6,2,4]⟩
]
theorem targetMeshFamily0Chunk11_checked : familyCheckedB targetMeshFamily0Chunk11 = true := by decide

def targetMeshFamily0Chunk11Codes : List TriangleCode := [(40,41,104),(41,82,104),(82,39,104),(41,42,105),(42,43,105),(43,84,105),(84,41,105),(39,82,106)]
theorem targetMeshFamily0Chunk11_bound : targetMeshFamily0Chunk11.map PolygonPacket.vertices =
    targetMeshFamily0Chunk11Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0Chunk12 : List PolygonPacket := [
  ⟨[(-18,24),(-24,24),(-20,20)],[(0,-1,24),(1,1,0),(-2,1,-60)],[6,4,2]⟩,
  ⟨[(-24,24),(-24,18),(-20,20)],[(1,0,24),(-1,2,-60),(-1,-1,0)],[6,2,4]⟩,
  ⟨[(-24,18),(-24,12),(-20,20)],[(1,0,24),(-2,1,-60),(1,-2,60)],[6,4,2]⟩,
  ⟨[(-24,12),(-18,18),(-20,20)],[(-1,1,-36),(-1,-1,0),(2,-1,60)],[6,2,4]⟩,
  ⟨[(-18,18),(-12,24),(-20,20)],[(-1,1,-36),(1,-2,60),(1,1,0)],[6,4,2]⟩,
  ⟨[(-12,24),(-18,18),(-20,12)],[(1,-1,36),(3,-1,72),(-3,2,-84)],[6,2,4]⟩,
  ⟨[(-18,18),(-24,12),(-20,12)],[(1,-1,36),(0,1,-12),(-3,1,-72)],[6,4,2]⟩,
  ⟨[(-24,12),(-24,6),(-20,12)],[(1,0,24),(-3,2,-84),(0,-1,12)],[6,2,4]⟩
]
theorem targetMeshFamily0Chunk12_checked : familyCheckedB targetMeshFamily0Chunk12 = true := by decide

def targetMeshFamily0Chunk12Codes : List TriangleCode := [(82,41,106),(41,84,106),(84,43,106),(43,83,106),(83,39,106),(39,83,107),(83,43,107),(43,45,107)]
theorem targetMeshFamily0Chunk12_bound : targetMeshFamily0Chunk12.map PolygonPacket.vertices =
    targetMeshFamily0Chunk12Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0Chunk13 : List PolygonPacket := [
  ⟨[(-24,6),(-24,0),(-20,12)],[(1,0,24),(-3,1,-72),(3,-2,84)],[6,4,2]⟩,
  ⟨[(-24,0),(-18,12),(-20,12)],[(-2,1,-48),(0,-1,12),(3,-1,72)],[6,2,4]⟩,
  ⟨[(-18,12),(-12,24),(-20,12)],[(-2,1,-48),(3,-2,84),(0,1,-12)],[6,4,2]⟩,
  ⟨[(-12,24),(-18,12),(-20,6)],[(2,-1,48),(3,-1,66),(-9,4,-204)],[6,2,2]⟩,
  ⟨[(-18,12),(-24,0),(-20,6)],[(2,-1,48),(-3,2,-72),(-3,1,-66)],[6,2,2]⟩,
  ⟨[(-24,0),(-24,-6),(-20,6)],[(1,0,24),(-3,1,-66),(3,-2,72)],[6,4,2]⟩,
  ⟨[(-24,-6),(-18,9),(-20,6)],[(-5,2,-108),(3,-2,72),(3,-1,66)],[3,1,4]⟩,
  ⟨[(-18,9),(-12,24),(-20,6)],[(-5,2,-108),(9,-4,204),(-3,2,-72)],[3,2,1]⟩
]
theorem targetMeshFamily0Chunk13_checked : familyCheckedB targetMeshFamily0Chunk13 = true := by decide

def targetMeshFamily0Chunk13Codes : List TriangleCode := [(45,1,107),(1,44,107),(44,39,107),(39,44,108),(44,1,108),(1,2,108),(2,47,108),(47,39,108)]
theorem targetMeshFamily0Chunk13_bound : targetMeshFamily0Chunk13.map PolygonPacket.vertices =
    targetMeshFamily0Chunk13Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0Chunk14 : List PolygonPacket := [
  ⟨[(-6,30),(-12,24),(-14,16)],[(1,-1,36),(4,-1,72),(-7,4,-162)],[6,2,2]⟩,
  ⟨[(-12,24),(-18,9),(-14,16)],[(5,-2,108),(-7,4,-162),(-4,1,-72)],[3,1,2]⟩,
  ⟨[(-18,9),(-24,-6),(-14,16)],[(5,-2,108),(-11,5,-234),(7,-4,162)],[3,2,1]⟩,
  ⟨[(-24,-6),(-15,12),(-14,16)],[(-2,1,-42),(-4,1,-72),(11,-5,234)],[9,1,2]⟩,
  ⟨[(-15,12),(-6,30),(-14,16)],[(-2,1,-42),(7,-4,162),(4,-1,72)],[9,2,1]⟩,
  ⟨[(-6,30),(-15,12),(-18,4)],[(2,-1,42),(8,-3,156),(-13,6,-258)],[9,1,2]⟩,
  ⟨[(-15,12),(-24,-6),(-18,4)],[(2,-1,42),(-5,3,-102),(-8,3,-156)],[9,2,1]⟩,
  ⟨[(-24,-6),(-24,-12),(-18,4)],[(1,0,24),(-8,3,-156),(5,-3,102)],[6,2,2]⟩
]
theorem targetMeshFamily0Chunk14_checked : familyCheckedB targetMeshFamily0Chunk14 = true := by decide

def targetMeshFamily0Chunk14Codes : List TriangleCode := [(38,39,109),(39,47,109),(47,2,109),(2,46,109),(46,38,109),(38,46,110),(46,2,110),(2,3,110)]
theorem targetMeshFamily0Chunk14_bound : targetMeshFamily0Chunk14.map PolygonPacket.vertices =
    targetMeshFamily0Chunk14Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0Chunk15 : List PolygonPacket := [
  ⟨[(-24,-12),(-15,9),(-18,4)],[(-7,3,-132),(5,-3,102),(8,-3,156)],[3,1,2]⟩,
  ⟨[(-15,9),(-6,30),(-18,4)],[(-7,3,-132),(13,-6,258),(-5,3,-102)],[3,2,1]⟩,
  ⟨[(-6,30),(-15,9),(-16,0)],[(7,-3,132),(9,-1,144),(-3,1,-48)],[3,1,10]⟩,
  ⟨[(-15,9),(-24,-12),(-16,0)],[(7,-3,132),(-3,2,-48),(-9,1,-144)],[3,4,1]⟩,
  ⟨[(-24,-12),(-18,-18),(-16,0)],[(1,1,36),(-9,1,-144),(3,-2,48)],[6,2,4]⟩,
  ⟨[(-18,-18),(-12,6),(-16,0)],[(-4,1,-54),(3,-2,48),(9,-1,144)],[6,2,2]⟩,
  ⟨[(-12,6),(-6,30),(-16,0)],[(-4,1,-54),(3,-1,48),(-3,2,-48)],[6,10,2]⟩,
  ⟨[(-6,30),(-12,6),(-6,-12)],[(4,-1,54),(3,1,30),(-1,0,-6)],[6,6,42]⟩
]
theorem targetMeshFamily0Chunk15_checked : familyCheckedB targetMeshFamily0Chunk15 = true := by decide

def targetMeshFamily0Chunk15Codes : List TriangleCode := [(3,48,110),(48,38,110),(38,48,111),(48,3,111),(3,4,111),(4,54,111),(54,38,111),(38,54,112)]
theorem targetMeshFamily0Chunk15_bound : targetMeshFamily0Chunk15.map PolygonPacket.vertices =
    targetMeshFamily0Chunk15Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0Chunk16 : List PolygonPacket := [
  ⟨[(-12,6),(-18,-18),(-6,-12)],[(4,-1,54),(-1,2,18),(-3,-1,-30)],[6,6,6]⟩,
  ⟨[(-18,-18),(-6,-33),(-6,-12)],[(5,4,162),(-1,0,-6),(1,-2,-18)],[3,21,6]⟩,
  ⟨[(-6,-33),(6,-48),(-6,-12)],[(5,4,162),(-3,-1,-30),(1,0,6)],[3,12,21]⟩,
  ⟨[(6,-48),(0,-9),(-6,-12)],[(-13,-2,-18),(1,-2,-18),(3,1,30)],[3,3,12]⟩,
  ⟨[(0,-9),(-6,30),(-6,-12)],[(-13,-2,-18),(1,0,6),(-1,2,18)],[3,42,3]⟩,
  ⟨[(6,-48),(15,-54),(16,-54)],[(2,3,132),(0,1,54),(-3,-5,-222)],[3,1,2]⟩,
  ⟨[(15,-54),(24,-60),(16,-54)],[(2,3,132),(-3,-4,-168),(0,-1,-54)],[3,2,1]⟩,
  ⟨[(24,-60),(18,-54),(16,-54)],[(-1,-1,-36),(0,-1,-54),(3,4,168)],[6,2,2]⟩
]
theorem targetMeshFamily0Chunk16_checked : familyCheckedB targetMeshFamily0Chunk16 = true := by decide

def targetMeshFamily0Chunk16Codes : List TriangleCode := [(54,4,112),(4,53,112),(53,10,112),(10,58,112),(58,38,112),(10,56,113),(56,13,113),(13,14,113)]
theorem targetMeshFamily0Chunk16_bound : targetMeshFamily0Chunk16.map PolygonPacket.vertices =
    targetMeshFamily0Chunk16Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0Chunk17 : List PolygonPacket := [
  ⟨[(18,-54),(12,-51),(16,-54)],[(-1,-2,-90),(3,4,168),(0,1,54)],[3,1,2]⟩,
  ⟨[(12,-51),(6,-48),(16,-54)],[(-1,-2,-90),(3,5,222),(-3,-4,-168)],[3,2,1]⟩,
  ⟨[(-6,30),(0,-9),(6,-24)],[(13,2,18),(5,2,18),(-9,-2,6)],[3,3,6]⟩,
  ⟨[(0,-9),(6,-48),(6,-24)],[(13,2,18),(-1,0,6),(-5,-2,-18)],[3,24,3]⟩,
  ⟨[(6,-48),(12,-51),(6,-24)],[(1,2,90),(-9,-2,6),(1,0,-6)],[3,3,24]⟩,
  ⟨[(12,-51),(18,-54),(6,-24)],[(1,2,90),(-5,-2,-18),(9,2,-6)],[3,6,3]⟩,
  ⟨[(18,-54),(6,-12),(6,-24)],[(-7,-2,18),(1,0,-6),(5,2,18)],[6,12,6]⟩,
  ⟨[(6,-12),(-6,30),(6,-24)],[(-7,-2,18),(9,2,-6),(-1,0,6)],[6,6,12]⟩
]
theorem targetMeshFamily0Chunk17_checked : familyCheckedB targetMeshFamily0Chunk17 = true := by decide

def targetMeshFamily0Chunk17Codes : List TriangleCode := [(14,57,113),(57,10,113),(38,58,114),(58,10,114),(10,57,114),(57,14,114),(14,59,114),(59,38,114)]
theorem targetMeshFamily0Chunk17_bound : targetMeshFamily0Chunk17.map PolygonPacket.vertices =
    targetMeshFamily0Chunk17Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0Chunk18 : List PolygonPacket := [
  ⟨[(-6,30),(6,-12),(12,-24)],[(7,2,-18),(2,1,0),(-3,-1,12)],[6,6,18]⟩,
  ⟨[(6,-12),(18,-54),(12,-24)],[(7,2,-18),(-5,-1,36),(-2,-1,0)],[6,6,6]⟩,
  ⟨[(18,-54),(24,-48),(12,-24)],[(-1,1,72),(-2,-1,0),(5,1,-36)],[6,12,6]⟩,
  ⟨[(24,-48),(9,-9),(12,-24)],[(-13,-5,72),(5,1,-36),(2,1,0)],[3,3,12]⟩,
  ⟨[(9,-9),(-6,30),(12,-24)],[(-13,-5,72),(3,1,-12),(-5,-1,36)],[3,18,3]⟩,
  ⟨[(-6,30),(9,-9),(18,-22)],[(13,5,-72),(13,9,-36),(-13,-6,102)],[3,1,4]⟩,
  ⟨[(9,-9),(24,-48),(18,-22)],[(13,5,-72),(-13,-3,168),(-13,-9,36)],[3,2,1]⟩,
  ⟨[(24,-48),(30,-48),(18,-22)],[(0,1,48),(-13,-6,102),(13,3,-168)],[6,2,2]⟩
]
theorem targetMeshFamily0Chunk18_checked : familyCheckedB targetMeshFamily0Chunk18 = true := by decide

def targetMeshFamily0Chunk18Codes : List TriangleCode := [(38,59,115),(59,14,115),(14,15,115),(15,61,115),(61,38,115),(38,61,116),(61,15,116),(15,60,116)]
theorem targetMeshFamily0Chunk18_bound : targetMeshFamily0Chunk18.map PolygonPacket.vertices =
    targetMeshFamily0Chunk18Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0Chunk19 : List PolygonPacket := [
  ⟨[(30,-48),(36,-48),(18,-22)],[(0,1,48),(-13,-9,36),(13,6,-102)],[6,2,2]⟩,
  ⟨[(36,-48),(15,-9),(18,-22)],[(-13,-7,132),(13,3,-168),(13,9,-36)],[3,1,2]⟩,
  ⟨[(15,-9),(-6,30),(18,-22)],[(-13,-7,132),(13,6,-102),(-13,-3,168)],[3,4,1]⟩,
  ⟨[(-6,30),(15,-9),(24,-22)],[(13,7,-132),(13,9,-114),(-26,-15,294)],[3,1,2]⟩,
  ⟨[(15,-9),(36,-48),(24,-22)],[(13,7,-132),(-13,-6,180),(-13,-9,114)],[3,2,1]⟩,
  ⟨[(36,-48),(42,-48),(24,-22)],[(0,1,48),(-13,-9,114),(13,6,-180)],[6,2,2]⟩,
  ⟨[(42,-48),(18,-9),(24,-22)],[(-13,-8,162),(13,6,-180),(13,9,-114)],[3,1,2]⟩,
  ⟨[(18,-9),(-6,30),(24,-22)],[(-13,-8,162),(26,15,-294),(-13,-6,180)],[3,2,1]⟩
]
theorem targetMeshFamily0Chunk19_checked : familyCheckedB targetMeshFamily0Chunk19 = true := by decide

def targetMeshFamily0Chunk19Codes : List TriangleCode := [(60,17,116),(17,62,116),(62,38,116),(38,62,117),(62,17,117),(17,18,117),(18,63,117),(63,38,117)]
theorem targetMeshFamily0Chunk19_bound : targetMeshFamily0Chunk19.map PolygonPacket.vertices =
    targetMeshFamily0Chunk19Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0Chunk20 : List PolygonPacket := [
  ⟨[(-6,30),(18,-9),(28,-22)],[(13,8,-162),(13,10,-144),(-26,-17,354)],[3,1,2]⟩,
  ⟨[(18,-9),(42,-48),(28,-22)],[(13,8,-162),(-13,-7,210),(-13,-10,144)],[3,2,1]⟩,
  ⟨[(42,-48),(48,-48),(28,-22)],[(0,1,48),(-13,-10,144),(13,7,-210)],[6,2,2]⟩,
  ⟨[(48,-48),(21,-9),(28,-22)],[(-13,-9,192),(13,7,-210),(13,10,-144)],[3,1,2]⟩,
  ⟨[(21,-9),(-6,30),(28,-22)],[(-13,-9,192),(26,17,-354),(-13,-7,210)],[3,2,1]⟩,
  ⟨[(-6,30),(21,-9),(30,-20)],[(13,9,-192),(11,9,-150),(-25,-18,390)],[3,1,2]⟩,
  ⟨[(21,-9),(48,-48),(30,-20)],[(13,9,-192),(-14,-9,240),(-11,-9,150)],[3,2,1]⟩,
  ⟨[(48,-48),(48,-42),(30,-20)],[(-1,0,48),(-11,-9,150),(14,9,-240)],[6,2,2]⟩
]
theorem targetMeshFamily0Chunk20_checked : familyCheckedB targetMeshFamily0Chunk20 = true := by decide

def targetMeshFamily0Chunk20Codes : List TriangleCode := [(38,63,118),(63,18,118),(18,19,118),(19,64,118),(64,38,118),(38,64,119),(64,19,119),(19,20,119)]
theorem targetMeshFamily0Chunk20_bound : targetMeshFamily0Chunk20.map PolygonPacket.vertices =
    targetMeshFamily0Chunk20Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0Chunk21 : List PolygonPacket := [
  ⟨[(48,-42),(21,-6),(30,-20)],[(-4,-3,66),(14,9,-240),(11,9,-150)],[9,1,2]⟩,
  ⟨[(21,-6),(-6,30),(30,-20)],[(-4,-3,66),(25,18,-390),(-14,-9,240)],[9,2,1]⟩,
  ⟨[(48,-42),(54,-39),(54,-38)],[(-1,2,132),(-1,0,54),(2,-3,-222)],[3,1,2]⟩,
  ⟨[(54,-39),(60,-36),(54,-38)],[(-1,2,132),(1,-3,-168),(1,0,-54)],[3,2,1]⟩,
  ⟨[(60,-36),(54,-36),(54,-38)],[(0,-1,-36),(1,0,-54),(-1,3,168)],[6,2,2]⟩,
  ⟨[(54,-36),(51,-39),(54,-38)],[(1,-1,-90),(-1,3,168),(-1,0,54)],[3,1,2]⟩,
  ⟨[(51,-39),(48,-42),(54,-38)],[(1,-1,-90),(-2,3,222),(1,-3,-168)],[3,2,1]⟩,
  ⟨[(48,-42),(51,-39),(46,-32)],[(-1,1,90),(-7,-5,162),(5,1,-198)],[3,1,2]⟩
]
theorem targetMeshFamily0Chunk21_checked : familyCheckedB targetMeshFamily0Chunk21 = true := by decide

def targetMeshFamily0Chunk21Codes : List TriangleCode := [(20,69,119),(69,38,119),(20,66,120),(66,23,120),(23,24,120),(24,67,120),(67,20,120),(20,67,121)]
theorem targetMeshFamily0Chunk21_bound : targetMeshFamily0Chunk21.map PolygonPacket.vertices =
    targetMeshFamily0Chunk21Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0Chunk22 : List PolygonPacket := [
  ⟨[(51,-39),(54,-36),(46,-32)],[(-1,1,90),(-1,-2,-18),(7,5,-162)],[3,4,1]⟩,
  ⟨[(54,-36),(45,-27),(46,-32)],[(-1,-1,18),(5,1,-198),(1,2,18)],[9,1,4]⟩,
  ⟨[(45,-27),(36,-18),(46,-32)],[(-1,-1,18),(7,5,-162),(-5,-1,198)],[9,2,1]⟩,
  ⟨[(36,-18),(42,-30),(46,-32)],[(2,1,-54),(1,2,18),(-7,-5,162)],[6,2,2]⟩,
  ⟨[(42,-30),(48,-42),(46,-32)],[(2,1,-54),(-5,-1,198),(-1,-2,-18)],[6,2,2]⟩,
  ⟨[(-6,30),(21,-6),(26,-10)],[(4,3,-66),(4,5,-54),(-5,-4,90)],[9,1,8]⟩,
  ⟨[(21,-6),(48,-42),(26,-10)],[(4,3,-66),(-16,-11,306),(-4,-5,54)],[9,2,1]⟩,
  ⟨[(48,-42),(42,-30),(26,-10)],[(-2,-1,54),(-5,-4,90),(16,11,-306)],[6,4,2]⟩
]
theorem targetMeshFamily0Chunk22_checked : familyCheckedB targetMeshFamily0Chunk22 = true := by decide

def targetMeshFamily0Chunk22Codes : List TriangleCode := [(67,24,121),(24,70,121),(70,26,121),(26,68,121),(68,20,121),(38,69,122),(69,20,122),(20,68,122)]
theorem targetMeshFamily0Chunk22_bound : targetMeshFamily0Chunk22.map PolygonPacket.vertices =
    targetMeshFamily0Chunk22Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0Chunk23 : List PolygonPacket := [
  ⟨[(42,-30),(36,-18),(26,-10)],[(-2,-1,54),(-4,-5,54),(5,4,-90)],[6,2,4]⟩,
  ⟨[(36,-18),(15,6),(26,-10)],[(-8,-7,162),(16,11,-306),(4,5,-54)],[3,1,2]⟩,
  ⟨[(15,6),(-6,30),(26,-10)],[(-8,-7,162),(5,4,-90),(-16,-11,306)],[3,8,1]⟩,
  ⟨[(36,-18),(36,-12),(34,-12)],[(-1,0,36),(0,-1,-12),(3,1,-90)],[6,2,2]⟩,
  ⟨[(36,-12),(30,-6),(34,-12)],[(-1,-1,24),(3,2,-78),(0,1,12)],[6,2,2]⟩,
  ⟨[(30,-6),(33,-12),(34,-12)],[(2,1,-54),(0,1,12),(-3,-2,78)],[3,1,2]⟩,
  ⟨[(33,-12),(36,-18),(34,-12)],[(2,1,-54),(-3,-1,90),(0,-1,-12)],[3,2,1]⟩,
  ⟨[(-6,30),(15,6),(20,2)],[(8,7,-162),(4,5,-90),(-14,-13,306)],[3,1,2]⟩
]
theorem targetMeshFamily0Chunk23_checked : familyCheckedB targetMeshFamily0Chunk23 = true := by decide

def targetMeshFamily0Chunk23Codes : List TriangleCode := [(68,26,122),(26,72,122),(72,38,122),(26,27,123),(27,28,123),(28,71,123),(71,26,123),(38,72,124)]
theorem targetMeshFamily0Chunk23_bound : targetMeshFamily0Chunk23.map PolygonPacket.vertices =
    targetMeshFamily0Chunk23Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0Chunk24 : List PolygonPacket := [
  ⟨[(15,6),(36,-18),(20,2)],[(8,7,-162),(-5,-4,108),(-4,-5,90)],[3,4,1]⟩,
  ⟨[(36,-18),(33,-12),(20,2)],[(-2,-1,54),(-14,-13,306),(5,4,-108)],[3,1,4]⟩,
  ⟨[(33,-12),(30,-6),(20,2)],[(-2,-1,54),(-4,-5,90),(14,13,-306)],[3,2,1]⟩,
  ⟨[(30,-6),(12,12),(20,2)],[(-1,-1,24),(5,4,-108),(4,5,-90)],[18,2,2]⟩,
  ⟨[(12,12),(-6,30),(20,2)],[(-1,-1,24),(14,13,-306),(-5,-4,108)],[18,2,2]⟩,
  ⟨[(-6,30),(12,12),(10,16)],[(1,1,-24),(-2,-1,36),(-7,-8,198)],[18,2,2]⟩,
  ⟨[(12,12),(30,-6),(10,16)],[(1,1,-24),(-11,-10,270),(2,1,-36)],[18,2,2]⟩,
  ⟨[(30,-6),(18,9),(10,16)],[(-5,-4,126),(-7,-8,198),(11,10,-270)],[3,1,2]⟩
]
theorem targetMeshFamily0Chunk24_checked : familyCheckedB targetMeshFamily0Chunk24 = true := by decide

def targetMeshFamily0Chunk24Codes : List TriangleCode := [(72,26,124),(26,71,124),(71,28,124),(28,78,124),(78,38,124),(38,78,125),(78,28,125),(28,77,125)]
theorem targetMeshFamily0Chunk24_bound : targetMeshFamily0Chunk24.map PolygonPacket.vertices =
    targetMeshFamily0Chunk24Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0Chunk25 : List PolygonPacket := [
  ⟨[(18,9),(6,24),(10,16)],[(-5,-4,126),(2,1,-36),(7,8,-198)],[3,4,1]⟩,
  ⟨[(6,24),(0,27),(10,16)],[(-1,-2,54),(11,10,-270),(-2,-1,36)],[3,1,4]⟩,
  ⟨[(0,27),(-6,30),(10,16)],[(-1,-2,54),(7,8,-198),(-11,-10,270)],[3,2,1]⟩,
  ⟨[(6,24),(-3,30),(-4,30)],[(-2,-3,84),(0,-1,30),(3,5,-138)],[3,1,2]⟩,
  ⟨[(-3,30),(-12,36),(-4,30)],[(-2,-3,84),(3,4,-108),(0,1,-30)],[3,2,1]⟩,
  ⟨[(-12,36),(-6,30),(-4,30)],[(1,1,-24),(0,1,-30),(-3,-4,108)],[6,2,2]⟩,
  ⟨[(-6,30),(0,27),(-4,30)],[(1,2,-54),(-3,-4,108),(0,-1,30)],[3,1,2]⟩,
  ⟨[(0,27),(6,24),(-4,30)],[(1,2,-54),(-3,-5,138),(3,4,-108)],[3,2,1]⟩
]
theorem targetMeshFamily0Chunk25_checked : familyCheckedB targetMeshFamily0Chunk25 = true := by decide

def targetMeshFamily0Chunk25Codes : List TriangleCode := [(77,34,125),(34,81,125),(81,38,125),(34,80,126),(80,37,126),(37,38,126),(38,81,126),(81,34,126)]
theorem targetMeshFamily0Chunk25_bound : targetMeshFamily0Chunk25.map PolygonPacket.vertices =
    targetMeshFamily0Chunk25Codes.map (triangleVertexList (targetVertices 0)) := by decide

def targetMeshFamily0 : List PolygonPacket := targetMeshFamily0Chunk0 ++ targetMeshFamily0Chunk1 ++ targetMeshFamily0Chunk2 ++ targetMeshFamily0Chunk3 ++ targetMeshFamily0Chunk4 ++ targetMeshFamily0Chunk5 ++ targetMeshFamily0Chunk6 ++ targetMeshFamily0Chunk7 ++ targetMeshFamily0Chunk8 ++ targetMeshFamily0Chunk9 ++ targetMeshFamily0Chunk10 ++ targetMeshFamily0Chunk11 ++ targetMeshFamily0Chunk12 ++ targetMeshFamily0Chunk13 ++ targetMeshFamily0Chunk14 ++ targetMeshFamily0Chunk15 ++ targetMeshFamily0Chunk16 ++ targetMeshFamily0Chunk17 ++ targetMeshFamily0Chunk18 ++ targetMeshFamily0Chunk19 ++ targetMeshFamily0Chunk20 ++ targetMeshFamily0Chunk21 ++ targetMeshFamily0Chunk22 ++ targetMeshFamily0Chunk23 ++ targetMeshFamily0Chunk24 ++ targetMeshFamily0Chunk25
theorem targetMeshFamily0_checked : familyCheckedB targetMeshFamily0 = true := by
  have h : familyCheckedB targetMeshFamily0Chunk0 = true ∧ familyCheckedB targetMeshFamily0Chunk1 = true ∧ familyCheckedB targetMeshFamily0Chunk2 = true ∧ familyCheckedB targetMeshFamily0Chunk3 = true ∧ familyCheckedB targetMeshFamily0Chunk4 = true ∧ familyCheckedB targetMeshFamily0Chunk5 = true ∧ familyCheckedB targetMeshFamily0Chunk6 = true ∧ familyCheckedB targetMeshFamily0Chunk7 = true ∧ familyCheckedB targetMeshFamily0Chunk8 = true ∧ familyCheckedB targetMeshFamily0Chunk9 = true ∧ familyCheckedB targetMeshFamily0Chunk10 = true ∧ familyCheckedB targetMeshFamily0Chunk11 = true ∧ familyCheckedB targetMeshFamily0Chunk12 = true ∧ familyCheckedB targetMeshFamily0Chunk13 = true ∧ familyCheckedB targetMeshFamily0Chunk14 = true ∧ familyCheckedB targetMeshFamily0Chunk15 = true ∧ familyCheckedB targetMeshFamily0Chunk16 = true ∧ familyCheckedB targetMeshFamily0Chunk17 = true ∧ familyCheckedB targetMeshFamily0Chunk18 = true ∧ familyCheckedB targetMeshFamily0Chunk19 = true ∧ familyCheckedB targetMeshFamily0Chunk20 = true ∧ familyCheckedB targetMeshFamily0Chunk21 = true ∧ familyCheckedB targetMeshFamily0Chunk22 = true ∧ familyCheckedB targetMeshFamily0Chunk23 = true ∧ familyCheckedB targetMeshFamily0Chunk24 = true ∧ familyCheckedB targetMeshFamily0Chunk25 = true := by
    exact ⟨targetMeshFamily0Chunk0_checked, targetMeshFamily0Chunk1_checked, targetMeshFamily0Chunk2_checked, targetMeshFamily0Chunk3_checked, targetMeshFamily0Chunk4_checked, targetMeshFamily0Chunk5_checked, targetMeshFamily0Chunk6_checked, targetMeshFamily0Chunk7_checked, targetMeshFamily0Chunk8_checked, targetMeshFamily0Chunk9_checked, targetMeshFamily0Chunk10_checked, targetMeshFamily0Chunk11_checked, targetMeshFamily0Chunk12_checked, targetMeshFamily0Chunk13_checked, targetMeshFamily0Chunk14_checked, targetMeshFamily0Chunk15_checked, targetMeshFamily0Chunk16_checked, targetMeshFamily0Chunk17_checked, targetMeshFamily0Chunk18_checked, targetMeshFamily0Chunk19_checked, targetMeshFamily0Chunk20_checked, targetMeshFamily0Chunk21_checked, targetMeshFamily0Chunk22_checked, targetMeshFamily0Chunk23_checked, targetMeshFamily0Chunk24_checked, targetMeshFamily0Chunk25_checked⟩
  simpa only [targetMeshFamily0,familyCheckedB,List.all_append,Bool.and_eq_true,and_assoc] using h

def targetCodes0 : List TriangleCode := targetMeshFamily0Chunk0Codes ++ targetMeshFamily0Chunk1Codes ++ targetMeshFamily0Chunk2Codes ++ targetMeshFamily0Chunk3Codes ++ targetMeshFamily0Chunk4Codes ++ targetMeshFamily0Chunk5Codes ++ targetMeshFamily0Chunk6Codes ++ targetMeshFamily0Chunk7Codes ++ targetMeshFamily0Chunk8Codes ++ targetMeshFamily0Chunk9Codes ++ targetMeshFamily0Chunk10Codes ++ targetMeshFamily0Chunk11Codes ++ targetMeshFamily0Chunk12Codes ++ targetMeshFamily0Chunk13Codes ++ targetMeshFamily0Chunk14Codes ++ targetMeshFamily0Chunk15Codes ++ targetMeshFamily0Chunk16Codes ++ targetMeshFamily0Chunk17Codes ++ targetMeshFamily0Chunk18Codes ++ targetMeshFamily0Chunk19Codes ++ targetMeshFamily0Chunk20Codes ++ targetMeshFamily0Chunk21Codes ++ targetMeshFamily0Chunk22Codes ++ targetMeshFamily0Chunk23Codes ++ targetMeshFamily0Chunk24Codes ++ targetMeshFamily0Chunk25Codes
theorem targetCodes0_bound : targetCodes0 = meshTriangles 0 := by decide
theorem targetMeshFamily0_vertices_bound : targetMeshFamily0.map PolygonPacket.vertices =
    (meshTriangles 0).map (triangleVertexList (targetVertices 0)) := by
  rw [←targetCodes0_bound]
  simp only [targetMeshFamily0,targetCodes0,List.map_append,targetMeshFamily0Chunk0_bound,targetMeshFamily0Chunk1_bound,targetMeshFamily0Chunk2_bound,targetMeshFamily0Chunk3_bound,targetMeshFamily0Chunk4_bound,targetMeshFamily0Chunk5_bound,targetMeshFamily0Chunk6_bound,targetMeshFamily0Chunk7_bound,targetMeshFamily0Chunk8_bound,targetMeshFamily0Chunk9_bound,targetMeshFamily0Chunk10_bound,targetMeshFamily0Chunk11_bound,targetMeshFamily0Chunk12_bound,targetMeshFamily0Chunk13_bound,targetMeshFamily0Chunk14_bound,targetMeshFamily0Chunk15_bound,targetMeshFamily0Chunk16_bound,targetMeshFamily0Chunk17_bound,targetMeshFamily0Chunk18_bound,targetMeshFamily0Chunk19_bound,targetMeshFamily0Chunk20_bound,targetMeshFamily0Chunk21_bound,targetMeshFamily0Chunk22_bound,targetMeshFamily0Chunk23_bound,targetMeshFamily0Chunk24_bound,targetMeshFamily0Chunk25_bound]

theorem targetKiteFamily0_vertices_bound : targetKiteFamily0.map PolygonPacket.vertices =
    (clusterCells .t7h).map (fun c => (cellVertices c).map (scalePoint 6)) := by decide

end SpectreGeometry.ReverseClusterTriangulation
