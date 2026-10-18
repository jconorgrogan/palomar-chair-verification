module

public import SpectreGeometry.ReverseClusterTriangulationTarget01Data
public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def target1FaceCodes216 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 3, 5, 0, 0, 0, 3, 5, 0, 0, 0, 3, 5, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 3, 5, 0, 0, 0, 3, 5, 0, 0, 0, 0, 3, 5, 0, 0, 0, 3, 5, 0, 0, 0, 3, 5, 0, 0, 0, 3, 5, 0, 0, 0, 0, 3, 5, 4, 0, 0, 3, 3, 5, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 5, 2]
theorem target1FaceRow216_checked : packetFaceRowB (targetMeshFamily1Chunk27.getD 0 default)
    (targetMeshFamily1.take 216) target1FaceCodes216 = true := by decide

def target1FaceCodes217 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 3, 0, 0, 4, 3, 0, 0, 2, 1, 1, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 2, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 5, 0, 0, 0, 3, 5, 0, 0, 0, 0, 3, 5, 0, 0, 0, 3, 5, 0, 0, 0, 3, 5, 0, 0, 0, 3, 5, 0, 0, 0, 0, 3, 5, 4, 0, 0, 3, 3, 3, 4, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 3, 5, 0, 0, 0, 0, 3, 5, 0, 0, 0, 5, 1, 4, 2]
theorem target1FaceRow217_checked : packetFaceRowB (targetMeshFamily1Chunk27.getD 1 default)
    (targetMeshFamily1.take 217) target1FaceCodes217 = true := by decide


end SpectreGeometry.ReverseClusterTriangulation
