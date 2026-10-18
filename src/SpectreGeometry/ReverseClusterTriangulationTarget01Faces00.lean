module

public import SpectreGeometry.ReverseClusterTriangulationTarget01Data
public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def target1FaceCodes0 : List Nat := []
theorem target1FaceRow0_checked : packetFaceRowB (targetMeshFamily1Chunk0.getD 0 default)
    (targetMeshFamily1.take 0) target1FaceCodes0 = true := by decide

def target1FaceCodes1 : List Nat := [2]
theorem target1FaceRow1_checked : packetFaceRowB (targetMeshFamily1Chunk0.getD 1 default)
    (targetMeshFamily1.take 1) target1FaceCodes1 = true := by decide

def target1FaceCodes2 : List Nat := [5, 2]
theorem target1FaceRow2_checked : packetFaceRowB (targetMeshFamily1Chunk0.getD 2 default)
    (targetMeshFamily1.take 2) target1FaceCodes2 = true := by decide

def target1FaceCodes3 : List Nat := [1, 4, 2]
theorem target1FaceRow3_checked : packetFaceRowB (targetMeshFamily1Chunk0.getD 3 default)
    (targetMeshFamily1.take 3) target1FaceCodes3 = true := by decide

def target1FaceCodes4 : List Nat := [0, 1, 1, 0]
theorem target1FaceRow4_checked : packetFaceRowB (targetMeshFamily1Chunk0.getD 4 default)
    (targetMeshFamily1.take 4) target1FaceCodes4 = true := by decide

def target1FaceCodes5 : List Nat := [5, 0, 0, 5, 2]
theorem target1FaceRow5_checked : packetFaceRowB (targetMeshFamily1Chunk0.getD 5 default)
    (targetMeshFamily1.take 5) target1FaceCodes5 = true := by decide

def target1FaceCodes6 : List Nat := [2, 2, 2, 2, 2, 2]
theorem target1FaceRow6_checked : packetFaceRowB (targetMeshFamily1Chunk0.getD 6 default)
    (targetMeshFamily1.take 6) target1FaceCodes6 = true := by decide

def target1FaceCodes7 : List Nat := [1, 2, 3, 1, 1, 6, 2]
theorem target1FaceRow7_checked : packetFaceRowB (targetMeshFamily1Chunk0.getD 7 default)
    (targetMeshFamily1.take 7) target1FaceCodes7 = true := by decide

def target1FaceCodes8 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2]
theorem target1FaceRow8_checked : packetFaceRowB (targetMeshFamily1Chunk1.getD 0 default)
    (targetMeshFamily1.take 8) target1FaceCodes8 = true := by decide

def target1FaceCodes9 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem target1FaceRow9_checked : packetFaceRowB (targetMeshFamily1Chunk1.getD 1 default)
    (targetMeshFamily1.take 9) target1FaceCodes9 = true := by decide

def target1FaceCodes10 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 1, 2]
theorem target1FaceRow10_checked : packetFaceRowB (targetMeshFamily1Chunk1.getD 2 default)
    (targetMeshFamily1.take 10) target1FaceCodes10 = true := by decide

def target1FaceCodes11 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2]
theorem target1FaceRow11_checked : packetFaceRowB (targetMeshFamily1Chunk1.getD 3 default)
    (targetMeshFamily1.take 11) target1FaceCodes11 = true := by decide

def target1FaceCodes12 : List Nat := [4, 1, 1, 3, 5, 1, 1, 1, 3, 1, 4, 2]
theorem target1FaceRow12_checked : packetFaceRowB (targetMeshFamily1Chunk1.getD 4 default)
    (targetMeshFamily1.take 12) target1FaceCodes12 = true := by decide

def target1FaceCodes13 : List Nat := [4, 0, 0, 2, 5, 0, 0, 3, 3, 0, 1, 1, 0]
theorem target1FaceRow13_checked : packetFaceRowB (targetMeshFamily1Chunk1.getD 5 default)
    (targetMeshFamily1.take 13) target1FaceCodes13 = true := by decide

def target1FaceCodes14 : List Nat := [2, 0, 0, 2, 2, 0, 0, 2, 2, 5, 0, 0, 5, 2]
theorem target1FaceRow14_checked : packetFaceRowB (targetMeshFamily1Chunk1.getD 6 default)
    (targetMeshFamily1.take 14) target1FaceCodes14 = true := by decide

def target1FaceCodes15 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem target1FaceRow15_checked : packetFaceRowB (targetMeshFamily1Chunk1.getD 7 default)
    (targetMeshFamily1.take 15) target1FaceCodes15 = true := by decide

def target1FaceCodes16 : List Nat := [0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 2, 3, 1, 1, 6, 2]
theorem target1FaceRow16_checked : packetFaceRowB (targetMeshFamily1Chunk2.getD 0 default)
    (targetMeshFamily1.take 16) target1FaceCodes16 = true := by decide

def target1FaceCodes17 : List Nat := [0, 4, 3, 0, 0, 4, 1, 3, 0, 1, 1, 1, 1, 1, 1, 4, 2]
theorem target1FaceRow17_checked : packetFaceRowB (targetMeshFamily1Chunk2.getD 1 default)
    (targetMeshFamily1.take 17) target1FaceCodes17 = true := by decide

def target1FaceCodes18 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem target1FaceRow18_checked : packetFaceRowB (targetMeshFamily1Chunk2.getD 2 default)
    (targetMeshFamily1.take 18) target1FaceCodes18 = true := by decide

def target1FaceCodes19 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem target1FaceRow19_checked : packetFaceRowB (targetMeshFamily1Chunk2.getD 3 default)
    (targetMeshFamily1.take 19) target1FaceCodes19 = true := by decide

def target1FaceCodes20 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2]
theorem target1FaceRow20_checked : packetFaceRowB (targetMeshFamily1Chunk2.getD 4 default)
    (targetMeshFamily1.take 20) target1FaceCodes20 = true := by decide

def target1FaceCodes21 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2]
theorem target1FaceRow21_checked : packetFaceRowB (targetMeshFamily1Chunk2.getD 5 default)
    (targetMeshFamily1.take 21) target1FaceCodes21 = true := by decide

def target1FaceCodes22 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
theorem target1FaceRow22_checked : packetFaceRowB (targetMeshFamily1Chunk2.getD 6 default)
    (targetMeshFamily1.take 22) target1FaceCodes22 = true := by decide

def target1FaceCodes23 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 5, 2]
theorem target1FaceRow23_checked : packetFaceRowB (targetMeshFamily1Chunk2.getD 7 default)
    (targetMeshFamily1.take 23) target1FaceCodes23 = true := by decide


end SpectreGeometry.ReverseClusterTriangulation
