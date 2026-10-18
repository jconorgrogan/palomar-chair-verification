module

public import SpectreGeometry.ReverseClusterTriangulationSource03Data
public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def source3FaceCodes0 : List Nat := []
theorem source3FaceRow0_checked : packetFaceRowB (sourceFamily3Chunk0.getD 0 default)
    (sourceFamily3.take 0) source3FaceCodes0 = true := by decide

def source3FaceCodes1 : List Nat := [2]
theorem source3FaceRow1_checked : packetFaceRowB (sourceFamily3Chunk0.getD 1 default)
    (sourceFamily3.take 1) source3FaceCodes1 = true := by decide

def source3FaceCodes2 : List Nat := [1, 2]
theorem source3FaceRow2_checked : packetFaceRowB (sourceFamily3Chunk0.getD 2 default)
    (sourceFamily3.take 2) source3FaceCodes2 = true := by decide

def source3FaceCodes3 : List Nat := [1, 1, 2]
theorem source3FaceRow3_checked : packetFaceRowB (sourceFamily3Chunk0.getD 3 default)
    (sourceFamily3.take 3) source3FaceCodes3 = true := by decide

def source3FaceCodes4 : List Nat := [0, 0, 0, 0]
theorem source3FaceRow4_checked : packetFaceRowB (sourceFamily3Chunk0.getD 4 default)
    (sourceFamily3.take 4) source3FaceCodes4 = true := by decide

def source3FaceCodes5 : List Nat := [0, 0, 0, 0, 2]
theorem source3FaceRow5_checked : packetFaceRowB (sourceFamily3Chunk0.getD 5 default)
    (sourceFamily3.take 5) source3FaceCodes5 = true := by decide

def source3FaceCodes6 : List Nat := [2, 2, 2, 2, 2, 2]
theorem source3FaceRow6_checked : packetFaceRowB (sourceFamily3Chunk0.getD 6 default)
    (sourceFamily3.take 6) source3FaceCodes6 = true := by decide

def source3FaceCodes7 : List Nat := [1, 2, 2, 1, 1, 2, 2]
theorem source3FaceRow7_checked : packetFaceRowB (sourceFamily3Chunk0.getD 7 default)
    (sourceFamily3.take 7) source3FaceCodes7 = true := by decide

def source3FaceCodes8 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2]
theorem source3FaceRow8_checked : packetFaceRowB (sourceFamily3Chunk1.getD 0 default)
    (sourceFamily3.take 8) source3FaceCodes8 = true := by decide

def source3FaceCodes9 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source3FaceRow9_checked : packetFaceRowB (sourceFamily3Chunk1.getD 1 default)
    (sourceFamily3.take 9) source3FaceCodes9 = true := by decide

def source3FaceCodes10 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source3FaceRow10_checked : packetFaceRowB (sourceFamily3Chunk1.getD 2 default)
    (sourceFamily3.take 10) source3FaceCodes10 = true := by decide

def source3FaceCodes11 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2]
theorem source3FaceRow11_checked : packetFaceRowB (sourceFamily3Chunk1.getD 3 default)
    (sourceFamily3.take 11) source3FaceCodes11 = true := by decide

def source3FaceCodes12 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source3FaceRow12_checked : packetFaceRowB (sourceFamily3Chunk1.getD 4 default)
    (sourceFamily3.take 12) source3FaceCodes12 = true := by decide

def source3FaceCodes13 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source3FaceRow13_checked : packetFaceRowB (sourceFamily3Chunk1.getD 5 default)
    (sourceFamily3.take 13) source3FaceCodes13 = true := by decide

def source3FaceCodes14 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 2]
theorem source3FaceRow14_checked : packetFaceRowB (sourceFamily3Chunk1.getD 6 default)
    (sourceFamily3.take 14) source3FaceCodes14 = true := by decide

def source3FaceCodes15 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem source3FaceRow15_checked : packetFaceRowB (sourceFamily3Chunk1.getD 7 default)
    (sourceFamily3.take 15) source3FaceCodes15 = true := by decide

def source3FaceCodes16 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 1, 2, 2]
theorem source3FaceRow16_checked : packetFaceRowB (sourceFamily3Chunk2.getD 0 default)
    (sourceFamily3.take 16) source3FaceCodes16 = true := by decide

def source3FaceCodes17 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source3FaceRow17_checked : packetFaceRowB (sourceFamily3Chunk2.getD 1 default)
    (sourceFamily3.take 17) source3FaceCodes17 = true := by decide

def source3FaceCodes18 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source3FaceRow18_checked : packetFaceRowB (sourceFamily3Chunk2.getD 2 default)
    (sourceFamily3.take 18) source3FaceCodes18 = true := by decide

def source3FaceCodes19 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source3FaceRow19_checked : packetFaceRowB (sourceFamily3Chunk2.getD 3 default)
    (sourceFamily3.take 19) source3FaceCodes19 = true := by decide

def source3FaceCodes20 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2]
theorem source3FaceRow20_checked : packetFaceRowB (sourceFamily3Chunk2.getD 4 default)
    (sourceFamily3.take 20) source3FaceCodes20 = true := by decide

def source3FaceCodes21 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2]
theorem source3FaceRow21_checked : packetFaceRowB (sourceFamily3Chunk2.getD 5 default)
    (sourceFamily3.take 21) source3FaceCodes21 = true := by decide

def source3FaceCodes22 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source3FaceRow22_checked : packetFaceRowB (sourceFamily3Chunk2.getD 6 default)
    (sourceFamily3.take 22) source3FaceCodes22 = true := by decide

def source3FaceCodes23 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 2]
theorem source3FaceRow23_checked : packetFaceRowB (sourceFamily3Chunk2.getD 7 default)
    (sourceFamily3.take 23) source3FaceCodes23 = true := by decide


end SpectreGeometry.ReverseClusterTriangulation
