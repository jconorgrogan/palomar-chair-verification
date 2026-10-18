module

public import SpectreGeometry.ReverseClusterTriangulationSource02Data
public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def source2FaceCodes0 : List Nat := []
theorem source2FaceRow0_checked : packetFaceRowB (sourceFamily2Chunk0.getD 0 default)
    (sourceFamily2.take 0) source2FaceCodes0 = true := by decide

def source2FaceCodes1 : List Nat := [2]
theorem source2FaceRow1_checked : packetFaceRowB (sourceFamily2Chunk0.getD 1 default)
    (sourceFamily2.take 1) source2FaceCodes1 = true := by decide

def source2FaceCodes2 : List Nat := [2, 2]
theorem source2FaceRow2_checked : packetFaceRowB (sourceFamily2Chunk0.getD 2 default)
    (sourceFamily2.take 2) source2FaceCodes2 = true := by decide

def source2FaceCodes3 : List Nat := [1, 1, 2]
theorem source2FaceRow3_checked : packetFaceRowB (sourceFamily2Chunk0.getD 3 default)
    (sourceFamily2.take 3) source2FaceCodes3 = true := by decide

def source2FaceCodes4 : List Nat := [0, 0, 0, 0]
theorem source2FaceRow4_checked : packetFaceRowB (sourceFamily2Chunk0.getD 4 default)
    (sourceFamily2.take 4) source2FaceCodes4 = true := by decide

def source2FaceCodes5 : List Nat := [0, 0, 0, 0, 2]
theorem source2FaceRow5_checked : packetFaceRowB (sourceFamily2Chunk0.getD 5 default)
    (sourceFamily2.take 5) source2FaceCodes5 = true := by decide

def source2FaceCodes6 : List Nat := [2, 2, 2, 2, 2, 2]
theorem source2FaceRow6_checked : packetFaceRowB (sourceFamily2Chunk0.getD 6 default)
    (sourceFamily2.take 6) source2FaceCodes6 = true := by decide

def source2FaceCodes7 : List Nat := [1, 2, 2, 1, 1, 2, 2]
theorem source2FaceRow7_checked : packetFaceRowB (sourceFamily2Chunk0.getD 7 default)
    (sourceFamily2.take 7) source2FaceCodes7 = true := by decide

def source2FaceCodes8 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2]
theorem source2FaceRow8_checked : packetFaceRowB (sourceFamily2Chunk1.getD 0 default)
    (sourceFamily2.take 8) source2FaceCodes8 = true := by decide

def source2FaceCodes9 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source2FaceRow9_checked : packetFaceRowB (sourceFamily2Chunk1.getD 1 default)
    (sourceFamily2.take 9) source2FaceCodes9 = true := by decide

def source2FaceCodes10 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source2FaceRow10_checked : packetFaceRowB (sourceFamily2Chunk1.getD 2 default)
    (sourceFamily2.take 10) source2FaceCodes10 = true := by decide

def source2FaceCodes11 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2]
theorem source2FaceRow11_checked : packetFaceRowB (sourceFamily2Chunk1.getD 3 default)
    (sourceFamily2.take 11) source2FaceCodes11 = true := by decide

def source2FaceCodes12 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source2FaceRow12_checked : packetFaceRowB (sourceFamily2Chunk1.getD 4 default)
    (sourceFamily2.take 12) source2FaceCodes12 = true := by decide

def source2FaceCodes13 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source2FaceRow13_checked : packetFaceRowB (sourceFamily2Chunk1.getD 5 default)
    (sourceFamily2.take 13) source2FaceCodes13 = true := by decide

def source2FaceCodes14 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 2]
theorem source2FaceRow14_checked : packetFaceRowB (sourceFamily2Chunk1.getD 6 default)
    (sourceFamily2.take 14) source2FaceCodes14 = true := by decide

def source2FaceCodes15 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem source2FaceRow15_checked : packetFaceRowB (sourceFamily2Chunk1.getD 7 default)
    (sourceFamily2.take 15) source2FaceCodes15 = true := by decide

def source2FaceCodes16 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 1, 2, 2]
theorem source2FaceRow16_checked : packetFaceRowB (sourceFamily2Chunk2.getD 0 default)
    (sourceFamily2.take 16) source2FaceCodes16 = true := by decide

def source2FaceCodes17 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source2FaceRow17_checked : packetFaceRowB (sourceFamily2Chunk2.getD 1 default)
    (sourceFamily2.take 17) source2FaceCodes17 = true := by decide

def source2FaceCodes18 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source2FaceRow18_checked : packetFaceRowB (sourceFamily2Chunk2.getD 2 default)
    (sourceFamily2.take 18) source2FaceCodes18 = true := by decide

def source2FaceCodes19 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2]
theorem source2FaceRow19_checked : packetFaceRowB (sourceFamily2Chunk2.getD 3 default)
    (sourceFamily2.take 19) source2FaceCodes19 = true := by decide

def source2FaceCodes20 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 2]
theorem source2FaceRow20_checked : packetFaceRowB (sourceFamily2Chunk2.getD 4 default)
    (sourceFamily2.take 20) source2FaceCodes20 = true := by decide

def source2FaceCodes21 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source2FaceRow21_checked : packetFaceRowB (sourceFamily2Chunk2.getD 5 default)
    (sourceFamily2.take 21) source2FaceCodes21 = true := by decide

def source2FaceCodes22 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source2FaceRow22_checked : packetFaceRowB (sourceFamily2Chunk2.getD 6 default)
    (sourceFamily2.take 22) source2FaceCodes22 = true := by decide

def source2FaceCodes23 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 0, 0, 0, 0, 2]
theorem source2FaceRow23_checked : packetFaceRowB (sourceFamily2Chunk2.getD 7 default)
    (sourceFamily2.take 23) source2FaceCodes23 = true := by decide


end SpectreGeometry.ReverseClusterTriangulation
