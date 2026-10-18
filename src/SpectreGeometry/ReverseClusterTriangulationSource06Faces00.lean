module

public import SpectreGeometry.ReverseClusterTriangulationSource06Data
public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def source6FaceCodes0 : List Nat := []
theorem source6FaceRow0_checked : packetFaceRowB (sourceFamily6Chunk0.getD 0 default)
    (sourceFamily6.take 0) source6FaceCodes0 = true := by decide

def source6FaceCodes1 : List Nat := [2]
theorem source6FaceRow1_checked : packetFaceRowB (sourceFamily6Chunk0.getD 1 default)
    (sourceFamily6.take 1) source6FaceCodes1 = true := by decide

def source6FaceCodes2 : List Nat := [1, 2]
theorem source6FaceRow2_checked : packetFaceRowB (sourceFamily6Chunk0.getD 2 default)
    (sourceFamily6.take 2) source6FaceCodes2 = true := by decide

def source6FaceCodes3 : List Nat := [1, 1, 2]
theorem source6FaceRow3_checked : packetFaceRowB (sourceFamily6Chunk0.getD 3 default)
    (sourceFamily6.take 3) source6FaceCodes3 = true := by decide

def source6FaceCodes4 : List Nat := [0, 0, 0, 0]
theorem source6FaceRow4_checked : packetFaceRowB (sourceFamily6Chunk0.getD 4 default)
    (sourceFamily6.take 4) source6FaceCodes4 = true := by decide

def source6FaceCodes5 : List Nat := [0, 0, 0, 0, 2]
theorem source6FaceRow5_checked : packetFaceRowB (sourceFamily6Chunk0.getD 5 default)
    (sourceFamily6.take 5) source6FaceCodes5 = true := by decide

def source6FaceCodes6 : List Nat := [2, 2, 2, 2, 2, 2]
theorem source6FaceRow6_checked : packetFaceRowB (sourceFamily6Chunk0.getD 6 default)
    (sourceFamily6.take 6) source6FaceCodes6 = true := by decide

def source6FaceCodes7 : List Nat := [1, 2, 2, 1, 1, 2, 2]
theorem source6FaceRow7_checked : packetFaceRowB (sourceFamily6Chunk0.getD 7 default)
    (sourceFamily6.take 7) source6FaceCodes7 = true := by decide

def source6FaceCodes8 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2]
theorem source6FaceRow8_checked : packetFaceRowB (sourceFamily6Chunk1.getD 0 default)
    (sourceFamily6.take 8) source6FaceCodes8 = true := by decide

def source6FaceCodes9 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source6FaceRow9_checked : packetFaceRowB (sourceFamily6Chunk1.getD 1 default)
    (sourceFamily6.take 9) source6FaceCodes9 = true := by decide

def source6FaceCodes10 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source6FaceRow10_checked : packetFaceRowB (sourceFamily6Chunk1.getD 2 default)
    (sourceFamily6.take 10) source6FaceCodes10 = true := by decide

def source6FaceCodes11 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2]
theorem source6FaceRow11_checked : packetFaceRowB (sourceFamily6Chunk1.getD 3 default)
    (sourceFamily6.take 11) source6FaceCodes11 = true := by decide

def source6FaceCodes12 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source6FaceRow12_checked : packetFaceRowB (sourceFamily6Chunk1.getD 4 default)
    (sourceFamily6.take 12) source6FaceCodes12 = true := by decide

def source6FaceCodes13 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source6FaceRow13_checked : packetFaceRowB (sourceFamily6Chunk1.getD 5 default)
    (sourceFamily6.take 13) source6FaceCodes13 = true := by decide

def source6FaceCodes14 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 2]
theorem source6FaceRow14_checked : packetFaceRowB (sourceFamily6Chunk1.getD 6 default)
    (sourceFamily6.take 14) source6FaceCodes14 = true := by decide

def source6FaceCodes15 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem source6FaceRow15_checked : packetFaceRowB (sourceFamily6Chunk1.getD 7 default)
    (sourceFamily6.take 15) source6FaceCodes15 = true := by decide

def source6FaceCodes16 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 1, 2, 2]
theorem source6FaceRow16_checked : packetFaceRowB (sourceFamily6Chunk2.getD 0 default)
    (sourceFamily6.take 16) source6FaceCodes16 = true := by decide

def source6FaceCodes17 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source6FaceRow17_checked : packetFaceRowB (sourceFamily6Chunk2.getD 1 default)
    (sourceFamily6.take 17) source6FaceCodes17 = true := by decide

def source6FaceCodes18 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source6FaceRow18_checked : packetFaceRowB (sourceFamily6Chunk2.getD 2 default)
    (sourceFamily6.take 18) source6FaceCodes18 = true := by decide

def source6FaceCodes19 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source6FaceRow19_checked : packetFaceRowB (sourceFamily6Chunk2.getD 3 default)
    (sourceFamily6.take 19) source6FaceCodes19 = true := by decide

def source6FaceCodes20 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2]
theorem source6FaceRow20_checked : packetFaceRowB (sourceFamily6Chunk2.getD 4 default)
    (sourceFamily6.take 20) source6FaceCodes20 = true := by decide

def source6FaceCodes21 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2]
theorem source6FaceRow21_checked : packetFaceRowB (sourceFamily6Chunk2.getD 5 default)
    (sourceFamily6.take 21) source6FaceCodes21 = true := by decide

def source6FaceCodes22 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source6FaceRow22_checked : packetFaceRowB (sourceFamily6Chunk2.getD 6 default)
    (sourceFamily6.take 22) source6FaceCodes22 = true := by decide

def source6FaceCodes23 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 2]
theorem source6FaceRow23_checked : packetFaceRowB (sourceFamily6Chunk2.getD 7 default)
    (sourceFamily6.take 23) source6FaceCodes23 = true := by decide


end SpectreGeometry.ReverseClusterTriangulation
