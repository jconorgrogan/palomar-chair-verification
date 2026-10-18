module

public import SpectreGeometry.ReverseClusterTriangulationSource05Data
public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def source5FaceCodes0 : List Nat := []
theorem source5FaceRow0_checked : packetFaceRowB (sourceFamily5Chunk0.getD 0 default)
    (sourceFamily5.take 0) source5FaceCodes0 = true := by decide

def source5FaceCodes1 : List Nat := [2]
theorem source5FaceRow1_checked : packetFaceRowB (sourceFamily5Chunk0.getD 1 default)
    (sourceFamily5.take 1) source5FaceCodes1 = true := by decide

def source5FaceCodes2 : List Nat := [4, 2]
theorem source5FaceRow2_checked : packetFaceRowB (sourceFamily5Chunk0.getD 2 default)
    (sourceFamily5.take 2) source5FaceCodes2 = true := by decide

def source5FaceCodes3 : List Nat := [1, 2, 2]
theorem source5FaceRow3_checked : packetFaceRowB (sourceFamily5Chunk0.getD 3 default)
    (sourceFamily5.take 3) source5FaceCodes3 = true := by decide

def source5FaceCodes4 : List Nat := [0, 0, 0, 0]
theorem source5FaceRow4_checked : packetFaceRowB (sourceFamily5Chunk0.getD 4 default)
    (sourceFamily5.take 4) source5FaceCodes4 = true := by decide

def source5FaceCodes5 : List Nat := [0, 0, 0, 0, 2]
theorem source5FaceRow5_checked : packetFaceRowB (sourceFamily5Chunk0.getD 5 default)
    (sourceFamily5.take 5) source5FaceCodes5 = true := by decide

def source5FaceCodes6 : List Nat := [2, 2, 2, 2, 2, 2]
theorem source5FaceRow6_checked : packetFaceRowB (sourceFamily5Chunk0.getD 6 default)
    (sourceFamily5.take 6) source5FaceCodes6 = true := by decide

def source5FaceCodes7 : List Nat := [4, 2, 2, 1, 1, 2, 2]
theorem source5FaceRow7_checked : packetFaceRowB (sourceFamily5Chunk0.getD 7 default)
    (sourceFamily5.take 7) source5FaceCodes7 = true := by decide

def source5FaceCodes8 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2]
theorem source5FaceRow8_checked : packetFaceRowB (sourceFamily5Chunk1.getD 0 default)
    (sourceFamily5.take 8) source5FaceCodes8 = true := by decide

def source5FaceCodes9 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source5FaceRow9_checked : packetFaceRowB (sourceFamily5Chunk1.getD 1 default)
    (sourceFamily5.take 9) source5FaceCodes9 = true := by decide

def source5FaceCodes10 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 1, 2]
theorem source5FaceRow10_checked : packetFaceRowB (sourceFamily5Chunk1.getD 2 default)
    (sourceFamily5.take 10) source5FaceCodes10 = true := by decide

def source5FaceCodes11 : List Nat := [1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 2]
theorem source5FaceRow11_checked : packetFaceRowB (sourceFamily5Chunk1.getD 3 default)
    (sourceFamily5.take 11) source5FaceCodes11 = true := by decide

def source5FaceCodes12 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source5FaceRow12_checked : packetFaceRowB (sourceFamily5Chunk1.getD 4 default)
    (sourceFamily5.take 12) source5FaceCodes12 = true := by decide

def source5FaceCodes13 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source5FaceRow13_checked : packetFaceRowB (sourceFamily5Chunk1.getD 5 default)
    (sourceFamily5.take 13) source5FaceCodes13 = true := by decide

def source5FaceCodes14 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 2]
theorem source5FaceRow14_checked : packetFaceRowB (sourceFamily5Chunk1.getD 6 default)
    (sourceFamily5.take 14) source5FaceCodes14 = true := by decide

def source5FaceCodes15 : List Nat := [4, 2, 3, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 2, 2]
theorem source5FaceRow15_checked : packetFaceRowB (sourceFamily5Chunk1.getD 7 default)
    (sourceFamily5.take 15) source5FaceCodes15 = true := by decide

def source5FaceCodes16 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2]
theorem source5FaceRow16_checked : packetFaceRowB (sourceFamily5Chunk2.getD 0 default)
    (sourceFamily5.take 16) source5FaceCodes16 = true := by decide

def source5FaceCodes17 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source5FaceRow17_checked : packetFaceRowB (sourceFamily5Chunk2.getD 1 default)
    (sourceFamily5.take 17) source5FaceCodes17 = true := by decide

def source5FaceCodes18 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source5FaceRow18_checked : packetFaceRowB (sourceFamily5Chunk2.getD 2 default)
    (sourceFamily5.take 18) source5FaceCodes18 = true := by decide

def source5FaceCodes19 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source5FaceRow19_checked : packetFaceRowB (sourceFamily5Chunk2.getD 3 default)
    (sourceFamily5.take 19) source5FaceCodes19 = true := by decide

def source5FaceCodes20 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2]
theorem source5FaceRow20_checked : packetFaceRowB (sourceFamily5Chunk2.getD 4 default)
    (sourceFamily5.take 20) source5FaceCodes20 = true := by decide

def source5FaceCodes21 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2]
theorem source5FaceRow21_checked : packetFaceRowB (sourceFamily5Chunk2.getD 5 default)
    (sourceFamily5.take 21) source5FaceCodes21 = true := by decide

def source5FaceCodes22 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source5FaceRow22_checked : packetFaceRowB (sourceFamily5Chunk2.getD 6 default)
    (sourceFamily5.take 22) source5FaceCodes22 = true := by decide

def source5FaceCodes23 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 2]
theorem source5FaceRow23_checked : packetFaceRowB (sourceFamily5Chunk2.getD 7 default)
    (sourceFamily5.take 23) source5FaceCodes23 = true := by decide


end SpectreGeometry.ReverseClusterTriangulation
