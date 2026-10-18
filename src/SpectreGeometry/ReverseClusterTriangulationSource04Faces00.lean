module

public import SpectreGeometry.ReverseClusterTriangulationSource04Data
public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def source4FaceCodes0 : List Nat := []
theorem source4FaceRow0_checked : packetFaceRowB (sourceFamily4Chunk0.getD 0 default)
    (sourceFamily4.take 0) source4FaceCodes0 = true := by decide

def source4FaceCodes1 : List Nat := [2]
theorem source4FaceRow1_checked : packetFaceRowB (sourceFamily4Chunk0.getD 1 default)
    (sourceFamily4.take 1) source4FaceCodes1 = true := by decide

def source4FaceCodes2 : List Nat := [4, 2]
theorem source4FaceRow2_checked : packetFaceRowB (sourceFamily4Chunk0.getD 2 default)
    (sourceFamily4.take 2) source4FaceCodes2 = true := by decide

def source4FaceCodes3 : List Nat := [1, 2, 2]
theorem source4FaceRow3_checked : packetFaceRowB (sourceFamily4Chunk0.getD 3 default)
    (sourceFamily4.take 3) source4FaceCodes3 = true := by decide

def source4FaceCodes4 : List Nat := [0, 0, 0, 0]
theorem source4FaceRow4_checked : packetFaceRowB (sourceFamily4Chunk0.getD 4 default)
    (sourceFamily4.take 4) source4FaceCodes4 = true := by decide

def source4FaceCodes5 : List Nat := [0, 0, 0, 0, 2]
theorem source4FaceRow5_checked : packetFaceRowB (sourceFamily4Chunk0.getD 5 default)
    (sourceFamily4.take 5) source4FaceCodes5 = true := by decide

def source4FaceCodes6 : List Nat := [2, 2, 2, 2, 2, 2]
theorem source4FaceRow6_checked : packetFaceRowB (sourceFamily4Chunk0.getD 6 default)
    (sourceFamily4.take 6) source4FaceCodes6 = true := by decide

def source4FaceCodes7 : List Nat := [4, 2, 2, 1, 1, 2, 2]
theorem source4FaceRow7_checked : packetFaceRowB (sourceFamily4Chunk0.getD 7 default)
    (sourceFamily4.take 7) source4FaceCodes7 = true := by decide

def source4FaceCodes8 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2]
theorem source4FaceRow8_checked : packetFaceRowB (sourceFamily4Chunk1.getD 0 default)
    (sourceFamily4.take 8) source4FaceCodes8 = true := by decide

def source4FaceCodes9 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source4FaceRow9_checked : packetFaceRowB (sourceFamily4Chunk1.getD 1 default)
    (sourceFamily4.take 9) source4FaceCodes9 = true := by decide

def source4FaceCodes10 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 1, 2]
theorem source4FaceRow10_checked : packetFaceRowB (sourceFamily4Chunk1.getD 2 default)
    (sourceFamily4.take 10) source4FaceCodes10 = true := by decide

def source4FaceCodes11 : List Nat := [1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 2]
theorem source4FaceRow11_checked : packetFaceRowB (sourceFamily4Chunk1.getD 3 default)
    (sourceFamily4.take 11) source4FaceCodes11 = true := by decide

def source4FaceCodes12 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source4FaceRow12_checked : packetFaceRowB (sourceFamily4Chunk1.getD 4 default)
    (sourceFamily4.take 12) source4FaceCodes12 = true := by decide

def source4FaceCodes13 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source4FaceRow13_checked : packetFaceRowB (sourceFamily4Chunk1.getD 5 default)
    (sourceFamily4.take 13) source4FaceCodes13 = true := by decide

def source4FaceCodes14 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 1, 0, 0, 0, 0, 2]
theorem source4FaceRow14_checked : packetFaceRowB (sourceFamily4Chunk1.getD 6 default)
    (sourceFamily4.take 14) source4FaceCodes14 = true := by decide

def source4FaceCodes15 : List Nat := [4, 4, 3, 1, 1, 4, 4, 3, 1, 2, 2, 2, 2, 2, 2]
theorem source4FaceRow15_checked : packetFaceRowB (sourceFamily4Chunk1.getD 7 default)
    (sourceFamily4.take 15) source4FaceCodes15 = true := by decide

def source4FaceCodes16 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2]
theorem source4FaceRow16_checked : packetFaceRowB (sourceFamily4Chunk2.getD 0 default)
    (sourceFamily4.take 16) source4FaceCodes16 = true := by decide

def source4FaceCodes17 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source4FaceRow17_checked : packetFaceRowB (sourceFamily4Chunk2.getD 1 default)
    (sourceFamily4.take 17) source4FaceCodes17 = true := by decide

def source4FaceCodes18 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source4FaceRow18_checked : packetFaceRowB (sourceFamily4Chunk2.getD 2 default)
    (sourceFamily4.take 18) source4FaceCodes18 = true := by decide

def source4FaceCodes19 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2]
theorem source4FaceRow19_checked : packetFaceRowB (sourceFamily4Chunk2.getD 3 default)
    (sourceFamily4.take 19) source4FaceCodes19 = true := by decide

def source4FaceCodes20 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 2]
theorem source4FaceRow20_checked : packetFaceRowB (sourceFamily4Chunk2.getD 4 default)
    (sourceFamily4.take 20) source4FaceCodes20 = true := by decide

def source4FaceCodes21 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source4FaceRow21_checked : packetFaceRowB (sourceFamily4Chunk2.getD 5 default)
    (sourceFamily4.take 21) source4FaceCodes21 = true := by decide

def source4FaceCodes22 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source4FaceRow22_checked : packetFaceRowB (sourceFamily4Chunk2.getD 6 default)
    (sourceFamily4.take 22) source4FaceCodes22 = true := by decide

def source4FaceCodes23 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 0, 0, 0, 0, 2]
theorem source4FaceRow23_checked : packetFaceRowB (sourceFamily4Chunk2.getD 7 default)
    (sourceFamily4.take 23) source4FaceCodes23 = true := by decide


end SpectreGeometry.ReverseClusterTriangulation
