module

public import SpectreGeometry.ReverseClusterTriangulationSource07Data
public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def source7FaceCodes0 : List Nat := []
theorem source7FaceRow0_checked : packetFaceRowB (sourceFamily7Chunk0.getD 0 default)
    (sourceFamily7.take 0) source7FaceCodes0 = true := by decide

def source7FaceCodes1 : List Nat := [2]
theorem source7FaceRow1_checked : packetFaceRowB (sourceFamily7Chunk0.getD 1 default)
    (sourceFamily7.take 1) source7FaceCodes1 = true := by decide

def source7FaceCodes2 : List Nat := [1, 2]
theorem source7FaceRow2_checked : packetFaceRowB (sourceFamily7Chunk0.getD 2 default)
    (sourceFamily7.take 2) source7FaceCodes2 = true := by decide

def source7FaceCodes3 : List Nat := [1, 1, 2]
theorem source7FaceRow3_checked : packetFaceRowB (sourceFamily7Chunk0.getD 3 default)
    (sourceFamily7.take 3) source7FaceCodes3 = true := by decide

def source7FaceCodes4 : List Nat := [0, 0, 0, 0]
theorem source7FaceRow4_checked : packetFaceRowB (sourceFamily7Chunk0.getD 4 default)
    (sourceFamily7.take 4) source7FaceCodes4 = true := by decide

def source7FaceCodes5 : List Nat := [0, 0, 0, 0, 2]
theorem source7FaceRow5_checked : packetFaceRowB (sourceFamily7Chunk0.getD 5 default)
    (sourceFamily7.take 5) source7FaceCodes5 = true := by decide

def source7FaceCodes6 : List Nat := [2, 2, 2, 2, 2, 2]
theorem source7FaceRow6_checked : packetFaceRowB (sourceFamily7Chunk0.getD 6 default)
    (sourceFamily7.take 6) source7FaceCodes6 = true := by decide

def source7FaceCodes7 : List Nat := [1, 2, 2, 1, 1, 2, 2]
theorem source7FaceRow7_checked : packetFaceRowB (sourceFamily7Chunk0.getD 7 default)
    (sourceFamily7.take 7) source7FaceCodes7 = true := by decide

def source7FaceCodes8 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2]
theorem source7FaceRow8_checked : packetFaceRowB (sourceFamily7Chunk1.getD 0 default)
    (sourceFamily7.take 8) source7FaceCodes8 = true := by decide

def source7FaceCodes9 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source7FaceRow9_checked : packetFaceRowB (sourceFamily7Chunk1.getD 1 default)
    (sourceFamily7.take 9) source7FaceCodes9 = true := by decide

def source7FaceCodes10 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source7FaceRow10_checked : packetFaceRowB (sourceFamily7Chunk1.getD 2 default)
    (sourceFamily7.take 10) source7FaceCodes10 = true := by decide

def source7FaceCodes11 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2]
theorem source7FaceRow11_checked : packetFaceRowB (sourceFamily7Chunk1.getD 3 default)
    (sourceFamily7.take 11) source7FaceCodes11 = true := by decide

def source7FaceCodes12 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source7FaceRow12_checked : packetFaceRowB (sourceFamily7Chunk1.getD 4 default)
    (sourceFamily7.take 12) source7FaceCodes12 = true := by decide

def source7FaceCodes13 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source7FaceRow13_checked : packetFaceRowB (sourceFamily7Chunk1.getD 5 default)
    (sourceFamily7.take 13) source7FaceCodes13 = true := by decide

def source7FaceCodes14 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 2]
theorem source7FaceRow14_checked : packetFaceRowB (sourceFamily7Chunk1.getD 6 default)
    (sourceFamily7.take 14) source7FaceCodes14 = true := by decide

def source7FaceCodes15 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem source7FaceRow15_checked : packetFaceRowB (sourceFamily7Chunk1.getD 7 default)
    (sourceFamily7.take 15) source7FaceCodes15 = true := by decide

def source7FaceCodes16 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 1, 2, 2]
theorem source7FaceRow16_checked : packetFaceRowB (sourceFamily7Chunk2.getD 0 default)
    (sourceFamily7.take 16) source7FaceCodes16 = true := by decide

def source7FaceCodes17 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source7FaceRow17_checked : packetFaceRowB (sourceFamily7Chunk2.getD 1 default)
    (sourceFamily7.take 17) source7FaceCodes17 = true := by decide

def source7FaceCodes18 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source7FaceRow18_checked : packetFaceRowB (sourceFamily7Chunk2.getD 2 default)
    (sourceFamily7.take 18) source7FaceCodes18 = true := by decide

def source7FaceCodes19 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source7FaceRow19_checked : packetFaceRowB (sourceFamily7Chunk2.getD 3 default)
    (sourceFamily7.take 19) source7FaceCodes19 = true := by decide

def source7FaceCodes20 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2]
theorem source7FaceRow20_checked : packetFaceRowB (sourceFamily7Chunk2.getD 4 default)
    (sourceFamily7.take 20) source7FaceCodes20 = true := by decide

def source7FaceCodes21 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2]
theorem source7FaceRow21_checked : packetFaceRowB (sourceFamily7Chunk2.getD 5 default)
    (sourceFamily7.take 21) source7FaceCodes21 = true := by decide

def source7FaceCodes22 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source7FaceRow22_checked : packetFaceRowB (sourceFamily7Chunk2.getD 6 default)
    (sourceFamily7.take 22) source7FaceCodes22 = true := by decide

def source7FaceCodes23 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 2]
theorem source7FaceRow23_checked : packetFaceRowB (sourceFamily7Chunk2.getD 7 default)
    (sourceFamily7.take 23) source7FaceCodes23 = true := by decide


end SpectreGeometry.ReverseClusterTriangulation
