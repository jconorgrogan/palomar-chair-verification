module

public import SpectreGeometry.ReverseClusterTriangulationSource08Data
public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def source8FaceCodes0 : List Nat := []
theorem source8FaceRow0_checked : packetFaceRowB (sourceFamily8Chunk0.getD 0 default)
    (sourceFamily8.take 0) source8FaceCodes0 = true := by decide

def source8FaceCodes1 : List Nat := [2]
theorem source8FaceRow1_checked : packetFaceRowB (sourceFamily8Chunk0.getD 1 default)
    (sourceFamily8.take 1) source8FaceCodes1 = true := by decide

def source8FaceCodes2 : List Nat := [4, 2]
theorem source8FaceRow2_checked : packetFaceRowB (sourceFamily8Chunk0.getD 2 default)
    (sourceFamily8.take 2) source8FaceCodes2 = true := by decide

def source8FaceCodes3 : List Nat := [1, 2, 2]
theorem source8FaceRow3_checked : packetFaceRowB (sourceFamily8Chunk0.getD 3 default)
    (sourceFamily8.take 3) source8FaceCodes3 = true := by decide

def source8FaceCodes4 : List Nat := [0, 0, 0, 0]
theorem source8FaceRow4_checked : packetFaceRowB (sourceFamily8Chunk0.getD 4 default)
    (sourceFamily8.take 4) source8FaceCodes4 = true := by decide

def source8FaceCodes5 : List Nat := [0, 0, 0, 0, 2]
theorem source8FaceRow5_checked : packetFaceRowB (sourceFamily8Chunk0.getD 5 default)
    (sourceFamily8.take 5) source8FaceCodes5 = true := by decide

def source8FaceCodes6 : List Nat := [2, 2, 2, 2, 2, 2]
theorem source8FaceRow6_checked : packetFaceRowB (sourceFamily8Chunk0.getD 6 default)
    (sourceFamily8.take 6) source8FaceCodes6 = true := by decide

def source8FaceCodes7 : List Nat := [4, 2, 2, 1, 1, 2, 2]
theorem source8FaceRow7_checked : packetFaceRowB (sourceFamily8Chunk0.getD 7 default)
    (sourceFamily8.take 7) source8FaceCodes7 = true := by decide

def source8FaceCodes8 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2]
theorem source8FaceRow8_checked : packetFaceRowB (sourceFamily8Chunk1.getD 0 default)
    (sourceFamily8.take 8) source8FaceCodes8 = true := by decide

def source8FaceCodes9 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source8FaceRow9_checked : packetFaceRowB (sourceFamily8Chunk1.getD 1 default)
    (sourceFamily8.take 9) source8FaceCodes9 = true := by decide

def source8FaceCodes10 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 1, 2]
theorem source8FaceRow10_checked : packetFaceRowB (sourceFamily8Chunk1.getD 2 default)
    (sourceFamily8.take 10) source8FaceCodes10 = true := by decide

def source8FaceCodes11 : List Nat := [1, 1, 1, 0, 0, 1, 1, 1, 0, 2, 2]
theorem source8FaceRow11_checked : packetFaceRowB (sourceFamily8Chunk1.getD 3 default)
    (sourceFamily8.take 11) source8FaceCodes11 = true := by decide

def source8FaceCodes12 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source8FaceRow12_checked : packetFaceRowB (sourceFamily8Chunk1.getD 4 default)
    (sourceFamily8.take 12) source8FaceCodes12 = true := by decide

def source8FaceCodes13 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source8FaceRow13_checked : packetFaceRowB (sourceFamily8Chunk1.getD 5 default)
    (sourceFamily8.take 13) source8FaceCodes13 = true := by decide

def source8FaceCodes14 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 2]
theorem source8FaceRow14_checked : packetFaceRowB (sourceFamily8Chunk1.getD 6 default)
    (sourceFamily8.take 14) source8FaceCodes14 = true := by decide

def source8FaceCodes15 : List Nat := [4, 2, 3, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 2, 2]
theorem source8FaceRow15_checked : packetFaceRowB (sourceFamily8Chunk1.getD 7 default)
    (sourceFamily8.take 15) source8FaceCodes15 = true := by decide

def source8FaceCodes16 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2]
theorem source8FaceRow16_checked : packetFaceRowB (sourceFamily8Chunk2.getD 0 default)
    (sourceFamily8.take 16) source8FaceCodes16 = true := by decide

def source8FaceCodes17 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source8FaceRow17_checked : packetFaceRowB (sourceFamily8Chunk2.getD 1 default)
    (sourceFamily8.take 17) source8FaceCodes17 = true := by decide

def source8FaceCodes18 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source8FaceRow18_checked : packetFaceRowB (sourceFamily8Chunk2.getD 2 default)
    (sourceFamily8.take 18) source8FaceCodes18 = true := by decide

def source8FaceCodes19 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source8FaceRow19_checked : packetFaceRowB (sourceFamily8Chunk2.getD 3 default)
    (sourceFamily8.take 19) source8FaceCodes19 = true := by decide

def source8FaceCodes20 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2]
theorem source8FaceRow20_checked : packetFaceRowB (sourceFamily8Chunk2.getD 4 default)
    (sourceFamily8.take 20) source8FaceCodes20 = true := by decide

def source8FaceCodes21 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2]
theorem source8FaceRow21_checked : packetFaceRowB (sourceFamily8Chunk2.getD 5 default)
    (sourceFamily8.take 21) source8FaceCodes21 = true := by decide

def source8FaceCodes22 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source8FaceRow22_checked : packetFaceRowB (sourceFamily8Chunk2.getD 6 default)
    (sourceFamily8.take 22) source8FaceCodes22 = true := by decide

def source8FaceCodes23 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 2]
theorem source8FaceRow23_checked : packetFaceRowB (sourceFamily8Chunk2.getD 7 default)
    (sourceFamily8.take 23) source8FaceCodes23 = true := by decide


end SpectreGeometry.ReverseClusterTriangulation
