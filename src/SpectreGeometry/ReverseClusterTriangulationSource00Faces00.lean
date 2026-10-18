module

public import SpectreGeometry.ReverseClusterTriangulationSource00
public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def source0FaceCodes0 : List Nat := []
theorem source0FaceRow0_checked : packetFaceRowB (sourceFamily0Chunk0.getD 0 default)
    (sourceFamily0.take 0) source0FaceCodes0 = true := by decide

def source0FaceCodes1 : List Nat := [2]
theorem source0FaceRow1_checked : packetFaceRowB (sourceFamily0Chunk0.getD 1 default)
    (sourceFamily0.take 1) source0FaceCodes1 = true := by decide

def source0FaceCodes2 : List Nat := [4, 2]
theorem source0FaceRow2_checked : packetFaceRowB (sourceFamily0Chunk0.getD 2 default)
    (sourceFamily0.take 2) source0FaceCodes2 = true := by decide

def source0FaceCodes3 : List Nat := [1, 2, 2]
theorem source0FaceRow3_checked : packetFaceRowB (sourceFamily0Chunk0.getD 3 default)
    (sourceFamily0.take 3) source0FaceCodes3 = true := by decide

def source0FaceCodes4 : List Nat := [0, 0, 0, 0]
theorem source0FaceRow4_checked : packetFaceRowB (sourceFamily0Chunk0.getD 4 default)
    (sourceFamily0.take 4) source0FaceCodes4 = true := by decide

def source0FaceCodes5 : List Nat := [0, 0, 0, 0, 2]
theorem source0FaceRow5_checked : packetFaceRowB (sourceFamily0Chunk0.getD 5 default)
    (sourceFamily0.take 5) source0FaceCodes5 = true := by decide

def source0FaceCodes6 : List Nat := [2, 2, 2, 2, 2, 2]
theorem source0FaceRow6_checked : packetFaceRowB (sourceFamily0Chunk0.getD 6 default)
    (sourceFamily0.take 6) source0FaceCodes6 = true := by decide

def source0FaceCodes7 : List Nat := [4, 2, 2, 1, 1, 2, 2]
theorem source0FaceRow7_checked : packetFaceRowB (sourceFamily0Chunk0.getD 7 default)
    (sourceFamily0.take 7) source0FaceCodes7 = true := by decide

def source0FaceCodes8 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2]
theorem source0FaceRow8_checked : packetFaceRowB (sourceFamily0Chunk1.getD 0 default)
    (sourceFamily0.take 8) source0FaceCodes8 = true := by decide

def source0FaceCodes9 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source0FaceRow9_checked : packetFaceRowB (sourceFamily0Chunk1.getD 1 default)
    (sourceFamily0.take 9) source0FaceCodes9 = true := by decide

def source0FaceCodes10 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 1, 2]
theorem source0FaceRow10_checked : packetFaceRowB (sourceFamily0Chunk1.getD 2 default)
    (sourceFamily0.take 10) source0FaceCodes10 = true := by decide

def source0FaceCodes11 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]
theorem source0FaceRow11_checked : packetFaceRowB (sourceFamily0Chunk1.getD 3 default)
    (sourceFamily0.take 11) source0FaceCodes11 = true := by decide

def source0FaceCodes12 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source0FaceRow12_checked : packetFaceRowB (sourceFamily0Chunk1.getD 4 default)
    (sourceFamily0.take 12) source0FaceCodes12 = true := by decide

def source0FaceCodes13 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source0FaceRow13_checked : packetFaceRowB (sourceFamily0Chunk1.getD 5 default)
    (sourceFamily0.take 13) source0FaceCodes13 = true := by decide

def source0FaceCodes14 : List Nat := [2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 0, 2]
theorem source0FaceRow14_checked : packetFaceRowB (sourceFamily0Chunk1.getD 6 default)
    (sourceFamily0.take 14) source0FaceCodes14 = true := by decide

def source0FaceCodes15 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem source0FaceRow15_checked : packetFaceRowB (sourceFamily0Chunk1.getD 7 default)
    (sourceFamily0.take 15) source0FaceCodes15 = true := by decide

def source0FaceCodes16 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 1, 2, 2]
theorem source0FaceRow16_checked : packetFaceRowB (sourceFamily0Chunk2.getD 0 default)
    (sourceFamily0.take 16) source0FaceCodes16 = true := by decide

def source0FaceCodes17 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2]
theorem source0FaceRow17_checked : packetFaceRowB (sourceFamily0Chunk2.getD 1 default)
    (sourceFamily0.take 17) source0FaceCodes17 = true := by decide

def source0FaceCodes18 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source0FaceRow18_checked : packetFaceRowB (sourceFamily0Chunk2.getD 2 default)
    (sourceFamily0.take 18) source0FaceCodes18 = true := by decide

def source0FaceCodes19 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2]
theorem source0FaceRow19_checked : packetFaceRowB (sourceFamily0Chunk2.getD 3 default)
    (sourceFamily0.take 19) source0FaceCodes19 = true := by decide

def source0FaceCodes20 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 2]
theorem source0FaceRow20_checked : packetFaceRowB (sourceFamily0Chunk2.getD 4 default)
    (sourceFamily0.take 20) source0FaceCodes20 = true := by decide

def source0FaceCodes21 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source0FaceRow21_checked : packetFaceRowB (sourceFamily0Chunk2.getD 5 default)
    (sourceFamily0.take 21) source0FaceCodes21 = true := by decide

def source0FaceCodes22 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source0FaceRow22_checked : packetFaceRowB (sourceFamily0Chunk2.getD 6 default)
    (sourceFamily0.take 22) source0FaceCodes22 = true := by decide

def source0FaceCodes23 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 2]
theorem source0FaceRow23_checked : packetFaceRowB (sourceFamily0Chunk2.getD 7 default)
    (sourceFamily0.take 23) source0FaceCodes23 = true := by decide


end SpectreGeometry.ReverseClusterTriangulation
