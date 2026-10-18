module

public import SpectreGeometry.ReverseClusterTriangulationSource01Data
public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def source1FaceCodes0 : List Nat := []
theorem source1FaceRow0_checked : packetFaceRowB (sourceFamily1Chunk0.getD 0 default)
    (sourceFamily1.take 0) source1FaceCodes0 = true := by decide

def source1FaceCodes1 : List Nat := [2]
theorem source1FaceRow1_checked : packetFaceRowB (sourceFamily1Chunk0.getD 1 default)
    (sourceFamily1.take 1) source1FaceCodes1 = true := by decide

def source1FaceCodes2 : List Nat := [1, 2]
theorem source1FaceRow2_checked : packetFaceRowB (sourceFamily1Chunk0.getD 2 default)
    (sourceFamily1.take 2) source1FaceCodes2 = true := by decide

def source1FaceCodes3 : List Nat := [1, 1, 2]
theorem source1FaceRow3_checked : packetFaceRowB (sourceFamily1Chunk0.getD 3 default)
    (sourceFamily1.take 3) source1FaceCodes3 = true := by decide

def source1FaceCodes4 : List Nat := [0, 0, 0, 0]
theorem source1FaceRow4_checked : packetFaceRowB (sourceFamily1Chunk0.getD 4 default)
    (sourceFamily1.take 4) source1FaceCodes4 = true := by decide

def source1FaceCodes5 : List Nat := [0, 0, 0, 0, 2]
theorem source1FaceRow5_checked : packetFaceRowB (sourceFamily1Chunk0.getD 5 default)
    (sourceFamily1.take 5) source1FaceCodes5 = true := by decide

def source1FaceCodes6 : List Nat := [2, 2, 2, 2, 2, 2]
theorem source1FaceRow6_checked : packetFaceRowB (sourceFamily1Chunk0.getD 6 default)
    (sourceFamily1.take 6) source1FaceCodes6 = true := by decide

def source1FaceCodes7 : List Nat := [1, 2, 2, 1, 1, 2, 2]
theorem source1FaceRow7_checked : packetFaceRowB (sourceFamily1Chunk0.getD 7 default)
    (sourceFamily1.take 7) source1FaceCodes7 = true := by decide

def source1FaceCodes8 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2]
theorem source1FaceRow8_checked : packetFaceRowB (sourceFamily1Chunk1.getD 0 default)
    (sourceFamily1.take 8) source1FaceCodes8 = true := by decide

def source1FaceCodes9 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source1FaceRow9_checked : packetFaceRowB (sourceFamily1Chunk1.getD 1 default)
    (sourceFamily1.take 9) source1FaceCodes9 = true := by decide

def source1FaceCodes10 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source1FaceRow10_checked : packetFaceRowB (sourceFamily1Chunk1.getD 2 default)
    (sourceFamily1.take 10) source1FaceCodes10 = true := by decide

def source1FaceCodes11 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2]
theorem source1FaceRow11_checked : packetFaceRowB (sourceFamily1Chunk1.getD 3 default)
    (sourceFamily1.take 11) source1FaceCodes11 = true := by decide

def source1FaceCodes12 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source1FaceRow12_checked : packetFaceRowB (sourceFamily1Chunk1.getD 4 default)
    (sourceFamily1.take 12) source1FaceCodes12 = true := by decide

def source1FaceCodes13 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source1FaceRow13_checked : packetFaceRowB (sourceFamily1Chunk1.getD 5 default)
    (sourceFamily1.take 13) source1FaceCodes13 = true := by decide

def source1FaceCodes14 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 2]
theorem source1FaceRow14_checked : packetFaceRowB (sourceFamily1Chunk1.getD 6 default)
    (sourceFamily1.take 14) source1FaceCodes14 = true := by decide

def source1FaceCodes15 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem source1FaceRow15_checked : packetFaceRowB (sourceFamily1Chunk1.getD 7 default)
    (sourceFamily1.take 15) source1FaceCodes15 = true := by decide

def source1FaceCodes16 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 1, 2, 2]
theorem source1FaceRow16_checked : packetFaceRowB (sourceFamily1Chunk2.getD 0 default)
    (sourceFamily1.take 16) source1FaceCodes16 = true := by decide

def source1FaceCodes17 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source1FaceRow17_checked : packetFaceRowB (sourceFamily1Chunk2.getD 1 default)
    (sourceFamily1.take 17) source1FaceCodes17 = true := by decide

def source1FaceCodes18 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source1FaceRow18_checked : packetFaceRowB (sourceFamily1Chunk2.getD 2 default)
    (sourceFamily1.take 18) source1FaceCodes18 = true := by decide

def source1FaceCodes19 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source1FaceRow19_checked : packetFaceRowB (sourceFamily1Chunk2.getD 3 default)
    (sourceFamily1.take 19) source1FaceCodes19 = true := by decide

def source1FaceCodes20 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2]
theorem source1FaceRow20_checked : packetFaceRowB (sourceFamily1Chunk2.getD 4 default)
    (sourceFamily1.take 20) source1FaceCodes20 = true := by decide

def source1FaceCodes21 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2]
theorem source1FaceRow21_checked : packetFaceRowB (sourceFamily1Chunk2.getD 5 default)
    (sourceFamily1.take 21) source1FaceCodes21 = true := by decide

def source1FaceCodes22 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source1FaceRow22_checked : packetFaceRowB (sourceFamily1Chunk2.getD 6 default)
    (sourceFamily1.take 22) source1FaceCodes22 = true := by decide

def source1FaceCodes23 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 2]
theorem source1FaceRow23_checked : packetFaceRowB (sourceFamily1Chunk2.getD 7 default)
    (sourceFamily1.take 23) source1FaceCodes23 = true := by decide


end SpectreGeometry.ReverseClusterTriangulation
