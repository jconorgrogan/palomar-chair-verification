module

public import SpectreGeometry.ReverseClusterTriangulationTarget01Data
public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def target1FaceCodes48 : List Nat := [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 2]
theorem target1FaceRow48_checked : packetFaceRowB (targetMeshFamily1Chunk6.getD 0 default)
    (targetMeshFamily1.take 48) target1FaceCodes48 = true := by decide

def target1FaceCodes49 : List Nat := [0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 3, 2, 2]
theorem target1FaceRow49_checked : packetFaceRowB (targetMeshFamily1Chunk6.getD 1 default)
    (targetMeshFamily1.take 49) target1FaceCodes49 = true := by decide

def target1FaceCodes50 : List Nat := [5, 0, 0, 3, 5, 0, 0, 0, 5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2]
theorem target1FaceRow50_checked : packetFaceRowB (targetMeshFamily1Chunk6.getD 2 default)
    (targetMeshFamily1.take 50) target1FaceCodes50 = true := by decide

def target1FaceCodes51 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]
theorem target1FaceRow51_checked : packetFaceRowB (targetMeshFamily1Chunk6.getD 3 default)
    (targetMeshFamily1.take 51) target1FaceCodes51 = true := by decide

def target1FaceCodes52 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 6, 2]
theorem target1FaceRow52_checked : packetFaceRowB (targetMeshFamily1Chunk6.getD 4 default)
    (targetMeshFamily1.take 52) target1FaceCodes52 = true := by decide

def target1FaceCodes53 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 3, 0, 0, 1, 1, 4, 2]
theorem target1FaceRow53_checked : packetFaceRowB (targetMeshFamily1Chunk6.getD 5 default)
    (targetMeshFamily1.take 53) target1FaceCodes53 = true := by decide

def target1FaceCodes54 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 1, 1, 0]
theorem target1FaceRow54_checked : packetFaceRowB (targetMeshFamily1Chunk6.getD 6 default)
    (targetMeshFamily1.take 54) target1FaceCodes54 = true := by decide

def target1FaceCodes55 : List Nat := [5, 0, 0, 3, 5, 0, 0, 0, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 0, 0, 0, 5, 2]
theorem target1FaceRow55_checked : packetFaceRowB (targetMeshFamily1Chunk6.getD 7 default)
    (targetMeshFamily1.take 55) target1FaceCodes55 = true := by decide

def target1FaceCodes56 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2]
theorem target1FaceRow56_checked : packetFaceRowB (targetMeshFamily1Chunk7.getD 0 default)
    (targetMeshFamily1.take 56) target1FaceCodes56 = true := by decide

def target1FaceCodes57 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 3, 1, 1, 6, 2]
theorem target1FaceRow57_checked : packetFaceRowB (targetMeshFamily1Chunk7.getD 1 default)
    (targetMeshFamily1.take 57) target1FaceCodes57 = true := by decide

def target1FaceCodes58 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 4, 2]
theorem target1FaceRow58_checked : packetFaceRowB (targetMeshFamily1Chunk7.getD 2 default)
    (targetMeshFamily1.take 58) target1FaceCodes58 = true := by decide

def target1FaceCodes59 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
theorem target1FaceRow59_checked : packetFaceRowB (targetMeshFamily1Chunk7.getD 3 default)
    (targetMeshFamily1.take 59) target1FaceCodes59 = true := by decide

def target1FaceCodes60 : List Nat := [4, 0, 0, 3, 5, 0, 0, 0, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 0, 0, 0, 3, 5, 0, 0, 0, 5, 2]
theorem target1FaceRow60_checked : packetFaceRowB (targetMeshFamily1Chunk7.getD 4 default)
    (targetMeshFamily1.take 60) target1FaceCodes60 = true := by decide

def target1FaceCodes61 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem target1FaceRow61_checked : packetFaceRowB (targetMeshFamily1Chunk7.getD 5 default)
    (targetMeshFamily1.take 61) target1FaceCodes61 = true := by decide

def target1FaceCodes62 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2]
theorem target1FaceRow62_checked : packetFaceRowB (targetMeshFamily1Chunk7.getD 6 default)
    (targetMeshFamily1.take 62) target1FaceCodes62 = true := by decide

def target1FaceCodes63 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2]
theorem target1FaceRow63_checked : packetFaceRowB (targetMeshFamily1Chunk7.getD 7 default)
    (targetMeshFamily1.take 63) target1FaceCodes63 = true := by decide

def target1FaceCodes64 : List Nat := [2, 2, 2, 2, 2, 2, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 0, 3, 2, 2, 4, 0, 0, 2, 2, 0, 0, 3, 2]
theorem target1FaceRow64_checked : packetFaceRowB (targetMeshFamily1Chunk8.getD 0 default)
    (targetMeshFamily1.take 64) target1FaceCodes64 = true := by decide

def target1FaceCodes65 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem target1FaceRow65_checked : packetFaceRowB (targetMeshFamily1Chunk8.getD 1 default)
    (targetMeshFamily1.take 65) target1FaceCodes65 = true := by decide

def target1FaceCodes66 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 5, 2]
theorem target1FaceRow66_checked : packetFaceRowB (targetMeshFamily1Chunk8.getD 2 default)
    (targetMeshFamily1.take 66) target1FaceCodes66 = true := by decide

def target1FaceCodes67 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 3, 0, 0, 4, 4, 3, 0, 1, 4, 2]
theorem target1FaceRow67_checked : packetFaceRowB (targetMeshFamily1Chunk8.getD 3 default)
    (targetMeshFamily1.take 67) target1FaceCodes67 = true := by decide

def target1FaceCodes68 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 3, 2, 2, 4, 0, 3, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 3, 2, 2]
theorem target1FaceRow68_checked : packetFaceRowB (targetMeshFamily1Chunk8.getD 4 default)
    (targetMeshFamily1.take 68) target1FaceCodes68 = true := by decide

def target1FaceCodes69 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 0, 2, 2, 5, 0, 0, 3, 5, 0, 0, 0, 5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem target1FaceRow69_checked : packetFaceRowB (targetMeshFamily1Chunk8.getD 5 default)
    (targetMeshFamily1.take 69) target1FaceCodes69 = true := by decide

def target1FaceCodes70 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]
theorem target1FaceRow70_checked : packetFaceRowB (targetMeshFamily1Chunk8.getD 6 default)
    (targetMeshFamily1.take 70) target1FaceCodes70 = true := by decide

def target1FaceCodes71 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 2, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 6, 2]
theorem target1FaceRow71_checked : packetFaceRowB (targetMeshFamily1Chunk8.getD 7 default)
    (targetMeshFamily1.take 71) target1FaceCodes71 = true := by decide


end SpectreGeometry.ReverseClusterTriangulation
