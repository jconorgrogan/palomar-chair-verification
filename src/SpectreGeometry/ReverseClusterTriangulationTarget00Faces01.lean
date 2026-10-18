module

public import SpectreGeometry.ReverseClusterTriangulationTarget00Data
public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def target0FaceCodes24 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem target0FaceRow24_checked : packetFaceRowB (targetMeshFamily0Chunk3.getD 0 default)
    (targetMeshFamily0.take 24) target0FaceCodes24 = true := by decide

def target0FaceCodes25 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2]
theorem target0FaceRow25_checked : packetFaceRowB (targetMeshFamily0Chunk3.getD 1 default)
    (targetMeshFamily0.take 25) target0FaceCodes25 = true := by decide

def target0FaceCodes26 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 1, 0, 5, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2]
theorem target0FaceRow26_checked : packetFaceRowB (targetMeshFamily0Chunk3.getD 2 default)
    (targetMeshFamily0.take 26) target0FaceCodes26 = true := by decide

def target0FaceCodes27 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 3, 2, 5, 4, 0, 3, 3]
theorem target0FaceRow27_checked : packetFaceRowB (targetMeshFamily0Chunk3.getD 3 default)
    (targetMeshFamily0.take 27) target0FaceCodes27 = true := by decide

def target0FaceCodes28 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2]
theorem target0FaceRow28_checked : packetFaceRowB (targetMeshFamily0Chunk3.getD 4 default)
    (targetMeshFamily0.take 28) target0FaceCodes28 = true := by decide

def target0FaceCodes29 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 5, 2]
theorem target0FaceRow29_checked : packetFaceRowB (targetMeshFamily0Chunk3.getD 5 default)
    (targetMeshFamily0.take 29) target0FaceCodes29 = true := by decide

def target0FaceCodes30 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 3, 0, 5, 4, 1, 3, 3, 1, 4, 2]
theorem target0FaceRow30_checked : packetFaceRowB (targetMeshFamily0Chunk3.getD 6 default)
    (targetMeshFamily0.take 30) target0FaceCodes30 = true := by decide

def target0FaceCodes31 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem target0FaceRow31_checked : packetFaceRowB (targetMeshFamily0Chunk3.getD 7 default)
    (targetMeshFamily0.take 31) target0FaceCodes31 = true := by decide

def target0FaceCodes32 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 0, 2, 2, 2, 2, 2, 2, 2]
theorem target0FaceRow32_checked : packetFaceRowB (targetMeshFamily0Chunk4.getD 0 default)
    (targetMeshFamily0.take 32) target0FaceCodes32 = true := by decide

def target0FaceCodes33 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2]
theorem target0FaceRow33_checked : packetFaceRowB (targetMeshFamily0Chunk4.getD 1 default)
    (targetMeshFamily0.take 33) target0FaceCodes33 = true := by decide

def target0FaceCodes34 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2]
theorem target0FaceRow34_checked : packetFaceRowB (targetMeshFamily0Chunk4.getD 2 default)
    (targetMeshFamily0.take 34) target0FaceCodes34 = true := by decide

def target0FaceCodes35 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
theorem target0FaceRow35_checked : packetFaceRowB (targetMeshFamily0Chunk4.getD 3 default)
    (targetMeshFamily0.take 35) target0FaceCodes35 = true := by decide

def target0FaceCodes36 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 5, 2]
theorem target0FaceRow36_checked : packetFaceRowB (targetMeshFamily0Chunk4.getD 4 default)
    (targetMeshFamily0.take 36) target0FaceCodes36 = true := by decide

def target0FaceCodes37 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2]
theorem target0FaceRow37_checked : packetFaceRowB (targetMeshFamily0Chunk4.getD 5 default)
    (targetMeshFamily0.take 37) target0FaceCodes37 = true := by decide

def target0FaceCodes38 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2]
theorem target0FaceRow38_checked : packetFaceRowB (targetMeshFamily0Chunk4.getD 6 default)
    (targetMeshFamily0.take 38) target0FaceCodes38 = true := by decide

def target0FaceCodes39 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2]
theorem target0FaceRow39_checked : packetFaceRowB (targetMeshFamily0Chunk4.getD 7 default)
    (targetMeshFamily0.take 39) target0FaceCodes39 = true := by decide

def target0FaceCodes40 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem target0FaceRow40_checked : packetFaceRowB (targetMeshFamily0Chunk5.getD 0 default)
    (targetMeshFamily0.take 40) target0FaceCodes40 = true := by decide

def target0FaceCodes41 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2]
theorem target0FaceRow41_checked : packetFaceRowB (targetMeshFamily0Chunk5.getD 1 default)
    (targetMeshFamily0.take 41) target0FaceCodes41 = true := by decide

def target0FaceCodes42 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2]
theorem target0FaceRow42_checked : packetFaceRowB (targetMeshFamily0Chunk5.getD 2 default)
    (targetMeshFamily0.take 42) target0FaceCodes42 = true := by decide

def target0FaceCodes43 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 1, 3, 5, 1, 1, 1, 3, 1, 4, 2]
theorem target0FaceRow43_checked : packetFaceRowB (targetMeshFamily0Chunk5.getD 3 default)
    (targetMeshFamily0.take 43) target0FaceCodes43 = true := by decide

def target0FaceCodes44 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 0, 0, 2, 5, 0, 0, 3, 3, 0, 1, 1, 0]
theorem target0FaceRow44_checked : packetFaceRowB (targetMeshFamily0Chunk5.getD 4 default)
    (targetMeshFamily0.take 44) target0FaceCodes44 = true := by decide

def target0FaceCodes45 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 5, 0, 0, 5, 2]
theorem target0FaceRow45_checked : packetFaceRowB (targetMeshFamily0Chunk5.getD 5 default)
    (targetMeshFamily0.take 45) target0FaceCodes45 = true := by decide

def target0FaceCodes46 : List Nat := [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem target0FaceRow46_checked : packetFaceRowB (targetMeshFamily0Chunk5.getD 6 default)
    (targetMeshFamily0.take 46) target0FaceCodes46 = true := by decide

def target0FaceCodes47 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 2, 3, 1, 1, 6, 2]
theorem target0FaceRow47_checked : packetFaceRowB (targetMeshFamily0Chunk5.getD 7 default)
    (targetMeshFamily0.take 47) target0FaceCodes47 = true := by decide


end SpectreGeometry.ReverseClusterTriangulation
