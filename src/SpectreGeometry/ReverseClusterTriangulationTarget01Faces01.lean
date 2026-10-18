module

public import SpectreGeometry.ReverseClusterTriangulationTarget01Data
public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def target1FaceCodes24 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem target1FaceRow24_checked : packetFaceRowB (targetMeshFamily1Chunk3.getD 0 default)
    (targetMeshFamily1.take 24) target1FaceCodes24 = true := by decide

def target1FaceCodes25 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2]
theorem target1FaceRow25_checked : packetFaceRowB (targetMeshFamily1Chunk3.getD 1 default)
    (targetMeshFamily1.take 25) target1FaceCodes25 = true := by decide

def target1FaceCodes26 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 1, 0, 5, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2]
theorem target1FaceRow26_checked : packetFaceRowB (targetMeshFamily1Chunk3.getD 2 default)
    (targetMeshFamily1.take 26) target1FaceCodes26 = true := by decide

def target1FaceCodes27 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem target1FaceRow27_checked : packetFaceRowB (targetMeshFamily1Chunk3.getD 3 default)
    (targetMeshFamily1.take 27) target1FaceCodes27 = true := by decide

def target1FaceCodes28 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2]
theorem target1FaceRow28_checked : packetFaceRowB (targetMeshFamily1Chunk3.getD 4 default)
    (targetMeshFamily1.take 28) target1FaceCodes28 = true := by decide

def target1FaceCodes29 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2]
theorem target1FaceRow29_checked : packetFaceRowB (targetMeshFamily1Chunk3.getD 5 default)
    (targetMeshFamily1.take 29) target1FaceCodes29 = true := by decide

def target1FaceCodes30 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 1, 3, 5, 1, 1, 1, 3, 1, 4, 2]
theorem target1FaceRow30_checked : packetFaceRowB (targetMeshFamily1Chunk3.getD 6 default)
    (targetMeshFamily1.take 30) target1FaceCodes30 = true := by decide

def target1FaceCodes31 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 0, 0, 2, 5, 0, 0, 3, 3, 0, 1, 1, 0]
theorem target1FaceRow31_checked : packetFaceRowB (targetMeshFamily1Chunk3.getD 7 default)
    (targetMeshFamily1.take 31) target1FaceCodes31 = true := by decide

def target1FaceCodes32 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 0, 2, 2, 0, 0, 2, 2, 5, 0, 0, 5, 2]
theorem target1FaceRow32_checked : packetFaceRowB (targetMeshFamily1Chunk4.getD 0 default)
    (targetMeshFamily1.take 32) target1FaceCodes32 = true := by decide

def target1FaceCodes33 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem target1FaceRow33_checked : packetFaceRowB (targetMeshFamily1Chunk4.getD 1 default)
    (targetMeshFamily1.take 33) target1FaceCodes33 = true := by decide

def target1FaceCodes34 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 2, 3, 1, 1, 6, 2]
theorem target1FaceRow34_checked : packetFaceRowB (targetMeshFamily1Chunk4.getD 2 default)
    (targetMeshFamily1.take 34) target1FaceCodes34 = true := by decide

def target1FaceCodes35 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 3, 0, 0, 4, 1, 3, 0, 1, 1, 1, 1, 1, 1, 4, 2]
theorem target1FaceRow35_checked : packetFaceRowB (targetMeshFamily1Chunk4.getD 3 default)
    (targetMeshFamily1.take 35) target1FaceCodes35 = true := by decide

def target1FaceCodes36 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem target1FaceRow36_checked : packetFaceRowB (targetMeshFamily1Chunk4.getD 4 default)
    (targetMeshFamily1.take 36) target1FaceCodes36 = true := by decide

def target1FaceCodes37 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem target1FaceRow37_checked : packetFaceRowB (targetMeshFamily1Chunk4.getD 5 default)
    (targetMeshFamily1.take 37) target1FaceCodes37 = true := by decide

def target1FaceCodes38 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2]
theorem target1FaceRow38_checked : packetFaceRowB (targetMeshFamily1Chunk4.getD 6 default)
    (targetMeshFamily1.take 38) target1FaceCodes38 = true := by decide

def target1FaceCodes39 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2]
theorem target1FaceRow39_checked : packetFaceRowB (targetMeshFamily1Chunk4.getD 7 default)
    (targetMeshFamily1.take 39) target1FaceCodes39 = true := by decide

def target1FaceCodes40 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
theorem target1FaceRow40_checked : packetFaceRowB (targetMeshFamily1Chunk5.getD 0 default)
    (targetMeshFamily1.take 40) target1FaceCodes40 = true := by decide

def target1FaceCodes41 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 5, 2]
theorem target1FaceRow41_checked : packetFaceRowB (targetMeshFamily1Chunk5.getD 1 default)
    (targetMeshFamily1.take 41) target1FaceCodes41 = true := by decide

def target1FaceCodes42 : List Nat := [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem target1FaceRow42_checked : packetFaceRowB (targetMeshFamily1Chunk5.getD 2 default)
    (targetMeshFamily1.take 42) target1FaceCodes42 = true := by decide

def target1FaceCodes43 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2]
theorem target1FaceRow43_checked : packetFaceRowB (targetMeshFamily1Chunk5.getD 3 default)
    (targetMeshFamily1.take 43) target1FaceCodes43 = true := by decide

def target1FaceCodes44 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 1, 0, 5, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2]
theorem target1FaceRow44_checked : packetFaceRowB (targetMeshFamily1Chunk5.getD 4 default)
    (targetMeshFamily1.take 44) target1FaceCodes44 = true := by decide

def target1FaceCodes45 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 0, 2, 2]
theorem target1FaceRow45_checked : packetFaceRowB (targetMeshFamily1Chunk5.getD 5 default)
    (targetMeshFamily1.take 45) target1FaceCodes45 = true := by decide

def target1FaceCodes46 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem target1FaceRow46_checked : packetFaceRowB (targetMeshFamily1Chunk5.getD 6 default)
    (targetMeshFamily1.take 46) target1FaceCodes46 = true := by decide

def target1FaceCodes47 : List Nat := [3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 2]
theorem target1FaceRow47_checked : packetFaceRowB (targetMeshFamily1Chunk5.getD 7 default)
    (targetMeshFamily1.take 47) target1FaceCodes47 = true := by decide


end SpectreGeometry.ReverseClusterTriangulation
