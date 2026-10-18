module

public import SpectreGeometry.ReverseClusterTriangulationSource00
public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def source0FaceCodes24 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem source0FaceRow24_checked : packetFaceRowB (sourceFamily0Chunk3.getD 0 default)
    (sourceFamily0.take 24) source0FaceCodes24 = true := by decide

def source0FaceCodes25 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 1, 2, 2]
theorem source0FaceRow25_checked : packetFaceRowB (sourceFamily0Chunk3.getD 1 default)
    (sourceFamily0.take 25) source0FaceCodes25 = true := by decide

def source0FaceCodes26 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2]
theorem source0FaceRow26_checked : packetFaceRowB (sourceFamily0Chunk3.getD 2 default)
    (sourceFamily0.take 26) source0FaceCodes26 = true := by decide

def source0FaceCodes27 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source0FaceRow27_checked : packetFaceRowB (sourceFamily0Chunk3.getD 3 default)
    (sourceFamily0.take 27) source0FaceCodes27 = true := by decide

def source0FaceCodes28 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2]
theorem source0FaceRow28_checked : packetFaceRowB (sourceFamily0Chunk3.getD 4 default)
    (sourceFamily0.take 28) source0FaceCodes28 = true := by decide

def source0FaceCodes29 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 2, 2]
theorem source0FaceRow29_checked : packetFaceRowB (sourceFamily0Chunk3.getD 5 default)
    (sourceFamily0.take 29) source0FaceCodes29 = true := by decide

def source0FaceCodes30 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source0FaceRow30_checked : packetFaceRowB (sourceFamily0Chunk3.getD 6 default)
    (sourceFamily0.take 30) source0FaceCodes30 = true := by decide

def source0FaceCodes31 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source0FaceRow31_checked : packetFaceRowB (sourceFamily0Chunk3.getD 7 default)
    (sourceFamily0.take 31) source0FaceCodes31 = true := by decide

def source0FaceCodes32 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2]
theorem source0FaceRow32_checked : packetFaceRowB (sourceFamily0Chunk4.getD 0 default)
    (sourceFamily0.take 32) source0FaceCodes32 = true := by decide

def source0FaceCodes33 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 2, 2]
theorem source0FaceRow33_checked : packetFaceRowB (sourceFamily0Chunk4.getD 1 default)
    (sourceFamily0.take 33) source0FaceCodes33 = true := by decide

def source0FaceCodes34 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source0FaceRow34_checked : packetFaceRowB (sourceFamily0Chunk4.getD 2 default)
    (sourceFamily0.take 34) source0FaceCodes34 = true := by decide

def source0FaceCodes35 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source0FaceRow35_checked : packetFaceRowB (sourceFamily0Chunk4.getD 3 default)
    (sourceFamily0.take 35) source0FaceCodes35 = true := by decide

def source0FaceCodes36 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 0, 0, 0, 0, 2]
theorem source0FaceRow36_checked : packetFaceRowB (sourceFamily0Chunk4.getD 4 default)
    (sourceFamily0.take 36) source0FaceCodes36 = true := by decide

def source0FaceCodes37 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 4, 3, 1, 4, 4, 3, 4, 2, 2, 2, 2, 2, 2]
theorem source0FaceRow37_checked : packetFaceRowB (sourceFamily0Chunk4.getD 5 default)
    (sourceFamily0.take 37) source0FaceCodes37 = true := by decide

def source0FaceCodes38 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2]
theorem source0FaceRow38_checked : packetFaceRowB (sourceFamily0Chunk4.getD 6 default)
    (sourceFamily0.take 38) source0FaceCodes38 = true := by decide

def source0FaceCodes39 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source0FaceRow39_checked : packetFaceRowB (sourceFamily0Chunk4.getD 7 default)
    (sourceFamily0.take 39) source0FaceCodes39 = true := by decide

def source0FaceCodes40 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source0FaceRow40_checked : packetFaceRowB (sourceFamily0Chunk5.getD 0 default)
    (sourceFamily0.take 40) source0FaceCodes40 = true := by decide

def source0FaceCodes41 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source0FaceRow41_checked : packetFaceRowB (sourceFamily0Chunk5.getD 1 default)
    (sourceFamily0.take 41) source0FaceCodes41 = true := by decide

def source0FaceCodes42 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2]
theorem source0FaceRow42_checked : packetFaceRowB (sourceFamily0Chunk5.getD 2 default)
    (sourceFamily0.take 42) source0FaceCodes42 = true := by decide

def source0FaceCodes43 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source0FaceRow43_checked : packetFaceRowB (sourceFamily0Chunk5.getD 3 default)
    (sourceFamily0.take 43) source0FaceCodes43 = true := by decide

def source0FaceCodes44 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source0FaceRow44_checked : packetFaceRowB (sourceFamily0Chunk5.getD 4 default)
    (sourceFamily0.take 44) source0FaceCodes44 = true := by decide

def source0FaceCodes45 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 2]
theorem source0FaceRow45_checked : packetFaceRowB (sourceFamily0Chunk5.getD 5 default)
    (sourceFamily0.take 45) source0FaceCodes45 = true := by decide

def source0FaceCodes46 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem source0FaceRow46_checked : packetFaceRowB (sourceFamily0Chunk5.getD 6 default)
    (sourceFamily0.take 46) source0FaceCodes46 = true := by decide

def source0FaceCodes47 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 1, 2, 2]
theorem source0FaceRow47_checked : packetFaceRowB (sourceFamily0Chunk5.getD 7 default)
    (sourceFamily0.take 47) source0FaceCodes47 = true := by decide


end SpectreGeometry.ReverseClusterTriangulation
