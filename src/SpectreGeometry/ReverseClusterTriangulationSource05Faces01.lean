module

public import SpectreGeometry.ReverseClusterTriangulationSource05Data
public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def source5FaceCodes24 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem source5FaceRow24_checked : packetFaceRowB (sourceFamily5Chunk3.getD 0 default)
    (sourceFamily5.take 24) source5FaceCodes24 = true := by decide

def source5FaceCodes25 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 2, 1, 1, 2, 2]
theorem source5FaceRow25_checked : packetFaceRowB (sourceFamily5Chunk3.getD 1 default)
    (sourceFamily5.take 25) source5FaceCodes25 = true := by decide

def source5FaceCodes26 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2]
theorem source5FaceRow26_checked : packetFaceRowB (sourceFamily5Chunk3.getD 2 default)
    (sourceFamily5.take 26) source5FaceCodes26 = true := by decide

def source5FaceCodes27 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source5FaceRow27_checked : packetFaceRowB (sourceFamily5Chunk3.getD 3 default)
    (sourceFamily5.take 27) source5FaceCodes27 = true := by decide

def source5FaceCodes28 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 2]
theorem source5FaceRow28_checked : packetFaceRowB (sourceFamily5Chunk3.getD 4 default)
    (sourceFamily5.take 28) source5FaceCodes28 = true := by decide

def source5FaceCodes29 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source5FaceRow29_checked : packetFaceRowB (sourceFamily5Chunk3.getD 5 default)
    (sourceFamily5.take 29) source5FaceCodes29 = true := by decide

def source5FaceCodes30 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source5FaceRow30_checked : packetFaceRowB (sourceFamily5Chunk3.getD 6 default)
    (sourceFamily5.take 30) source5FaceCodes30 = true := by decide

def source5FaceCodes31 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source5FaceRow31_checked : packetFaceRowB (sourceFamily5Chunk3.getD 7 default)
    (sourceFamily5.take 31) source5FaceCodes31 = true := by decide

def source5FaceCodes32 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 0, 2]
theorem source5FaceRow32_checked : packetFaceRowB (sourceFamily5Chunk4.getD 0 default)
    (sourceFamily5.take 32) source5FaceCodes32 = true := by decide

def source5FaceCodes33 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem source5FaceRow33_checked : packetFaceRowB (sourceFamily5Chunk4.getD 1 default)
    (sourceFamily5.take 33) source5FaceCodes33 = true := by decide

def source5FaceCodes34 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 1, 2, 2]
theorem source5FaceRow34_checked : packetFaceRowB (sourceFamily5Chunk4.getD 2 default)
    (sourceFamily5.take 34) source5FaceCodes34 = true := by decide

def source5FaceCodes35 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2]
theorem source5FaceRow35_checked : packetFaceRowB (sourceFamily5Chunk4.getD 3 default)
    (sourceFamily5.take 35) source5FaceCodes35 = true := by decide

def source5FaceCodes36 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source5FaceRow36_checked : packetFaceRowB (sourceFamily5Chunk4.getD 4 default)
    (sourceFamily5.take 36) source5FaceCodes36 = true := by decide

def source5FaceCodes37 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2]
theorem source5FaceRow37_checked : packetFaceRowB (sourceFamily5Chunk4.getD 5 default)
    (sourceFamily5.take 37) source5FaceCodes37 = true := by decide

def source5FaceCodes38 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 2, 2]
theorem source5FaceRow38_checked : packetFaceRowB (sourceFamily5Chunk4.getD 6 default)
    (sourceFamily5.take 38) source5FaceCodes38 = true := by decide

def source5FaceCodes39 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source5FaceRow39_checked : packetFaceRowB (sourceFamily5Chunk4.getD 7 default)
    (sourceFamily5.take 39) source5FaceCodes39 = true := by decide

def source5FaceCodes40 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source5FaceRow40_checked : packetFaceRowB (sourceFamily5Chunk5.getD 0 default)
    (sourceFamily5.take 40) source5FaceCodes40 = true := by decide

def source5FaceCodes41 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 0, 0, 0, 0, 2]
theorem source5FaceRow41_checked : packetFaceRowB (sourceFamily5Chunk5.getD 1 default)
    (sourceFamily5.take 41) source5FaceCodes41 = true := by decide

def source5FaceCodes42 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 4, 3, 1, 2, 2, 2, 2, 2, 2]
theorem source5FaceRow42_checked : packetFaceRowB (sourceFamily5Chunk5.getD 2 default)
    (sourceFamily5.take 42) source5FaceCodes42 = true := by decide

def source5FaceCodes43 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 5, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2]
theorem source5FaceRow43_checked : packetFaceRowB (sourceFamily5Chunk5.getD 3 default)
    (sourceFamily5.take 43) source5FaceCodes43 = true := by decide

def source5FaceCodes44 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source5FaceRow44_checked : packetFaceRowB (sourceFamily5Chunk5.getD 4 default)
    (sourceFamily5.take 44) source5FaceCodes44 = true := by decide

def source5FaceCodes45 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
theorem source5FaceRow45_checked : packetFaceRowB (sourceFamily5Chunk5.getD 5 default)
    (sourceFamily5.take 45) source5FaceCodes45 = true := by decide

def source5FaceCodes46 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source5FaceRow46_checked : packetFaceRowB (sourceFamily5Chunk5.getD 6 default)
    (sourceFamily5.take 46) source5FaceCodes46 = true := by decide

def source5FaceCodes47 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2]
theorem source5FaceRow47_checked : packetFaceRowB (sourceFamily5Chunk5.getD 7 default)
    (sourceFamily5.take 47) source5FaceCodes47 = true := by decide


end SpectreGeometry.ReverseClusterTriangulation
