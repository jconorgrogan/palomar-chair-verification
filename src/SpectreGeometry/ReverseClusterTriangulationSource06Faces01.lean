module

public import SpectreGeometry.ReverseClusterTriangulationSource06Data
public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def source6FaceCodes24 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem source6FaceRow24_checked : packetFaceRowB (sourceFamily6Chunk3.getD 0 default)
    (sourceFamily6.take 24) source6FaceCodes24 = true := by decide

def source6FaceCodes25 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 2, 1, 1, 2, 2]
theorem source6FaceRow25_checked : packetFaceRowB (sourceFamily6Chunk3.getD 1 default)
    (sourceFamily6.take 25) source6FaceCodes25 = true := by decide

def source6FaceCodes26 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2]
theorem source6FaceRow26_checked : packetFaceRowB (sourceFamily6Chunk3.getD 2 default)
    (sourceFamily6.take 26) source6FaceCodes26 = true := by decide

def source6FaceCodes27 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source6FaceRow27_checked : packetFaceRowB (sourceFamily6Chunk3.getD 3 default)
    (sourceFamily6.take 27) source6FaceCodes27 = true := by decide

def source6FaceCodes28 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 2]
theorem source6FaceRow28_checked : packetFaceRowB (sourceFamily6Chunk3.getD 4 default)
    (sourceFamily6.take 28) source6FaceCodes28 = true := by decide

def source6FaceCodes29 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source6FaceRow29_checked : packetFaceRowB (sourceFamily6Chunk3.getD 5 default)
    (sourceFamily6.take 29) source6FaceCodes29 = true := by decide

def source6FaceCodes30 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source6FaceRow30_checked : packetFaceRowB (sourceFamily6Chunk3.getD 6 default)
    (sourceFamily6.take 30) source6FaceCodes30 = true := by decide

def source6FaceCodes31 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source6FaceRow31_checked : packetFaceRowB (sourceFamily6Chunk3.getD 7 default)
    (sourceFamily6.take 31) source6FaceCodes31 = true := by decide

def source6FaceCodes32 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 0, 2, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2]
theorem source6FaceRow32_checked : packetFaceRowB (sourceFamily6Chunk4.getD 0 default)
    (sourceFamily6.take 32) source6FaceCodes32 = true := by decide

def source6FaceCodes33 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem source6FaceRow33_checked : packetFaceRowB (sourceFamily6Chunk4.getD 1 default)
    (sourceFamily6.take 33) source6FaceCodes33 = true := by decide

def source6FaceCodes34 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 1, 2, 2]
theorem source6FaceRow34_checked : packetFaceRowB (sourceFamily6Chunk4.getD 2 default)
    (sourceFamily6.take 34) source6FaceCodes34 = true := by decide

def source6FaceCodes35 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2]
theorem source6FaceRow35_checked : packetFaceRowB (sourceFamily6Chunk4.getD 3 default)
    (sourceFamily6.take 35) source6FaceCodes35 = true := by decide

def source6FaceCodes36 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source6FaceRow36_checked : packetFaceRowB (sourceFamily6Chunk4.getD 4 default)
    (sourceFamily6.take 36) source6FaceCodes36 = true := by decide

def source6FaceCodes37 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2]
theorem source6FaceRow37_checked : packetFaceRowB (sourceFamily6Chunk4.getD 5 default)
    (sourceFamily6.take 37) source6FaceCodes37 = true := by decide

def source6FaceCodes38 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 2]
theorem source6FaceRow38_checked : packetFaceRowB (sourceFamily6Chunk4.getD 6 default)
    (sourceFamily6.take 38) source6FaceCodes38 = true := by decide

def source6FaceCodes39 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source6FaceRow39_checked : packetFaceRowB (sourceFamily6Chunk4.getD 7 default)
    (sourceFamily6.take 39) source6FaceCodes39 = true := by decide

def source6FaceCodes40 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source6FaceRow40_checked : packetFaceRowB (sourceFamily6Chunk5.getD 0 default)
    (sourceFamily6.take 40) source6FaceCodes40 = true := by decide

def source6FaceCodes41 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 2]
theorem source6FaceRow41_checked : packetFaceRowB (sourceFamily6Chunk5.getD 1 default)
    (sourceFamily6.take 41) source6FaceCodes41 = true := by decide

def source6FaceCodes42 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem source6FaceRow42_checked : packetFaceRowB (sourceFamily6Chunk5.getD 2 default)
    (sourceFamily6.take 42) source6FaceCodes42 = true := by decide

def source6FaceCodes43 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2]
theorem source6FaceRow43_checked : packetFaceRowB (sourceFamily6Chunk5.getD 3 default)
    (sourceFamily6.take 43) source6FaceCodes43 = true := by decide

def source6FaceCodes44 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 4, 2]
theorem source6FaceRow44_checked : packetFaceRowB (sourceFamily6Chunk5.getD 4 default)
    (sourceFamily6.take 44) source6FaceCodes44 = true := by decide

def source6FaceCodes45 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1]
theorem source6FaceRow45_checked : packetFaceRowB (sourceFamily6Chunk5.getD 5 default)
    (sourceFamily6.take 45) source6FaceCodes45 = true := by decide

def source6FaceCodes46 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 4, 3, 1, 2]
theorem source6FaceRow46_checked : packetFaceRowB (sourceFamily6Chunk5.getD 6 default)
    (sourceFamily6.take 46) source6FaceCodes46 = true := by decide

def source6FaceCodes47 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 3, 0, 0, 4, 4, 3, 0, 2, 2]
theorem source6FaceRow47_checked : packetFaceRowB (sourceFamily6Chunk5.getD 7 default)
    (sourceFamily6.take 47) source6FaceCodes47 = true := by decide


end SpectreGeometry.ReverseClusterTriangulation
