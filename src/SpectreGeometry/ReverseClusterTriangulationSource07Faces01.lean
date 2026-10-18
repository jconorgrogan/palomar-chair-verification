module

public import SpectreGeometry.ReverseClusterTriangulationSource07Data
public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def source7FaceCodes24 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem source7FaceRow24_checked : packetFaceRowB (sourceFamily7Chunk3.getD 0 default)
    (sourceFamily7.take 24) source7FaceCodes24 = true := by decide

def source7FaceCodes25 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 2, 1, 1, 2, 2]
theorem source7FaceRow25_checked : packetFaceRowB (sourceFamily7Chunk3.getD 1 default)
    (sourceFamily7.take 25) source7FaceCodes25 = true := by decide

def source7FaceCodes26 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2]
theorem source7FaceRow26_checked : packetFaceRowB (sourceFamily7Chunk3.getD 2 default)
    (sourceFamily7.take 26) source7FaceCodes26 = true := by decide

def source7FaceCodes27 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source7FaceRow27_checked : packetFaceRowB (sourceFamily7Chunk3.getD 3 default)
    (sourceFamily7.take 27) source7FaceCodes27 = true := by decide

def source7FaceCodes28 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 2]
theorem source7FaceRow28_checked : packetFaceRowB (sourceFamily7Chunk3.getD 4 default)
    (sourceFamily7.take 28) source7FaceCodes28 = true := by decide

def source7FaceCodes29 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 2, 2]
theorem source7FaceRow29_checked : packetFaceRowB (sourceFamily7Chunk3.getD 5 default)
    (sourceFamily7.take 29) source7FaceCodes29 = true := by decide

def source7FaceCodes30 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source7FaceRow30_checked : packetFaceRowB (sourceFamily7Chunk3.getD 6 default)
    (sourceFamily7.take 30) source7FaceCodes30 = true := by decide

def source7FaceCodes31 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source7FaceRow31_checked : packetFaceRowB (sourceFamily7Chunk3.getD 7 default)
    (sourceFamily7.take 31) source7FaceCodes31 = true := by decide

def source7FaceCodes32 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 0, 0, 0, 0, 2]
theorem source7FaceRow32_checked : packetFaceRowB (sourceFamily7Chunk4.getD 0 default)
    (sourceFamily7.take 32) source7FaceCodes32 = true := by decide

def source7FaceCodes33 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 4, 4, 3, 1, 2, 2, 2, 2, 2, 2]
theorem source7FaceRow33_checked : packetFaceRowB (sourceFamily7Chunk4.getD 1 default)
    (sourceFamily7.take 33) source7FaceCodes33 = true := by decide

def source7FaceCodes34 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2]
theorem source7FaceRow34_checked : packetFaceRowB (sourceFamily7Chunk4.getD 2 default)
    (sourceFamily7.take 34) source7FaceCodes34 = true := by decide

def source7FaceCodes35 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source7FaceRow35_checked : packetFaceRowB (sourceFamily7Chunk4.getD 3 default)
    (sourceFamily7.take 35) source7FaceCodes35 = true := by decide

def source7FaceCodes36 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source7FaceRow36_checked : packetFaceRowB (sourceFamily7Chunk4.getD 4 default)
    (sourceFamily7.take 36) source7FaceCodes36 = true := by decide

def source7FaceCodes37 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2]
theorem source7FaceRow37_checked : packetFaceRowB (sourceFamily7Chunk4.getD 5 default)
    (sourceFamily7.take 37) source7FaceCodes37 = true := by decide

def source7FaceCodes38 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 2]
theorem source7FaceRow38_checked : packetFaceRowB (sourceFamily7Chunk4.getD 6 default)
    (sourceFamily7.take 38) source7FaceCodes38 = true := by decide

def source7FaceCodes39 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source7FaceRow39_checked : packetFaceRowB (sourceFamily7Chunk4.getD 7 default)
    (sourceFamily7.take 39) source7FaceCodes39 = true := by decide

def source7FaceCodes40 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source7FaceRow40_checked : packetFaceRowB (sourceFamily7Chunk5.getD 0 default)
    (sourceFamily7.take 40) source7FaceCodes40 = true := by decide

def source7FaceCodes41 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 0, 0, 0, 0, 2]
theorem source7FaceRow41_checked : packetFaceRowB (sourceFamily7Chunk5.getD 1 default)
    (sourceFamily7.take 41) source7FaceCodes41 = true := by decide

def source7FaceCodes42 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 2]
theorem source7FaceRow42_checked : packetFaceRowB (sourceFamily7Chunk5.getD 2 default)
    (sourceFamily7.take 42) source7FaceCodes42 = true := by decide

def source7FaceCodes43 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 2, 2, 1, 1, 2, 2]
theorem source7FaceRow43_checked : packetFaceRowB (sourceFamily7Chunk5.getD 3 default)
    (sourceFamily7.take 43) source7FaceCodes43 = true := by decide

def source7FaceCodes44 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source7FaceRow44_checked : packetFaceRowB (sourceFamily7Chunk5.getD 4 default)
    (sourceFamily7.take 44) source7FaceCodes44 = true := by decide

def source7FaceCodes45 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
theorem source7FaceRow45_checked : packetFaceRowB (sourceFamily7Chunk5.getD 5 default)
    (sourceFamily7.take 45) source7FaceCodes45 = true := by decide

def source7FaceCodes46 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source7FaceRow46_checked : packetFaceRowB (sourceFamily7Chunk5.getD 6 default)
    (sourceFamily7.take 46) source7FaceCodes46 = true := by decide

def source7FaceCodes47 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2]
theorem source7FaceRow47_checked : packetFaceRowB (sourceFamily7Chunk5.getD 7 default)
    (sourceFamily7.take 47) source7FaceCodes47 = true := by decide


end SpectreGeometry.ReverseClusterTriangulation
