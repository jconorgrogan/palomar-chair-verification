module

public import SpectreGeometry.ReverseClusterTriangulationSource02Data
public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def source2FaceCodes24 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 2]
theorem source2FaceRow24_checked : packetFaceRowB (sourceFamily2Chunk3.getD 0 default)
    (sourceFamily2.take 24) source2FaceCodes24 = true := by decide

def source2FaceCodes25 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 2, 2, 1, 1, 2, 2]
theorem source2FaceRow25_checked : packetFaceRowB (sourceFamily2Chunk3.getD 1 default)
    (sourceFamily2.take 25) source2FaceCodes25 = true := by decide

def source2FaceCodes26 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source2FaceRow26_checked : packetFaceRowB (sourceFamily2Chunk3.getD 2 default)
    (sourceFamily2.take 26) source2FaceCodes26 = true := by decide

def source2FaceCodes27 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source2FaceRow27_checked : packetFaceRowB (sourceFamily2Chunk3.getD 3 default)
    (sourceFamily2.take 27) source2FaceCodes27 = true := by decide

def source2FaceCodes28 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source2FaceRow28_checked : packetFaceRowB (sourceFamily2Chunk3.getD 4 default)
    (sourceFamily2.take 28) source2FaceCodes28 = true := by decide

def source2FaceCodes29 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2]
theorem source2FaceRow29_checked : packetFaceRowB (sourceFamily2Chunk3.getD 5 default)
    (sourceFamily2.take 29) source2FaceCodes29 = true := by decide

def source2FaceCodes30 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source2FaceRow30_checked : packetFaceRowB (sourceFamily2Chunk3.getD 6 default)
    (sourceFamily2.take 30) source2FaceCodes30 = true := by decide

def source2FaceCodes31 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source2FaceRow31_checked : packetFaceRowB (sourceFamily2Chunk3.getD 7 default)
    (sourceFamily2.take 31) source2FaceCodes31 = true := by decide

def source2FaceCodes32 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 2]
theorem source2FaceRow32_checked : packetFaceRowB (sourceFamily2Chunk4.getD 0 default)
    (sourceFamily2.take 32) source2FaceCodes32 = true := by decide

def source2FaceCodes33 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem source2FaceRow33_checked : packetFaceRowB (sourceFamily2Chunk4.getD 1 default)
    (sourceFamily2.take 33) source2FaceCodes33 = true := by decide

def source2FaceCodes34 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 1, 2, 2]
theorem source2FaceRow34_checked : packetFaceRowB (sourceFamily2Chunk4.getD 2 default)
    (sourceFamily2.take 34) source2FaceCodes34 = true := by decide

def source2FaceCodes35 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source2FaceRow35_checked : packetFaceRowB (sourceFamily2Chunk4.getD 3 default)
    (sourceFamily2.take 35) source2FaceCodes35 = true := by decide

def source2FaceCodes36 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source2FaceRow36_checked : packetFaceRowB (sourceFamily2Chunk4.getD 4 default)
    (sourceFamily2.take 36) source2FaceCodes36 = true := by decide

def source2FaceCodes37 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2]
theorem source2FaceRow37_checked : packetFaceRowB (sourceFamily2Chunk4.getD 5 default)
    (sourceFamily2.take 37) source2FaceCodes37 = true := by decide

def source2FaceCodes38 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 2]
theorem source2FaceRow38_checked : packetFaceRowB (sourceFamily2Chunk4.getD 6 default)
    (sourceFamily2.take 38) source2FaceCodes38 = true := by decide

def source2FaceCodes39 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source2FaceRow39_checked : packetFaceRowB (sourceFamily2Chunk4.getD 7 default)
    (sourceFamily2.take 39) source2FaceCodes39 = true := by decide

def source2FaceCodes40 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source2FaceRow40_checked : packetFaceRowB (sourceFamily2Chunk5.getD 0 default)
    (sourceFamily2.take 40) source2FaceCodes40 = true := by decide

def source2FaceCodes41 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 0, 0, 0, 0, 2]
theorem source2FaceRow41_checked : packetFaceRowB (sourceFamily2Chunk5.getD 1 default)
    (sourceFamily2.take 41) source2FaceCodes41 = true := by decide

def source2FaceCodes42 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 2]
theorem source2FaceRow42_checked : packetFaceRowB (sourceFamily2Chunk5.getD 2 default)
    (sourceFamily2.take 42) source2FaceCodes42 = true := by decide

def source2FaceCodes43 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 2, 2, 1, 1, 2, 2]
theorem source2FaceRow43_checked : packetFaceRowB (sourceFamily2Chunk5.getD 3 default)
    (sourceFamily2.take 43) source2FaceCodes43 = true := by decide

def source2FaceCodes44 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source2FaceRow44_checked : packetFaceRowB (sourceFamily2Chunk5.getD 4 default)
    (sourceFamily2.take 44) source2FaceCodes44 = true := by decide

def source2FaceCodes45 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
theorem source2FaceRow45_checked : packetFaceRowB (sourceFamily2Chunk5.getD 5 default)
    (sourceFamily2.take 45) source2FaceCodes45 = true := by decide

def source2FaceCodes46 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source2FaceRow46_checked : packetFaceRowB (sourceFamily2Chunk5.getD 6 default)
    (sourceFamily2.take 46) source2FaceCodes46 = true := by decide

def source2FaceCodes47 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2]
theorem source2FaceRow47_checked : packetFaceRowB (sourceFamily2Chunk5.getD 7 default)
    (sourceFamily2.take 47) source2FaceCodes47 = true := by decide


end SpectreGeometry.ReverseClusterTriangulation
