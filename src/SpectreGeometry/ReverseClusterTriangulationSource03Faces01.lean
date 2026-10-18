module

public import SpectreGeometry.ReverseClusterTriangulationSource03Data
public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def source3FaceCodes24 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem source3FaceRow24_checked : packetFaceRowB (sourceFamily3Chunk3.getD 0 default)
    (sourceFamily3.take 24) source3FaceCodes24 = true := by decide

def source3FaceCodes25 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 2, 1, 1, 2, 2]
theorem source3FaceRow25_checked : packetFaceRowB (sourceFamily3Chunk3.getD 1 default)
    (sourceFamily3.take 25) source3FaceCodes25 = true := by decide

def source3FaceCodes26 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2]
theorem source3FaceRow26_checked : packetFaceRowB (sourceFamily3Chunk3.getD 2 default)
    (sourceFamily3.take 26) source3FaceCodes26 = true := by decide

def source3FaceCodes27 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source3FaceRow27_checked : packetFaceRowB (sourceFamily3Chunk3.getD 3 default)
    (sourceFamily3.take 27) source3FaceCodes27 = true := by decide

def source3FaceCodes28 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 2]
theorem source3FaceRow28_checked : packetFaceRowB (sourceFamily3Chunk3.getD 4 default)
    (sourceFamily3.take 28) source3FaceCodes28 = true := by decide

def source3FaceCodes29 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source3FaceRow29_checked : packetFaceRowB (sourceFamily3Chunk3.getD 5 default)
    (sourceFamily3.take 29) source3FaceCodes29 = true := by decide

def source3FaceCodes30 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source3FaceRow30_checked : packetFaceRowB (sourceFamily3Chunk3.getD 6 default)
    (sourceFamily3.take 30) source3FaceCodes30 = true := by decide

def source3FaceCodes31 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source3FaceRow31_checked : packetFaceRowB (sourceFamily3Chunk3.getD 7 default)
    (sourceFamily3.take 31) source3FaceCodes31 = true := by decide

def source3FaceCodes32 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 0, 2]
theorem source3FaceRow32_checked : packetFaceRowB (sourceFamily3Chunk4.getD 0 default)
    (sourceFamily3.take 32) source3FaceCodes32 = true := by decide

def source3FaceCodes33 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem source3FaceRow33_checked : packetFaceRowB (sourceFamily3Chunk4.getD 1 default)
    (sourceFamily3.take 33) source3FaceCodes33 = true := by decide

def source3FaceCodes34 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 1, 2, 2]
theorem source3FaceRow34_checked : packetFaceRowB (sourceFamily3Chunk4.getD 2 default)
    (sourceFamily3.take 34) source3FaceCodes34 = true := by decide

def source3FaceCodes35 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2]
theorem source3FaceRow35_checked : packetFaceRowB (sourceFamily3Chunk4.getD 3 default)
    (sourceFamily3.take 35) source3FaceCodes35 = true := by decide

def source3FaceCodes36 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source3FaceRow36_checked : packetFaceRowB (sourceFamily3Chunk4.getD 4 default)
    (sourceFamily3.take 36) source3FaceCodes36 = true := by decide

def source3FaceCodes37 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2]
theorem source3FaceRow37_checked : packetFaceRowB (sourceFamily3Chunk4.getD 5 default)
    (sourceFamily3.take 37) source3FaceCodes37 = true := by decide

def source3FaceCodes38 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 2, 2]
theorem source3FaceRow38_checked : packetFaceRowB (sourceFamily3Chunk4.getD 6 default)
    (sourceFamily3.take 38) source3FaceCodes38 = true := by decide

def source3FaceCodes39 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source3FaceRow39_checked : packetFaceRowB (sourceFamily3Chunk4.getD 7 default)
    (sourceFamily3.take 39) source3FaceCodes39 = true := by decide

def source3FaceCodes40 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source3FaceRow40_checked : packetFaceRowB (sourceFamily3Chunk5.getD 0 default)
    (sourceFamily3.take 40) source3FaceCodes40 = true := by decide

def source3FaceCodes41 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 0, 0, 0, 0, 2]
theorem source3FaceRow41_checked : packetFaceRowB (sourceFamily3Chunk5.getD 1 default)
    (sourceFamily3.take 41) source3FaceCodes41 = true := by decide

def source3FaceCodes42 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 4, 3, 1, 2, 2, 2, 2, 2, 2]
theorem source3FaceRow42_checked : packetFaceRowB (sourceFamily3Chunk5.getD 2 default)
    (sourceFamily3.take 42) source3FaceCodes42 = true := by decide

def source3FaceCodes43 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 5, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2]
theorem source3FaceRow43_checked : packetFaceRowB (sourceFamily3Chunk5.getD 3 default)
    (sourceFamily3.take 43) source3FaceCodes43 = true := by decide

def source3FaceCodes44 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source3FaceRow44_checked : packetFaceRowB (sourceFamily3Chunk5.getD 4 default)
    (sourceFamily3.take 44) source3FaceCodes44 = true := by decide

def source3FaceCodes45 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
theorem source3FaceRow45_checked : packetFaceRowB (sourceFamily3Chunk5.getD 5 default)
    (sourceFamily3.take 45) source3FaceCodes45 = true := by decide

def source3FaceCodes46 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source3FaceRow46_checked : packetFaceRowB (sourceFamily3Chunk5.getD 6 default)
    (sourceFamily3.take 46) source3FaceCodes46 = true := by decide

def source3FaceCodes47 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2]
theorem source3FaceRow47_checked : packetFaceRowB (sourceFamily3Chunk5.getD 7 default)
    (sourceFamily3.take 47) source3FaceCodes47 = true := by decide


end SpectreGeometry.ReverseClusterTriangulation
