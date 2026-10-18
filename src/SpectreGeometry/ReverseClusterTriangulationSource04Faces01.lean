module

public import SpectreGeometry.ReverseClusterTriangulationSource04Data
public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def source4FaceCodes24 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 2]
theorem source4FaceRow24_checked : packetFaceRowB (sourceFamily4Chunk3.getD 0 default)
    (sourceFamily4.take 24) source4FaceCodes24 = true := by decide

def source4FaceCodes25 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 2, 2, 1, 1, 2, 2]
theorem source4FaceRow25_checked : packetFaceRowB (sourceFamily4Chunk3.getD 1 default)
    (sourceFamily4.take 25) source4FaceCodes25 = true := by decide

def source4FaceCodes26 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source4FaceRow26_checked : packetFaceRowB (sourceFamily4Chunk3.getD 2 default)
    (sourceFamily4.take 26) source4FaceCodes26 = true := by decide

def source4FaceCodes27 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source4FaceRow27_checked : packetFaceRowB (sourceFamily4Chunk3.getD 3 default)
    (sourceFamily4.take 27) source4FaceCodes27 = true := by decide

def source4FaceCodes28 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source4FaceRow28_checked : packetFaceRowB (sourceFamily4Chunk3.getD 4 default)
    (sourceFamily4.take 28) source4FaceCodes28 = true := by decide

def source4FaceCodes29 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2]
theorem source4FaceRow29_checked : packetFaceRowB (sourceFamily4Chunk3.getD 5 default)
    (sourceFamily4.take 29) source4FaceCodes29 = true := by decide

def source4FaceCodes30 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source4FaceRow30_checked : packetFaceRowB (sourceFamily4Chunk3.getD 6 default)
    (sourceFamily4.take 30) source4FaceCodes30 = true := by decide

def source4FaceCodes31 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source4FaceRow31_checked : packetFaceRowB (sourceFamily4Chunk3.getD 7 default)
    (sourceFamily4.take 31) source4FaceCodes31 = true := by decide

def source4FaceCodes32 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 2]
theorem source4FaceRow32_checked : packetFaceRowB (sourceFamily4Chunk4.getD 0 default)
    (sourceFamily4.take 32) source4FaceCodes32 = true := by decide

def source4FaceCodes33 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem source4FaceRow33_checked : packetFaceRowB (sourceFamily4Chunk4.getD 1 default)
    (sourceFamily4.take 33) source4FaceCodes33 = true := by decide

def source4FaceCodes34 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 1, 2, 2]
theorem source4FaceRow34_checked : packetFaceRowB (sourceFamily4Chunk4.getD 2 default)
    (sourceFamily4.take 34) source4FaceCodes34 = true := by decide

def source4FaceCodes35 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source4FaceRow35_checked : packetFaceRowB (sourceFamily4Chunk4.getD 3 default)
    (sourceFamily4.take 35) source4FaceCodes35 = true := by decide

def source4FaceCodes36 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source4FaceRow36_checked : packetFaceRowB (sourceFamily4Chunk4.getD 4 default)
    (sourceFamily4.take 36) source4FaceCodes36 = true := by decide

def source4FaceCodes37 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2]
theorem source4FaceRow37_checked : packetFaceRowB (sourceFamily4Chunk4.getD 5 default)
    (sourceFamily4.take 37) source4FaceCodes37 = true := by decide

def source4FaceCodes38 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 2]
theorem source4FaceRow38_checked : packetFaceRowB (sourceFamily4Chunk4.getD 6 default)
    (sourceFamily4.take 38) source4FaceCodes38 = true := by decide

def source4FaceCodes39 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source4FaceRow39_checked : packetFaceRowB (sourceFamily4Chunk4.getD 7 default)
    (sourceFamily4.take 39) source4FaceCodes39 = true := by decide

def source4FaceCodes40 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source4FaceRow40_checked : packetFaceRowB (sourceFamily4Chunk5.getD 0 default)
    (sourceFamily4.take 40) source4FaceCodes40 = true := by decide

def source4FaceCodes41 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 0, 0, 0, 0, 2]
theorem source4FaceRow41_checked : packetFaceRowB (sourceFamily4Chunk5.getD 1 default)
    (sourceFamily4.take 41) source4FaceCodes41 = true := by decide

def source4FaceCodes42 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 2]
theorem source4FaceRow42_checked : packetFaceRowB (sourceFamily4Chunk5.getD 2 default)
    (sourceFamily4.take 42) source4FaceCodes42 = true := by decide

def source4FaceCodes43 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 2, 2, 1, 1, 2, 2]
theorem source4FaceRow43_checked : packetFaceRowB (sourceFamily4Chunk5.getD 3 default)
    (sourceFamily4.take 43) source4FaceCodes43 = true := by decide

def source4FaceCodes44 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source4FaceRow44_checked : packetFaceRowB (sourceFamily4Chunk5.getD 4 default)
    (sourceFamily4.take 44) source4FaceCodes44 = true := by decide

def source4FaceCodes45 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
theorem source4FaceRow45_checked : packetFaceRowB (sourceFamily4Chunk5.getD 5 default)
    (sourceFamily4.take 45) source4FaceCodes45 = true := by decide

def source4FaceCodes46 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source4FaceRow46_checked : packetFaceRowB (sourceFamily4Chunk5.getD 6 default)
    (sourceFamily4.take 46) source4FaceCodes46 = true := by decide

def source4FaceCodes47 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2]
theorem source4FaceRow47_checked : packetFaceRowB (sourceFamily4Chunk5.getD 7 default)
    (sourceFamily4.take 47) source4FaceCodes47 = true := by decide


end SpectreGeometry.ReverseClusterTriangulation
