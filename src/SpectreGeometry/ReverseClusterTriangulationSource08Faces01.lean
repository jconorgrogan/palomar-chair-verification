module

public import SpectreGeometry.ReverseClusterTriangulationSource08Data
public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def source8FaceCodes24 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem source8FaceRow24_checked : packetFaceRowB (sourceFamily8Chunk3.getD 0 default)
    (sourceFamily8.take 24) source8FaceCodes24 = true := by decide

def source8FaceCodes25 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 2, 1, 1, 2, 2]
theorem source8FaceRow25_checked : packetFaceRowB (sourceFamily8Chunk3.getD 1 default)
    (sourceFamily8.take 25) source8FaceCodes25 = true := by decide

def source8FaceCodes26 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2]
theorem source8FaceRow26_checked : packetFaceRowB (sourceFamily8Chunk3.getD 2 default)
    (sourceFamily8.take 26) source8FaceCodes26 = true := by decide

def source8FaceCodes27 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source8FaceRow27_checked : packetFaceRowB (sourceFamily8Chunk3.getD 3 default)
    (sourceFamily8.take 27) source8FaceCodes27 = true := by decide

def source8FaceCodes28 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 2]
theorem source8FaceRow28_checked : packetFaceRowB (sourceFamily8Chunk3.getD 4 default)
    (sourceFamily8.take 28) source8FaceCodes28 = true := by decide

def source8FaceCodes29 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 2]
theorem source8FaceRow29_checked : packetFaceRowB (sourceFamily8Chunk3.getD 5 default)
    (sourceFamily8.take 29) source8FaceCodes29 = true := by decide

def source8FaceCodes30 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source8FaceRow30_checked : packetFaceRowB (sourceFamily8Chunk3.getD 6 default)
    (sourceFamily8.take 30) source8FaceCodes30 = true := by decide

def source8FaceCodes31 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source8FaceRow31_checked : packetFaceRowB (sourceFamily8Chunk3.getD 7 default)
    (sourceFamily8.take 31) source8FaceCodes31 = true := by decide

def source8FaceCodes32 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 0, 0, 0, 0, 2]
theorem source8FaceRow32_checked : packetFaceRowB (sourceFamily8Chunk4.getD 0 default)
    (sourceFamily8.take 32) source8FaceCodes32 = true := by decide

def source8FaceCodes33 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 4, 4, 3, 1, 2, 2, 2, 2, 2, 2]
theorem source8FaceRow33_checked : packetFaceRowB (sourceFamily8Chunk4.getD 1 default)
    (sourceFamily8.take 33) source8FaceCodes33 = true := by decide

def source8FaceCodes34 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2]
theorem source8FaceRow34_checked : packetFaceRowB (sourceFamily8Chunk4.getD 2 default)
    (sourceFamily8.take 34) source8FaceCodes34 = true := by decide

def source8FaceCodes35 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source8FaceRow35_checked : packetFaceRowB (sourceFamily8Chunk4.getD 3 default)
    (sourceFamily8.take 35) source8FaceCodes35 = true := by decide

def source8FaceCodes36 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source8FaceRow36_checked : packetFaceRowB (sourceFamily8Chunk4.getD 4 default)
    (sourceFamily8.take 36) source8FaceCodes36 = true := by decide

def source8FaceCodes37 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2]
theorem source8FaceRow37_checked : packetFaceRowB (sourceFamily8Chunk4.getD 5 default)
    (sourceFamily8.take 37) source8FaceCodes37 = true := by decide

def source8FaceCodes38 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 2]
theorem source8FaceRow38_checked : packetFaceRowB (sourceFamily8Chunk4.getD 6 default)
    (sourceFamily8.take 38) source8FaceCodes38 = true := by decide

def source8FaceCodes39 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source8FaceRow39_checked : packetFaceRowB (sourceFamily8Chunk4.getD 7 default)
    (sourceFamily8.take 39) source8FaceCodes39 = true := by decide

def source8FaceCodes40 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source8FaceRow40_checked : packetFaceRowB (sourceFamily8Chunk5.getD 0 default)
    (sourceFamily8.take 40) source8FaceCodes40 = true := by decide

def source8FaceCodes41 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 0, 0, 0, 0, 2]
theorem source8FaceRow41_checked : packetFaceRowB (sourceFamily8Chunk5.getD 1 default)
    (sourceFamily8.take 41) source8FaceCodes41 = true := by decide

def source8FaceCodes42 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 2]
theorem source8FaceRow42_checked : packetFaceRowB (sourceFamily8Chunk5.getD 2 default)
    (sourceFamily8.take 42) source8FaceCodes42 = true := by decide

def source8FaceCodes43 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 2, 2, 1, 1, 2, 2]
theorem source8FaceRow43_checked : packetFaceRowB (sourceFamily8Chunk5.getD 3 default)
    (sourceFamily8.take 43) source8FaceCodes43 = true := by decide

def source8FaceCodes44 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source8FaceRow44_checked : packetFaceRowB (sourceFamily8Chunk5.getD 4 default)
    (sourceFamily8.take 44) source8FaceCodes44 = true := by decide

def source8FaceCodes45 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
theorem source8FaceRow45_checked : packetFaceRowB (sourceFamily8Chunk5.getD 5 default)
    (sourceFamily8.take 45) source8FaceCodes45 = true := by decide

def source8FaceCodes46 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source8FaceRow46_checked : packetFaceRowB (sourceFamily8Chunk5.getD 6 default)
    (sourceFamily8.take 46) source8FaceCodes46 = true := by decide

def source8FaceCodes47 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2]
theorem source8FaceRow47_checked : packetFaceRowB (sourceFamily8Chunk5.getD 7 default)
    (sourceFamily8.take 47) source8FaceCodes47 = true := by decide


end SpectreGeometry.ReverseClusterTriangulation
