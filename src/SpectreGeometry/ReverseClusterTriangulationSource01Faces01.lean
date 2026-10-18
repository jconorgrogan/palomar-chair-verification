module

public import SpectreGeometry.ReverseClusterTriangulationSource01Data
public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def source1FaceCodes24 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem source1FaceRow24_checked : packetFaceRowB (sourceFamily1Chunk3.getD 0 default)
    (sourceFamily1.take 24) source1FaceCodes24 = true := by decide

def source1FaceCodes25 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 2, 1, 1, 2, 2]
theorem source1FaceRow25_checked : packetFaceRowB (sourceFamily1Chunk3.getD 1 default)
    (sourceFamily1.take 25) source1FaceCodes25 = true := by decide

def source1FaceCodes26 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2]
theorem source1FaceRow26_checked : packetFaceRowB (sourceFamily1Chunk3.getD 2 default)
    (sourceFamily1.take 26) source1FaceCodes26 = true := by decide

def source1FaceCodes27 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source1FaceRow27_checked : packetFaceRowB (sourceFamily1Chunk3.getD 3 default)
    (sourceFamily1.take 27) source1FaceCodes27 = true := by decide

def source1FaceCodes28 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 2]
theorem source1FaceRow28_checked : packetFaceRowB (sourceFamily1Chunk3.getD 4 default)
    (sourceFamily1.take 28) source1FaceCodes28 = true := by decide

def source1FaceCodes29 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]
theorem source1FaceRow29_checked : packetFaceRowB (sourceFamily1Chunk3.getD 5 default)
    (sourceFamily1.take 29) source1FaceCodes29 = true := by decide

def source1FaceCodes30 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source1FaceRow30_checked : packetFaceRowB (sourceFamily1Chunk3.getD 6 default)
    (sourceFamily1.take 30) source1FaceCodes30 = true := by decide

def source1FaceCodes31 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source1FaceRow31_checked : packetFaceRowB (sourceFamily1Chunk3.getD 7 default)
    (sourceFamily1.take 31) source1FaceCodes31 = true := by decide

def source1FaceCodes32 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 0, 2, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2]
theorem source1FaceRow32_checked : packetFaceRowB (sourceFamily1Chunk4.getD 0 default)
    (sourceFamily1.take 32) source1FaceCodes32 = true := by decide

def source1FaceCodes33 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem source1FaceRow33_checked : packetFaceRowB (sourceFamily1Chunk4.getD 1 default)
    (sourceFamily1.take 33) source1FaceCodes33 = true := by decide

def source1FaceCodes34 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 1, 2, 2]
theorem source1FaceRow34_checked : packetFaceRowB (sourceFamily1Chunk4.getD 2 default)
    (sourceFamily1.take 34) source1FaceCodes34 = true := by decide

def source1FaceCodes35 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2]
theorem source1FaceRow35_checked : packetFaceRowB (sourceFamily1Chunk4.getD 3 default)
    (sourceFamily1.take 35) source1FaceCodes35 = true := by decide

def source1FaceCodes36 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
theorem source1FaceRow36_checked : packetFaceRowB (sourceFamily1Chunk4.getD 4 default)
    (sourceFamily1.take 36) source1FaceCodes36 = true := by decide

def source1FaceCodes37 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2]
theorem source1FaceRow37_checked : packetFaceRowB (sourceFamily1Chunk4.getD 5 default)
    (sourceFamily1.take 37) source1FaceCodes37 = true := by decide

def source1FaceCodes38 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]
theorem source1FaceRow38_checked : packetFaceRowB (sourceFamily1Chunk4.getD 6 default)
    (sourceFamily1.take 38) source1FaceCodes38 = true := by decide

def source1FaceCodes39 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]
theorem source1FaceRow39_checked : packetFaceRowB (sourceFamily1Chunk4.getD 7 default)
    (sourceFamily1.take 39) source1FaceCodes39 = true := by decide

def source1FaceCodes40 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0]
theorem source1FaceRow40_checked : packetFaceRowB (sourceFamily1Chunk5.getD 0 default)
    (sourceFamily1.take 40) source1FaceCodes40 = true := by decide

def source1FaceCodes41 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 2, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2]
theorem source1FaceRow41_checked : packetFaceRowB (sourceFamily1Chunk5.getD 1 default)
    (sourceFamily1.take 41) source1FaceCodes41 = true := by decide

def source1FaceCodes42 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
theorem source1FaceRow42_checked : packetFaceRowB (sourceFamily1Chunk5.getD 2 default)
    (sourceFamily1.take 42) source1FaceCodes42 = true := by decide

def source1FaceCodes43 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2]
theorem source1FaceRow43_checked : packetFaceRowB (sourceFamily1Chunk5.getD 3 default)
    (sourceFamily1.take 43) source1FaceCodes43 = true := by decide

def source1FaceCodes44 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 4, 2]
theorem source1FaceRow44_checked : packetFaceRowB (sourceFamily1Chunk5.getD 4 default)
    (sourceFamily1.take 44) source1FaceCodes44 = true := by decide

def source1FaceCodes45 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
theorem source1FaceRow45_checked : packetFaceRowB (sourceFamily1Chunk5.getD 5 default)
    (sourceFamily1.take 45) source1FaceCodes45 = true := by decide

def source1FaceCodes46 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
theorem source1FaceRow46_checked : packetFaceRowB (sourceFamily1Chunk5.getD 6 default)
    (sourceFamily1.take 46) source1FaceCodes46 = true := by decide

def source1FaceCodes47 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2]
theorem source1FaceRow47_checked : packetFaceRowB (sourceFamily1Chunk5.getD 7 default)
    (sourceFamily1.take 47) source1FaceCodes47 = true := by decide


end SpectreGeometry.ReverseClusterTriangulation
