module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates19552 : MateCertificate 160 := ⟨76, 30, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 30) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 31 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 32 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 33 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 34))))))))⟩
def fullMates19553 : MateCertificate 160 := ⟨76, 30, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 30) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 34 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 33 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 32 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 31))))))))⟩
def fullMates19563 : MateCertificate 160 := ⟨76, 38, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 38) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 35 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 37 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 39 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 36))))))))⟩
def fullMates19564 : MateCertificate 160 := ⟨76, 38, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 38) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 36 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 39 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 37 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 35))))))))⟩
def fullAccept046 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm0 12 9187, .accepted fullMates19552⟩,
  ⟨Pose.ofCodes perm3 12 9187, .accepted fullMates19553⟩,
  ⟨Pose.ofCodes perm12 13 9189, .accepted fullMates19563⟩,
  ⟨Pose.ofCodes perm13 13 9189, .accepted fullMates19564⟩
]
theorem fullAccept046_checked : indexedValidate geometry fullAccept046 = true := by decide
theorem fullAccept046_length : fullAccept046.length = 4 := by rfl
def fullAccept046Output : List (Pose 5) := [Pose.ofCodes perm0 12 9187, Pose.ofCodes perm3 12 9187, Pose.ofCodes perm12 13 9189, Pose.ofCodes perm13 13 9189]
theorem fullAccept046_output : indexedAcceptedPoses fullAccept046 = fullAccept046Output := by rfl
#print axioms fullAccept046_checked
end SparseMonotiles.Contact.IndexedData5
