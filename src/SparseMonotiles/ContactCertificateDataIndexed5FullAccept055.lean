module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates19704 : MateCertificate 160 := ⟨76, 125, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 125) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 126 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 122 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 123 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 124))))))))⟩
def fullMates19705 : MateCertificate 160 := ⟨76, 125, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 125) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 124 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 123 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 122 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 126))))))))⟩
def fullMates19709 : MateCertificate 160 := ⟨76, 127, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 127) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 130 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 128 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 131 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 129))))))))⟩
def fullMates19710 : MateCertificate 160 := ⟨76, 127, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 127) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 129 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 131 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 128 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 130))))))))⟩
def fullAccept055 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm15 12 9187, .accepted fullMates19704⟩,
  ⟨Pose.ofCodes perm14 12 9187, .accepted fullMates19705⟩,
  ⟨Pose.ofCodes perm2 13 9189, .accepted fullMates19709⟩,
  ⟨Pose.ofCodes perm1 13 9189, .accepted fullMates19710⟩
]
theorem fullAccept055_checked : indexedValidate geometry fullAccept055 = true := by decide +kernel
theorem fullAccept055_length : fullAccept055.length = 4 := by rfl
def fullAccept055Output : List (Pose 5) := [Pose.ofCodes perm15 12 9187, Pose.ofCodes perm14 12 9187, Pose.ofCodes perm2 13 9189, Pose.ofCodes perm1 13 9189]
theorem fullAccept055_output : indexedAcceptedPoses fullAccept055 = fullAccept055Output := by rfl
#print axioms fullAccept055_checked
end SparseMonotiles.Contact.IndexedData5
