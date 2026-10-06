module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates19618 : MateCertificate 160 := ⟨76, 72, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 72) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 70 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 73 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 71 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 74))))))))⟩
def fullMates19619 : MateCertificate 160 := ⟨76, 72, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 72) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 74 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 71 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 73 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 70))))))))⟩
def fullMates19626 : MateCertificate 160 := ⟨76, 75, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 75) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 80 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 79 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 78 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 77))))))))⟩
def fullMates19627 : MateCertificate 160 := ⟨76, 75, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 75) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 77 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 78 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 79 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 80))))))))⟩
def fullAccept050 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm8 13 9189, .accepted fullMates19618⟩,
  ⟨Pose.ofCodes perm11 13 9189, .accepted fullMates19619⟩,
  ⟨Pose.ofCodes perm3 30 14003, .accepted fullMates19626⟩,
  ⟨Pose.ofCodes perm0 30 14003, .accepted fullMates19627⟩
]
theorem fullAccept050_checked : indexedValidate geometry fullAccept050 = true := by decide
theorem fullAccept050_length : fullAccept050.length = 4 := by rfl
def fullAccept050Output : List (Pose 5) := [Pose.ofCodes perm8 13 9189, Pose.ofCodes perm11 13 9189, Pose.ofCodes perm3 30 14003, Pose.ofCodes perm0 30 14003]
theorem fullAccept050_output : indexedAcceptedPoses fullAccept050 = fullAccept050Output := by rfl
#print axioms fullAccept050_checked
end SparseMonotiles.Contact.IndexedData5
