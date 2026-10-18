module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates34287 : MateCertificate 160 := ⟨148, 140, fun i => (if i.val < 80 then none else (if i.val < 120 then none else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then none else (if i.val < 147 then none else (if i.val < 148 then none else (if i.val < 149 then some 140 else some 152)))) else (if i.val < 155 then (if i.val < 152 then (if i.val < 151 then some 159 else some 76) else (if i.val < 153 then none else (if i.val < 154 then some 118 else none))) else none)))))⟩
def fullMates34294 : MateCertificate 160 := ⟨148, 152, fun i => (if i.val < 80 then none else (if i.val < 120 then none else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then none else (if i.val < 147 then none else (if i.val < 148 then none else (if i.val < 149 then some 152 else some 140)))) else (if i.val < 155 then (if i.val < 152 then (if i.val < 151 then some 118 else some 76) else (if i.val < 153 then none else (if i.val < 154 then some 159 else none))) else none)))))⟩
def fullMates35272 : MateCertificate 160 := ⟨154, 118, fun i => (if i.val < 80 then none else (if i.val < 120 then none else (if i.val < 140 then none else (if i.val < 150 then none else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then none else (if i.val < 154 then none else some 118))) else (if i.val < 157 then (if i.val < 156 then some 140 else some 152) else (if i.val < 158 then some 159 else (if i.val < 159 then some 76 else none))))))))⟩
def fullMates35295 : MateCertificate 160 := ⟨154, 159, fun i => (if i.val < 80 then none else (if i.val < 120 then none else (if i.val < 140 then none else (if i.val < 150 then none else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then none else (if i.val < 154 then none else some 159))) else (if i.val < 157 then (if i.val < 156 then some 152 else some 140) else (if i.val < 158 then some 118 else (if i.val < 159 then some 76 else none))))))))⟩
def fullAccept070 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm10 23 12633, .accepted fullMates34287⟩,
  ⟨Pose.ofCodes perm14 23 12633, .accepted fullMates34294⟩,
  ⟨Pose.ofCodes perm5 15 4401, .accepted fullMates35272⟩,
  ⟨Pose.ofCodes perm19 15 4401, .accepted fullMates35295⟩
]
theorem fullAccept070_checked : indexedValidate geometry fullAccept070 = true := by decide +kernel
theorem fullAccept070_length : fullAccept070.length = 4 := by rfl
def fullAccept070Output : List (Pose 5) := [Pose.ofCodes perm10 23 12633, Pose.ofCodes perm14 23 12633, Pose.ofCodes perm5 15 4401, Pose.ofCodes perm19 15 4401]
theorem fullAccept070_output : indexedAcceptedPoses fullAccept070 = fullAccept070Output := by rfl
#print axioms fullAccept070_checked
end SparseMonotiles.Contact.IndexedData5
