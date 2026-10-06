module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates15894 : MateCertificate 160 := ⟨60, 118, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then (if i.val < 65 then (if i.val < 62 then (if i.val < 61 then some 118 else some 140) else (if i.val < 63 then some 152 else (if i.val < 64 then some 159 else some 76))) else none) else none))) else none)⟩
def fullMates15931 : MateCertificate 160 := ⟨60, 159, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then (if i.val < 65 then (if i.val < 62 then (if i.val < 61 then some 159 else some 152) else (if i.val < 63 then some 140 else (if i.val < 64 then some 118 else some 76))) else none) else none))) else none)⟩
def fullMates17115 : MateCertificate 160 := ⟨65, 140, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then (if i.val < 65 then none else (if i.val < 67 then (if i.val < 66 then some 140 else some 159) else (if i.val < 68 then some 118 else (if i.val < 69 then some 152 else some 76)))) else none))) else none)⟩
def fullMates17122 : MateCertificate 160 := ⟨65, 152, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then (if i.val < 65 then none else (if i.val < 67 then (if i.val < 66 then some 152 else some 118) else (if i.val < 68 then some 159 else (if i.val < 69 then some 140 else some 76)))) else none))) else none)⟩
def fullAccept041 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm5 6 3025, .accepted fullMates15894⟩,
  ⟨Pose.ofCodes perm19 6 3025, .accepted fullMates15931⟩,
  ⟨Pose.ofCodes perm11 22 12629, .accepted fullMates17115⟩,
  ⟨Pose.ofCodes perm13 22 12629, .accepted fullMates17122⟩
]
theorem fullAccept041_checked : indexedValidate geometry fullAccept041 = true := by decide
theorem fullAccept041_length : fullAccept041.length = 4 := by rfl
def fullAccept041Output : List (Pose 5) := [Pose.ofCodes perm5 6 3025, Pose.ofCodes perm19 6 3025, Pose.ofCodes perm11 22 12629, Pose.ofCodes perm13 22 12629]
theorem fullAccept041_output : indexedAcceptedPoses fullAccept041 = fullAccept041Output := by rfl
#print axioms fullAccept041_checked
end SparseMonotiles.Contact.IndexedData5
