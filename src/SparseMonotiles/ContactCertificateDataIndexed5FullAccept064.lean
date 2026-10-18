module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates21981 : MateCertificate 160 := ⟨86, 140, fun i => (if i.val < 80 then none else (if i.val < 120 then (if i.val < 100 then (if i.val < 90 then (if i.val < 85 then none else (if i.val < 87 then (if i.val < 86 then none else some 140) else (if i.val < 88 then some 118 else (if i.val < 89 then some 76 else some 159)))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 91 then some 152 else none) else none) else none)) else none) else none))⟩
def fullMates21997 : MateCertificate 160 := ⟨86, 152, fun i => (if i.val < 80 then none else (if i.val < 120 then (if i.val < 100 then (if i.val < 90 then (if i.val < 85 then none else (if i.val < 87 then (if i.val < 86 then none else some 152) else (if i.val < 88 then some 159 else (if i.val < 89 then some 76 else some 118)))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 91 then some 140 else none) else none) else none)) else none) else none))⟩
def fullMates23177 : MateCertificate 160 := ⟨91, 118, fun i => (if i.val < 80 then none else (if i.val < 120 then (if i.val < 100 then (if i.val < 90 then none else (if i.val < 95 then (if i.val < 92 then (if i.val < 91 then none else some 118) else (if i.val < 93 then some 140 else (if i.val < 94 then some 152 else some 159))) else (if i.val < 97 then (if i.val < 96 then some 76 else none) else none))) else none) else none))⟩
def fullMates23231 : MateCertificate 160 := ⟨91, 159, fun i => (if i.val < 80 then none else (if i.val < 120 then (if i.val < 100 then (if i.val < 90 then none else (if i.val < 95 then (if i.val < 92 then (if i.val < 91 then none else some 159) else (if i.val < 93 then some 152 else (if i.val < 94 then some 140 else some 118))) else (if i.val < 97 then (if i.val < 96 then some 76 else none) else none))) else none) else none))⟩
def fullAccept064 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm9 17 12409, .accepted fullMates21981⟩,
  ⟨Pose.ofCodes perm15 17 12409, .accepted fullMates21997⟩,
  ⟨Pose.ofCodes perm5 9 4177, .accepted fullMates23177⟩,
  ⟨Pose.ofCodes perm19 9 4177, .accepted fullMates23231⟩
]
theorem fullAccept064_checked : indexedValidate geometry fullAccept064 = true := by decide +kernel
theorem fullAccept064_length : fullAccept064.length = 4 := by rfl
def fullAccept064Output : List (Pose 5) := [Pose.ofCodes perm9 17 12409, Pose.ofCodes perm15 17 12409, Pose.ofCodes perm5 9 4177, Pose.ofCodes perm19 9 4177]
theorem fullAccept064_output : indexedAcceptedPoses fullAccept064 = fullAccept064Output := by rfl
#print axioms fullAccept064_checked
end SparseMonotiles.Contact.IndexedData5
