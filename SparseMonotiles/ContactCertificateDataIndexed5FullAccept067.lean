module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates28340 : MateCertificate 160 := ⟨116, 118, fun i => (if i.val < 80 then none else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then (if i.val < 116 then none else some 118) else (if i.val < 118 then some 76 else (if i.val < 119 then none else some 159)))))) else (if i.val < 140 then (if i.val < 130 then (if i.val < 125 then (if i.val < 122 then (if i.val < 121 then some 152 else some 140) else none) else none) else none) else none)))⟩
def fullMates28371 : MateCertificate 160 := ⟨116, 159, fun i => (if i.val < 80 then none else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then (if i.val < 116 then none else some 159) else (if i.val < 118 then some 76 else (if i.val < 119 then none else some 118)))))) else (if i.val < 140 then (if i.val < 130 then (if i.val < 125 then (if i.val < 122 then (if i.val < 121 then some 140 else some 152) else none) else none) else none) else none)))⟩
def fullMates29505 : MateCertificate 160 := ⟨122, 140, fun i => (if i.val < 80 then none else (if i.val < 120 then none else (if i.val < 140 then (if i.val < 130 then (if i.val < 125 then (if i.val < 122 then none else (if i.val < 123 then some 140 else (if i.val < 124 then some 152 else some 159))) else (if i.val < 127 then (if i.val < 126 then some 76 else some 118) else none)) else none) else none)))⟩
def fullMates29521 : MateCertificate 160 := ⟨122, 152, fun i => (if i.val < 80 then none else (if i.val < 120 then none else (if i.val < 140 then (if i.val < 130 then (if i.val < 125 then (if i.val < 122 then none else (if i.val < 123 then some 152 else (if i.val < 124 then some 140 else some 118))) else (if i.val < 127 then (if i.val < 126 then some 76 else some 159) else none)) else none) else none)))⟩
def fullAccept067 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm4 29 13977, .accepted fullMates28340⟩,
  ⟨Pose.ofCodes perm16 29 13977, .accepted fullMates28371⟩,
  ⟨Pose.ofCodes perm10 3 2833, .accepted fullMates29505⟩,
  ⟨Pose.ofCodes perm14 3 2833, .accepted fullMates29521⟩
]
theorem fullAccept067_checked : indexedValidate geometry fullAccept067 = true := by decide +kernel
theorem fullAccept067_length : fullAccept067.length = 4 := by rfl
def fullAccept067Output : List (Pose 5) := [Pose.ofCodes perm4 29 13977, Pose.ofCodes perm16 29 13977, Pose.ofCodes perm10 3 2833, Pose.ofCodes perm14 3 2833]
theorem fullAccept067_output : indexedAcceptedPoses fullAccept067 = fullAccept067Output := by rfl
#print axioms fullAccept067_checked
end SparseMonotiles.Contact.IndexedData5
