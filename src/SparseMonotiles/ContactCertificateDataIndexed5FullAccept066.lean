module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates26525 : MateCertificate 160 := ⟨106, 118, fun i => (if i.val < 80 then none else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then (if i.val < 105 then none else (if i.val < 107 then (if i.val < 106 then none else some 118) else (if i.val < 108 then some 152 else (if i.val < 109 then some 76 else some 140)))) else (if i.val < 115 then (if i.val < 112 then (if i.val < 111 then some 159 else none) else none) else none))) else none))⟩
def fullMates26571 : MateCertificate 160 := ⟨106, 159, fun i => (if i.val < 80 then none else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then (if i.val < 105 then none else (if i.val < 107 then (if i.val < 106 then none else some 159) else (if i.val < 108 then some 140 else (if i.val < 109 then some 76 else some 152)))) else (if i.val < 115 then (if i.val < 112 then (if i.val < 111 then some 118 else none) else none) else none))) else none))⟩
def fullMates27402 : MateCertificate 160 := ⟨111, 76, fun i => (if i.val < 80 then none else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then (if i.val < 112 then (if i.val < 111 then none else some 76) else (if i.val < 113 then some 140 else (if i.val < 114 then some 159 else some 118))) else (if i.val < 117 then (if i.val < 116 then some 152 else none) else none)))) else none))⟩
def fullMates27403 : MateCertificate 160 := ⟨111, 76, fun i => (if i.val < 80 then none else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then (if i.val < 112 then (if i.val < 111 then none else some 76) else (if i.val < 113 then some 152 else (if i.val < 114 then some 118 else some 159))) else (if i.val < 117 then (if i.val < 116 then some 140 else none) else none)))) else none))⟩
def fullAccept066 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm6 21 12605, .accepted fullMates26525⟩,
  ⟨Pose.ofCodes perm18 21 12605, .accepted fullMates26571⟩,
  ⟨Pose.ofCodes perm1 13 4373, .accepted fullMates27402⟩,
  ⟨Pose.ofCodes perm2 13 4373, .accepted fullMates27403⟩
]
theorem fullAccept066_checked : indexedValidate geometry fullAccept066 = true := by decide +kernel
theorem fullAccept066_length : fullAccept066.length = 4 := by rfl
def fullAccept066Output : List (Pose 5) := [Pose.ofCodes perm6 21 12605, Pose.ofCodes perm18 21 12605, Pose.ofCodes perm1 13 4373, Pose.ofCodes perm2 13 4373]
theorem fullAccept066_output : indexedAcceptedPoses fullAccept066 = fullAccept066Output := by rfl
#print axioms fullAccept066_checked
end SparseMonotiles.Contact.IndexedData5
