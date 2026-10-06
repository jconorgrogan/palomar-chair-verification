module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates30580 : MateCertificate 160 := ⟨127, 76, fun i => (if i.val < 80 then none else (if i.val < 120 then none else (if i.val < 140 then (if i.val < 130 then (if i.val < 125 then none else (if i.val < 127 then none else (if i.val < 128 then some 76 else (if i.val < 129 then some 140 else some 159)))) else (if i.val < 135 then (if i.val < 132 then (if i.val < 131 then some 118 else some 152) else none) else none)) else none)))⟩
def fullMates30581 : MateCertificate 160 := ⟨127, 76, fun i => (if i.val < 80 then none else (if i.val < 120 then none else (if i.val < 140 then (if i.val < 130 then (if i.val < 125 then none else (if i.val < 127 then none else (if i.val < 128 then some 76 else (if i.val < 129 then some 152 else some 118)))) else (if i.val < 135 then (if i.val < 132 then (if i.val < 131 then some 159 else some 140) else none) else none)) else none)))⟩
def fullMates31529 : MateCertificate 160 := ⟨132, 118, fun i => (if i.val < 80 then none else (if i.val < 120 then none else (if i.val < 140 then (if i.val < 130 then none else (if i.val < 135 then (if i.val < 132 then none else (if i.val < 133 then some 118 else (if i.val < 134 then some 159 else some 140))) else (if i.val < 137 then (if i.val < 136 then some 76 else some 152) else none))) else none)))⟩
def fullMates31575 : MateCertificate 160 := ⟨132, 159, fun i => (if i.val < 80 then none else (if i.val < 120 then none else (if i.val < 140 then (if i.val < 130 then none else (if i.val < 135 then (if i.val < 132 then none else (if i.val < 133 then some 159 else (if i.val < 134 then some 118 else some 152))) else (if i.val < 137 then (if i.val < 136 then some 76 else some 140) else none))) else none)))⟩
def fullAccept068 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm1 19 12437, .accepted fullMates30580⟩,
  ⟨Pose.ofCodes perm2 19 12437, .accepted fullMates30581⟩,
  ⟨Pose.ofCodes perm7 11 4205, .accepted fullMates31529⟩,
  ⟨Pose.ofCodes perm17 11 4205, .accepted fullMates31575⟩
]
theorem fullAccept068_checked : indexedValidate geometry fullAccept068 = true := by decide +kernel
theorem fullAccept068_length : fullAccept068.length = 4 := by rfl
def fullAccept068Output : List (Pose 5) := [Pose.ofCodes perm1 19 12437, Pose.ofCodes perm2 19 12437, Pose.ofCodes perm7 11 4205, Pose.ofCodes perm17 11 4205]
theorem fullAccept068_output : indexedAcceptedPoses fullAccept068 = fullAccept068Output := by rfl
#print axioms fullAccept068_checked
end SparseMonotiles.Contact.IndexedData5
