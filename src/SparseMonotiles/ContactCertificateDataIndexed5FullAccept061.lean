module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates20766 : MateCertificate 160 := ⟨81, 76, fun i => (if i.val < 80 then none else (if i.val < 120 then (if i.val < 100 then (if i.val < 90 then (if i.val < 85 then (if i.val < 82 then (if i.val < 81 then none else some 76) else (if i.val < 83 then some 140 else (if i.val < 84 then some 159 else some 118))) else (if i.val < 87 then (if i.val < 86 then some 152 else none) else none)) else none) else none) else none))⟩
def fullMates20767 : MateCertificate 160 := ⟨81, 76, fun i => (if i.val < 80 then none else (if i.val < 120 then (if i.val < 100 then (if i.val < 90 then (if i.val < 85 then (if i.val < 82 then (if i.val < 81 then none else some 76) else (if i.val < 83 then some 152 else (if i.val < 84 then some 118 else some 159))) else (if i.val < 87 then (if i.val < 86 then some 140 else none) else none)) else none) else none) else none))⟩
def fullMates20774 : MateCertificate 160 := ⟨81, 81, fun i => (if i.val < 80 then none else (if i.val < 120 then (if i.val < 100 then (if i.val < 90 then (if i.val < 85 then (if i.val < 82 then (if i.val < 81 then none else some 81) else none) else (if i.val < 87 then (if i.val < 86 then none else some 91) else none)) else (if i.val < 95 then (if i.val < 92 then (if i.val < 91 then none else some 122) else none) else (if i.val < 97 then (if i.val < 96 then none else some 132) else none))) else (if i.val < 110 then (if i.val < 105 then (if i.val < 102 then (if i.val < 101 then none else some 86) else none) else (if i.val < 107 then (if i.val < 106 then none else some 96) else none)) else (if i.val < 115 then (if i.val < 112 then (if i.val < 111 then none else some 127) else none) else (if i.val < 117 then (if i.val < 116 then none else some 137) else none)))) else (if i.val < 140 then (if i.val < 130 then (if i.val < 125 then (if i.val < 122 then none else (if i.val < 123 then some 101 else none)) else (if i.val < 127 then none else (if i.val < 128 then some 111 else none))) else (if i.val < 135 then (if i.val < 132 then none else (if i.val < 133 then some 143 else none)) else (if i.val < 137 then none else (if i.val < 138 then some 154 else none)))) else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then none else (if i.val < 143 then none else (if i.val < 144 then some 106 else none))) else (if i.val < 147 then none else (if i.val < 148 then none else (if i.val < 149 then some 116 else none)))) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then none else (if i.val < 154 then none else some 148))) else none)))))⟩
def fullMates20775 : MateCertificate 160 := ⟨81, 81, fun i => (if i.val < 80 then none else (if i.val < 120 then (if i.val < 100 then (if i.val < 90 then (if i.val < 85 then (if i.val < 82 then (if i.val < 81 then none else some 81) else none) else (if i.val < 87 then (if i.val < 86 then none else some 101) else none)) else (if i.val < 95 then (if i.val < 92 then (if i.val < 91 then none else some 86) else none) else (if i.val < 97 then (if i.val < 96 then none else some 106) else none))) else (if i.val < 110 then (if i.val < 105 then (if i.val < 102 then (if i.val < 101 then none else some 122) else none) else (if i.val < 107 then (if i.val < 106 then none else some 143) else none)) else (if i.val < 115 then (if i.val < 112 then (if i.val < 111 then none else some 127) else none) else (if i.val < 117 then (if i.val < 116 then none else some 148) else none)))) else (if i.val < 140 then (if i.val < 130 then (if i.val < 125 then (if i.val < 122 then none else (if i.val < 123 then some 91 else none)) else (if i.val < 127 then none else (if i.val < 128 then some 111 else none))) else (if i.val < 135 then (if i.val < 132 then none else (if i.val < 133 then some 96 else none)) else (if i.val < 137 then none else (if i.val < 138 then some 116 else none)))) else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then none else (if i.val < 143 then none else (if i.val < 144 then some 132 else none))) else (if i.val < 147 then none else (if i.val < 148 then none else (if i.val < 149 then some 154 else none)))) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then none else (if i.val < 154 then none else some 137))) else none)))))⟩
def fullAccept061 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm1 1 2805, .accepted fullMates20766⟩,
  ⟨Pose.ofCodes perm2 1 2805, .accepted fullMates20767⟩,
  ⟨Pose.ofCodes perm1 1 5606, .accepted fullMates20774⟩,
  ⟨Pose.ofCodes perm2 1 5606, .accepted fullMates20775⟩
]
theorem fullAccept061_checked : indexedValidate geometry fullAccept061 = true := by decide +kernel
theorem fullAccept061_length : fullAccept061.length = 4 := by rfl
def fullAccept061Output : List (Pose 5) := [Pose.ofCodes perm1 1 2805, Pose.ofCodes perm2 1 2805, Pose.ofCodes perm1 1 5606, Pose.ofCodes perm2 1 5606]
theorem fullAccept061_output : indexedAcceptedPoses fullAccept061 = fullAccept061Output := by rfl
#print axioms fullAccept061_checked
end SparseMonotiles.Contact.IndexedData5
