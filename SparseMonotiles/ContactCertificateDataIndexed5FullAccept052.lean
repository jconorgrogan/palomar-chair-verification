module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates19658 : MateCertificate 160 := ⟨76, 95, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 95) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 94 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 93 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 92 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 91))))))))⟩
def fullMates19659 : MateCertificate 160 := ⟨76, 95, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 95) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 91 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 92 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 93 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 94))))))))⟩
def fullMates19664 : MateCertificate 160 := ⟨76, 100, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 100) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 98 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 96 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 99 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 97))))))))⟩
def fullMates19665 : MateCertificate 160 := ⟨76, 100, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 100) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 97 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 99 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 96 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 98))))))))⟩
def fullAccept052 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm19 18 13219, .accepted fullMates19658⟩,
  ⟨Pose.ofCodes perm16 18 13219, .accepted fullMates19659⟩,
  ⟨Pose.ofCodes perm18 13 9189, .accepted fullMates19664⟩,
  ⟨Pose.ofCodes perm17 13 9189, .accepted fullMates19665⟩
]
theorem fullAccept052_checked : indexedValidate geometry fullAccept052 = true := by decide
theorem fullAccept052_length : fullAccept052.length = 4 := by rfl
def fullAccept052Output : List (Pose 5) := [Pose.ofCodes perm19 18 13219, Pose.ofCodes perm16 18 13219, Pose.ofCodes perm18 13 9189, Pose.ofCodes perm17 13 9189]
theorem fullAccept052_output : indexedAcceptedPoses fullAccept052 = fullAccept052Output := by rfl
#print axioms fullAccept052_checked
end SparseMonotiles.Contact.IndexedData5
