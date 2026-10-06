module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates19722 : MateCertificate 160 := ⟨76, 135, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 135) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 133 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 136 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 134 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 132))))))))⟩
def fullMates19723 : MateCertificate 160 := ⟨76, 135, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 135) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 132 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 134 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 136 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 133))))))))⟩
def fullMates19727 : MateCertificate 160 := ⟨76, 139, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 139) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 138 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 137 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 142 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 141))))))))⟩
def fullMates19728 : MateCertificate 160 := ⟨76, 139, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 139) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 141 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 142 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 137 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 138))))))))⟩
def fullAccept056 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm13 19 13221, .accepted fullMates19722⟩,
  ⟨Pose.ofCodes perm12 19 13221, .accepted fullMates19723⟩,
  ⟨Pose.ofCodes perm9 30 14003, .accepted fullMates19727⟩,
  ⟨Pose.ofCodes perm10 30 14003, .accepted fullMates19728⟩
]
theorem fullAccept056_checked : indexedValidate geometry fullAccept056 = true := by decide +kernel
theorem fullAccept056_length : fullAccept056.length = 4 := by rfl
def fullAccept056Output : List (Pose 5) := [Pose.ofCodes perm13 19 13221, Pose.ofCodes perm12 19 13221, Pose.ofCodes perm9 30 14003, Pose.ofCodes perm10 30 14003]
theorem fullAccept056_output : indexedAcceptedPoses fullAccept056 = fullAccept056Output := by rfl
#print axioms fullAccept056_checked
end SparseMonotiles.Contact.IndexedData5
