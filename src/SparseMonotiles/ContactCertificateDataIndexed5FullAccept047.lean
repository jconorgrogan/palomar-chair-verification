module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates19571 : MateCertificate 160 := ⟨76, 41, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 41) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 44 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 42 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 40 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 43))))))))⟩
def fullMates19572 : MateCertificate 160 := ⟨76, 41, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 41) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 43 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 40 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 42 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 44))))))))⟩
def fullMates19578 : MateCertificate 160 := ⟨76, 45, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 45) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 49 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 48 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 47 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 46))))))))⟩
def fullMates19579 : MateCertificate 160 := ⟨76, 45, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 45) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 46 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 47 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 48 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 49))))))))⟩
def fullAccept047 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm7 1 8405, .accepted fullMates19571⟩,
  ⟨Pose.ofCodes perm6 1 8405, .accepted fullMates19572⟩,
  ⟨Pose.ofCodes perm3 18 13219, .accepted fullMates19578⟩,
  ⟨Pose.ofCodes perm0 18 13219, .accepted fullMates19579⟩
]
theorem fullAccept047_checked : indexedValidate geometry fullAccept047 = true := by decide
theorem fullAccept047_length : fullAccept047.length = 4 := by rfl
def fullAccept047Output : List (Pose 5) := [Pose.ofCodes perm7 1 8405, Pose.ofCodes perm6 1 8405, Pose.ofCodes perm3 18 13219, Pose.ofCodes perm0 18 13219]
theorem fullAccept047_output : indexedAcceptedPoses fullAccept047 = fullAccept047Output := by rfl
#print axioms fullAccept047_checked
end SparseMonotiles.Contact.IndexedData5
