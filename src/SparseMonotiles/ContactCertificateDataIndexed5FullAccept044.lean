module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates19523 : MateCertificate 160 := ⟨76, 13, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 13) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 10 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 12 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 14 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 11))))))))⟩
def fullMates19524 : MateCertificate 160 := ⟨76, 13, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 13) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 11 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 14 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 12 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 10))))))))⟩
def fullMates19529 : MateCertificate 160 := ⟨76, 16, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 16) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 15 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 19 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 18 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 17))))))))⟩
def fullMates19530 : MateCertificate 160 := ⟨76, 16, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 16) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 17 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 18 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 19 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 15))))))))⟩
def fullAccept044 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm12 1 8405, .accepted fullMates19523⟩,
  ⟨Pose.ofCodes perm13 1 8405, .accepted fullMates19524⟩,
  ⟨Pose.ofCodes perm4 12 9187, .accepted fullMates19529⟩,
  ⟨Pose.ofCodes perm5 12 9187, .accepted fullMates19530⟩
]
theorem fullAccept044_checked : indexedValidate geometry fullAccept044 = true := by decide
theorem fullAccept044_length : fullAccept044.length = 4 := by rfl
def fullAccept044Output : List (Pose 5) := [Pose.ofCodes perm12 1 8405, Pose.ofCodes perm13 1 8405, Pose.ofCodes perm4 12 9187, Pose.ofCodes perm5 12 9187]
theorem fullAccept044_output : indexedAcceptedPoses fullAccept044 = fullAccept044Output := by rfl
#print axioms fullAccept044_checked
end SparseMonotiles.Contact.IndexedData5
