module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates19504 : MateCertificate 160 := ⟨76, 0, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 0) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 1 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 2 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 3 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 4))))))))⟩
def fullMates19505 : MateCertificate 160 := ⟨76, 0, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 0) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 4 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 3 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 2 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 1))))))))⟩
def fullMates19518 : MateCertificate 160 := ⟨76, 9, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 9) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 6 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 8 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 5 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 7))))))))⟩
def fullMates19519 : MateCertificate 160 := ⟨76, 9, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 9) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 7 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 5 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 8 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 6))))))))⟩
def fullAccept043 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm0 0 8403, .accepted fullMates19504⟩,
  ⟨Pose.ofCodes perm3 0 8403, .accepted fullMates19505⟩,
  ⟨Pose.ofCodes perm17 1 8405, .accepted fullMates19518⟩,
  ⟨Pose.ofCodes perm18 1 8405, .accepted fullMates19519⟩
]
theorem fullAccept043_checked : indexedValidate geometry fullAccept043 = true := by decide
theorem fullAccept043_length : fullAccept043.length = 4 := by rfl
def fullAccept043Output : List (Pose 5) := [Pose.ofCodes perm0 0 8403, Pose.ofCodes perm3 0 8403, Pose.ofCodes perm17 1 8405, Pose.ofCodes perm18 1 8405]
theorem fullAccept043_output : indexedAcceptedPoses fullAccept043 = fullAccept043Output := by rfl
#print axioms fullAccept043_checked
end SparseMonotiles.Contact.IndexedData5
