module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates19638 : MateCertificate 160 := ⟨76, 81, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 81) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 83 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 85 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 82 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 84))))))))⟩
def fullMates19639 : MateCertificate 160 := ⟨76, 81, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 81) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 84 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 82 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 85 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 83))))))))⟩
def fullMates19646 : MateCertificate 160 := ⟨76, 88, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 88) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 87 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 86 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 90 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 89))))))))⟩
def fullMates19647 : MateCertificate 160 := ⟨76, 88, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 88) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 89 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 90 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 86 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 87))))))))⟩
def fullAccept051 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm1 1 8405, .accepted fullMates19638⟩,
  ⟨Pose.ofCodes perm2 1 8405, .accepted fullMates19639⟩,
  ⟨Pose.ofCodes perm9 12 9187, .accepted fullMates19646⟩,
  ⟨Pose.ofCodes perm10 12 9187, .accepted fullMates19647⟩
]
theorem fullAccept051_checked : indexedValidate geometry fullAccept051 = true := by decide
theorem fullAccept051_length : fullAccept051.length = 4 := by rfl
def fullAccept051Output : List (Pose 5) := [Pose.ofCodes perm1 1 8405, Pose.ofCodes perm2 1 8405, Pose.ofCodes perm9 12 9187, Pose.ofCodes perm10 12 9187]
theorem fullAccept051_output : indexedAcceptedPoses fullAccept051 = fullAccept051Output := by rfl
#print axioms fullAccept051_checked
end SparseMonotiles.Contact.IndexedData5
