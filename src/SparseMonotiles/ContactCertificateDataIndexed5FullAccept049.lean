module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates19604 : MateCertificate 160 := ⟨76, 64, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 64) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 60 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 61 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 62 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 63))))))))⟩
def fullMates19605 : MateCertificate 160 := ⟨76, 64, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 64) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 63 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 62 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 61 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 60))))))))⟩
def fullMates19614 : MateCertificate 160 := ⟨76, 69, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 69) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 66 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 68 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 65 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 67))))))))⟩
def fullMates19615 : MateCertificate 160 := ⟨76, 69, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 69) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 67 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 65 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 68 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 66))))))))⟩
def fullAccept049 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm16 12 9187, .accepted fullMates19604⟩,
  ⟨Pose.ofCodes perm19 12 9187, .accepted fullMates19605⟩,
  ⟨Pose.ofCodes perm17 19 13221, .accepted fullMates19614⟩,
  ⟨Pose.ofCodes perm18 19 13221, .accepted fullMates19615⟩
]
theorem fullAccept049_checked : indexedValidate geometry fullAccept049 = true := by decide
theorem fullAccept049_length : fullAccept049.length = 4 := by rfl
def fullAccept049Output : List (Pose 5) := [Pose.ofCodes perm16 12 9187, Pose.ofCodes perm19 12 9187, Pose.ofCodes perm17 19 13221, Pose.ofCodes perm18 19 13221]
theorem fullAccept049_output : indexedAcceptedPoses fullAccept049 = fullAccept049Output := by rfl
#print axioms fullAccept049_checked
end SparseMonotiles.Contact.IndexedData5
