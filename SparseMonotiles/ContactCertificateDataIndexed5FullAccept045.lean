module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates19538 : MateCertificate 160 := ⟨76, 22, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 22) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 20 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 23 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 21 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 24))))))))⟩
def fullMates19539 : MateCertificate 160 := ⟨76, 22, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 22) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 24 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 21 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 23 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 20))))))))⟩
def fullMates19549 : MateCertificate 160 := ⟨76, 28, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 28) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 27 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 26 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 25 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 29))))))))⟩
def fullMates19550 : MateCertificate 160 := ⟨76, 28, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 28) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 29 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 25 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 26 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 27))))))))⟩
def fullAccept045 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm8 1 8405, .accepted fullMates19538⟩,
  ⟨Pose.ofCodes perm11 1 8405, .accepted fullMates19539⟩,
  ⟨Pose.ofCodes perm14 18 13219, .accepted fullMates19549⟩,
  ⟨Pose.ofCodes perm15 18 13219, .accepted fullMates19550⟩
]
theorem fullAccept045_checked : indexedValidate geometry fullAccept045 = true := by decide
theorem fullAccept045_length : fullAccept045.length = 4 := by rfl
def fullAccept045Output : List (Pose 5) := [Pose.ofCodes perm8 1 8405, Pose.ofCodes perm11 1 8405, Pose.ofCodes perm14 18 13219, Pose.ofCodes perm15 18 13219]
theorem fullAccept045_output : indexedAcceptedPoses fullAccept045 = fullAccept045Output := by rfl
#print axioms fullAccept045_checked
end SparseMonotiles.Contact.IndexedData5
