module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates19588 : MateCertificate 160 := ⟨76, 52, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 52) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 53 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 54 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 50 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 51))))))))⟩
def fullMates19589 : MateCertificate 160 := ⟨76, 52, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 52) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 51 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 50 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 54 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 53))))))))⟩
def fullMates19595 : MateCertificate 160 := ⟨76, 56, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 56) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 59 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 57 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 55 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 58))))))))⟩
def fullMates19596 : MateCertificate 160 := ⟨76, 56, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 56) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 58 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 55 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 57 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 59))))))))⟩
def fullAccept048 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm10 18 13219, .accepted fullMates19588⟩,
  ⟨Pose.ofCodes perm9 18 13219, .accepted fullMates19589⟩,
  ⟨Pose.ofCodes perm7 19 13221, .accepted fullMates19595⟩,
  ⟨Pose.ofCodes perm6 19 13221, .accepted fullMates19596⟩
]
theorem fullAccept048_checked : indexedValidate geometry fullAccept048 = true := by decide
theorem fullAccept048_length : fullAccept048.length = 4 := by rfl
def fullAccept048Output : List (Pose 5) := [Pose.ofCodes perm10 18 13219, Pose.ofCodes perm9 18 13219, Pose.ofCodes perm7 19 13221, Pose.ofCodes perm6 19 13221]
theorem fullAccept048_output : indexedAcceptedPoses fullAccept048 = fullAccept048Output := by rfl
#print axioms fullAccept048_checked
end SparseMonotiles.Contact.IndexedData5
