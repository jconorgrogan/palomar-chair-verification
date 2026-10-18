module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates19735 : MateCertificate 160 := ⟨76, 144, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 144) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 146 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 143 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 145 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 147))))))))⟩
def fullMates19736 : MateCertificate 160 := ⟨76, 144, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 144) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 147 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 145 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 143 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 146))))))))⟩
def fullMates19745 : MateCertificate 160 := ⟨76, 151, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 151) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 153 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 148 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 149 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 150))))))))⟩
def fullMates19746 : MateCertificate 160 := ⟨76, 151, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 151) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 150 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 149 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 148 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 153))))))))⟩
def fullAccept057 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm6 13 9189, .accepted fullMates19735⟩,
  ⟨Pose.ofCodes perm7 13 9189, .accepted fullMates19736⟩,
  ⟨Pose.ofCodes perm15 30 14003, .accepted fullMates19745⟩,
  ⟨Pose.ofCodes perm14 30 14003, .accepted fullMates19746⟩
]
theorem fullAccept057_checked : indexedValidate geometry fullAccept057 = true := by decide +kernel
theorem fullAccept057_length : fullAccept057.length = 4 := by rfl
def fullAccept057Output : List (Pose 5) := [Pose.ofCodes perm6 13 9189, Pose.ofCodes perm7 13 9189, Pose.ofCodes perm15 30 14003, Pose.ofCodes perm14 30 14003]
theorem fullAccept057_output : indexedAcceptedPoses fullAccept057 = fullAccept057Output := by rfl
#print axioms fullAccept057_checked
end SparseMonotiles.Contact.IndexedData5
