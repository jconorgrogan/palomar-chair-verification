module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates19686 : MateCertificate 160 := ⟨76, 111, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 111) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 113 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 115 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 112 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 114))))))))⟩
def fullMates19687 : MateCertificate 160 := ⟨76, 111, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 111) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 114 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 112 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 115 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 113))))))))⟩
def fullMates19695 : MateCertificate 160 := ⟨76, 117, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 117) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 119 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 120 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 121 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 116))))))))⟩
def fullMates19696 : MateCertificate 160 := ⟨76, 117, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 117) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 116 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 121 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 120 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 119))))))))⟩
def fullAccept054 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm1 19 13221, .accepted fullMates19686⟩,
  ⟨Pose.ofCodes perm2 19 13221, .accepted fullMates19687⟩,
  ⟨Pose.ofCodes perm5 30 14003, .accepted fullMates19695⟩,
  ⟨Pose.ofCodes perm4 30 14003, .accepted fullMates19696⟩
]
theorem fullAccept054_checked : indexedValidate geometry fullAccept054 = true := by decide +kernel
theorem fullAccept054_length : fullAccept054.length = 4 := by rfl
def fullAccept054Output : List (Pose 5) := [Pose.ofCodes perm1 19 13221, Pose.ofCodes perm2 19 13221, Pose.ofCodes perm5 30 14003, Pose.ofCodes perm4 30 14003]
theorem fullAccept054_output : indexedAcceptedPoses fullAccept054 = fullAccept054Output := by rfl
#print axioms fullAccept054_checked
end SparseMonotiles.Contact.IndexedData5
