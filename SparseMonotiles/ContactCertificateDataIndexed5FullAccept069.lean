module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates32423 : MateCertificate 160 := ⟨137, 140, fun i => (if i.val < 80 then none else (if i.val < 120 then none else (if i.val < 140 then (if i.val < 130 then none else (if i.val < 135 then none else (if i.val < 137 then none else (if i.val < 138 then some 140 else (if i.val < 139 then some 118 else some 76))))) else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then none else some 159) else (if i.val < 143 then some 152 else none)) else none) else none))))⟩
def fullMates32430 : MateCertificate 160 := ⟨137, 152, fun i => (if i.val < 80 then none else (if i.val < 120 then none else (if i.val < 140 then (if i.val < 130 then none else (if i.val < 135 then none else (if i.val < 137 then none else (if i.val < 138 then some 152 else (if i.val < 139 then some 159 else some 76))))) else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then none else some 118) else (if i.val < 143 then some 140 else none)) else none) else none))))⟩
def fullMates33461 : MateCertificate 160 := ⟨143, 140, fun i => (if i.val < 80 then none else (if i.val < 120 then none else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then none else (if i.val < 143 then none else (if i.val < 144 then some 140 else some 76))) else (if i.val < 147 then (if i.val < 146 then some 152 else some 118) else (if i.val < 148 then some 159 else none))) else none))))⟩
def fullMates33470 : MateCertificate 160 := ⟨143, 152, fun i => (if i.val < 80 then none else (if i.val < 120 then none else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then none else (if i.val < 143 then none else (if i.val < 144 then some 152 else some 76))) else (if i.val < 147 then (if i.val < 146 then some 140 else some 159) else (if i.val < 148 then some 118 else none))) else none))))⟩
def fullAccept069 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm9 27 13809, .accepted fullMates32423⟩,
  ⟨Pose.ofCodes perm15 27 13809, .accepted fullMates32430⟩,
  ⟨Pose.ofCodes perm8 7 3029, .accepted fullMates33461⟩,
  ⟨Pose.ofCodes perm12 7 3029, .accepted fullMates33470⟩
]
theorem fullAccept069_checked : indexedValidate geometry fullAccept069 = true := by decide +kernel
theorem fullAccept069_length : fullAccept069.length = 4 := by rfl
def fullAccept069Output : List (Pose 5) := [Pose.ofCodes perm9 27 13809, Pose.ofCodes perm15 27 13809, Pose.ofCodes perm8 7 3029, Pose.ofCodes perm12 7 3029]
theorem fullAccept069_output : indexedAcceptedPoses fullAccept069 = fullAccept069Output := by rfl
#print axioms fullAccept069_checked
end SparseMonotiles.Contact.IndexedData5
