module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates13671 : MateCertificate 160 := ⟨50, 140, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then (if i.val < 50 then none else (if i.val < 55 then (if i.val < 52 then (if i.val < 51 then some 140 else some 118) else (if i.val < 53 then some 76 else (if i.val < 54 then some 159 else some 152))) else none)) else none)) else none)⟩
def fullMates13682 : MateCertificate 160 := ⟨50, 152, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then (if i.val < 50 then none else (if i.val < 55 then (if i.val < 52 then (if i.val < 51 then some 152 else some 159) else (if i.val < 53 then some 76 else (if i.val < 54 then some 118 else some 140))) else none)) else none)) else none)⟩
def fullMates14871 : MateCertificate 160 := ⟨55, 140, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then (if i.val < 50 then none else (if i.val < 55 then none else (if i.val < 57 then (if i.val < 56 then some 140 else some 76) else (if i.val < 58 then some 152 else (if i.val < 59 then some 118 else some 159))))) else none)) else none)⟩
def fullMates14878 : MateCertificate 160 := ⟨55, 152, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then (if i.val < 50 then none else (if i.val < 55 then none else (if i.val < 57 then (if i.val < 56 then some 152 else some 76) else (if i.val < 58 then some 140 else (if i.val < 59 then some 159 else some 118))))) else none)) else none)⟩
def fullAccept040 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm9 10 4201, .accepted fullMates13671⟩,
  ⟨Pose.ofCodes perm15 10 4201, .accepted fullMates13682⟩,
  ⟨Pose.ofCodes perm8 26 13805, .accepted fullMates14871⟩,
  ⟨Pose.ofCodes perm12 26 13805, .accepted fullMates14878⟩
]
theorem fullAccept040_checked : indexedValidate geometry fullAccept040 = true := by decide
theorem fullAccept040_length : fullAccept040.length = 4 := by rfl
def fullAccept040Output : List (Pose 5) := [Pose.ofCodes perm9 10 4201, Pose.ofCodes perm15 10 4201, Pose.ofCodes perm8 26 13805, Pose.ofCodes perm12 26 13805]
theorem fullAccept040_output : indexedAcceptedPoses fullAccept040 = fullAccept040Output := by rfl
#print axioms fullAccept040_checked
end SparseMonotiles.Contact.IndexedData5
