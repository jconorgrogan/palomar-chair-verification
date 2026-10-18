module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates24383 : MateCertificate 160 := ⟨96, 140, fun i => (if i.val < 80 then none else (if i.val < 120 then (if i.val < 100 then (if i.val < 90 then none else (if i.val < 95 then none else (if i.val < 97 then (if i.val < 96 then none else some 140) else (if i.val < 98 then some 159 else (if i.val < 99 then some 118 else some 152))))) else (if i.val < 110 then (if i.val < 105 then (if i.val < 102 then (if i.val < 101 then some 76 else none) else none) else none) else none)) else none))⟩
def fullMates24397 : MateCertificate 160 := ⟨96, 152, fun i => (if i.val < 80 then none else (if i.val < 120 then (if i.val < 100 then (if i.val < 90 then none else (if i.val < 95 then none else (if i.val < 97 then (if i.val < 96 then none else some 152) else (if i.val < 98 then some 118 else (if i.val < 99 then some 159 else some 140))))) else (if i.val < 110 then (if i.val < 105 then (if i.val < 102 then (if i.val < 101 then some 76 else none) else none) else none) else none)) else none))⟩
def fullMates25341 : MateCertificate 160 := ⟨101, 118, fun i => (if i.val < 80 then none else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then (if i.val < 105 then (if i.val < 102 then (if i.val < 101 then none else some 118) else (if i.val < 103 then some 76 else (if i.val < 104 then some 159 else some 152))) else (if i.val < 107 then (if i.val < 106 then some 140 else none) else none)) else none)) else none))⟩
def fullMates25395 : MateCertificate 160 := ⟨101, 159, fun i => (if i.val < 80 then none else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then (if i.val < 105 then (if i.val < 102 then (if i.val < 101 then none else some 159) else (if i.val < 103 then some 76 else (if i.val < 104 then some 118 else some 140))) else (if i.val < 107 then (if i.val < 106 then some 152 else none) else none)) else none)) else none))⟩
def fullAccept065 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm11 25 13781, .accepted fullMates24383⟩,
  ⟨Pose.ofCodes perm13 25 13781, .accepted fullMates24397⟩,
  ⟨Pose.ofCodes perm4 5 3001, .accepted fullMates25341⟩,
  ⟨Pose.ofCodes perm16 5 3001, .accepted fullMates25395⟩
]
theorem fullAccept065_checked : indexedValidate geometry fullAccept065 = true := by decide +kernel
theorem fullAccept065_length : fullAccept065.length = 4 := by rfl
def fullAccept065Output : List (Pose 5) := [Pose.ofCodes perm11 25 13781, Pose.ofCodes perm13 25 13781, Pose.ofCodes perm4 5 3001, Pose.ofCodes perm16 5 3001]
theorem fullAccept065_output : indexedAcceptedPoses fullAccept065 = fullAccept065Output := by rfl
#print axioms fullAccept065_checked
end SparseMonotiles.Contact.IndexedData5
