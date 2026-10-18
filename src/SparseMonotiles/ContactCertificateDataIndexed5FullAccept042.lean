module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates18080 : MateCertificate 160 := ⟨70, 118, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then (if i.val < 72 then (if i.val < 71 then some 118 else some 152) else (if i.val < 73 then some 76 else (if i.val < 74 then some 140 else some 159))) else none)))) else none)⟩
def fullMates18103 : MateCertificate 160 := ⟨70, 159, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then (if i.val < 72 then (if i.val < 71 then some 159 else some 140) else (if i.val < 73 then some 76 else (if i.val < 74 then some 152 else some 118))) else none)))) else none)⟩
def fullMates19050 : MateCertificate 160 := ⟨75, 76, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then some 76 else none) else (if i.val < 78 then some 159 else (if i.val < 79 then some 152 else some 140))))))) else (if i.val < 120 then (if i.val < 100 then (if i.val < 90 then (if i.val < 85 then (if i.val < 82 then (if i.val < 81 then some 118 else none) else none) else none) else none) else none) else none))⟩
def fullMates19051 : MateCertificate 160 := ⟨75, 76, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then some 76 else none) else (if i.val < 78 then some 118 else (if i.val < 79 then some 140 else some 152))))))) else (if i.val < 120 then (if i.val < 100 then (if i.val < 90 then (if i.val < 85 then (if i.val < 82 then (if i.val < 81 then some 159 else none) else none) else none) else none) else none) else none))⟩
def fullAccept042 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm6 14 4397, .accepted fullMates18080⟩,
  ⟨Pose.ofCodes perm18 14 4397, .accepted fullMates18103⟩,
  ⟨Pose.ofCodes perm3 30 14001, .accepted fullMates19050⟩,
  ⟨Pose.ofCodes perm0 30 14001, .accepted fullMates19051⟩
]
theorem fullAccept042_checked : indexedValidate geometry fullAccept042 = true := by decide
theorem fullAccept042_length : fullAccept042.length = 4 := by rfl
def fullAccept042Output : List (Pose 5) := [Pose.ofCodes perm6 14 4397, Pose.ofCodes perm18 14 4397, Pose.ofCodes perm3 30 14001, Pose.ofCodes perm0 30 14001]
theorem fullAccept042_output : indexedAcceptedPoses fullAccept042 = fullAccept042Output := by rfl
#print axioms fullAccept042_checked
end SparseMonotiles.Contact.IndexedData5
