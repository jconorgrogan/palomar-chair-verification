module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates8984 : MateCertificate 160 := ⟨30, 76, fun i => (if i.val < 80 then (if i.val < 40 then (if i.val < 20 then none else (if i.val < 30 then none else (if i.val < 35 then (if i.val < 32 then (if i.val < 31 then some 76 else some 118) else (if i.val < 33 then some 140 else (if i.val < 34 then some 152 else some 159))) else none))) else none) else none)⟩
def fullMates8985 : MateCertificate 160 := ⟨30, 76, fun i => (if i.val < 80 then (if i.val < 40 then (if i.val < 20 then none else (if i.val < 30 then none else (if i.val < 35 then (if i.val < 32 then (if i.val < 31 then some 76 else some 159) else (if i.val < 33 then some 152 else (if i.val < 34 then some 140 else some 118))) else none))) else none) else none)⟩
def fullMates10108 : MateCertificate 160 := ⟨35, 118, fun i => (if i.val < 80 then (if i.val < 40 then (if i.val < 20 then none else (if i.val < 30 then none else (if i.val < 35 then none else (if i.val < 37 then (if i.val < 36 then some 118 else some 159) else (if i.val < 38 then some 140 else (if i.val < 39 then some 76 else some 152)))))) else none) else none)⟩
def fullMates10131 : MateCertificate 160 := ⟨35, 159, fun i => (if i.val < 80 then (if i.val < 40 then (if i.val < 20 then none else (if i.val < 30 then none else (if i.val < 35 then none else (if i.val < 37 then (if i.val < 36 then some 159 else some 118) else (if i.val < 38 then some 152 else (if i.val < 39 then some 76 else some 140)))))) else none) else none)⟩
def fullAccept033 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm0 12 4369, .accepted fullMates8984⟩,
  ⟨Pose.ofCodes perm3 12 4369, .accepted fullMates8985⟩,
  ⟨Pose.ofCodes perm7 28 13973, .accepted fullMates10108⟩,
  ⟨Pose.ofCodes perm17 28 13973, .accepted fullMates10131⟩
]
theorem fullAccept033_checked : indexedValidate geometry fullAccept033 = true := by decide
theorem fullAccept033_length : fullAccept033.length = 4 := by rfl
def fullAccept033Output : List (Pose 5) := [Pose.ofCodes perm0 12 4369, Pose.ofCodes perm3 12 4369, Pose.ofCodes perm7 28 13973, Pose.ofCodes perm17 28 13973]
theorem fullAccept033_output : indexedAcceptedPoses fullAccept033 = fullAccept033Output := by rfl
#print axioms fullAccept033_checked
end SparseMonotiles.Contact.IndexedData5
