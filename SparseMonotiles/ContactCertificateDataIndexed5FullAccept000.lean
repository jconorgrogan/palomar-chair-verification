module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates2 : MateCertificate 160 := ⟨0, 0, fun i => (if i.val < 80 then (if i.val < 40 then (if i.val < 20 then (if i.val < 10 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then some 0 else none) else none) else (if i.val < 7 then (if i.val < 6 then some 10 else none) else none)) else (if i.val < 15 then (if i.val < 12 then (if i.val < 11 then some 40 else none) else none) else (if i.val < 17 then (if i.val < 16 then some 50 else none) else none))) else (if i.val < 30 then (if i.val < 25 then (if i.val < 22 then (if i.val < 21 then some 5 else none) else none) else (if i.val < 27 then (if i.val < 26 then some 15 else none) else none)) else (if i.val < 35 then (if i.val < 32 then (if i.val < 31 then some 45 else none) else none) else (if i.val < 37 then (if i.val < 36 then some 55 else none) else none)))) else (if i.val < 60 then (if i.val < 50 then (if i.val < 45 then (if i.val < 42 then (if i.val < 41 then some 20 else none) else none) else (if i.val < 47 then (if i.val < 46 then some 30 else none) else none)) else (if i.val < 55 then (if i.val < 52 then (if i.val < 51 then some 60 else none) else none) else (if i.val < 57 then (if i.val < 56 then some 70 else none) else none))) else (if i.val < 70 then (if i.val < 65 then (if i.val < 62 then (if i.val < 61 then some 25 else none) else none) else (if i.val < 67 then (if i.val < 66 then some 35 else none) else none)) else (if i.val < 75 then (if i.val < 72 then (if i.val < 71 then some 65 else none) else none) else (if i.val < 77 then (if i.val < 76 then some 75 else none) else none))))) else none)⟩
def fullMates3 : MateCertificate 160 := ⟨0, 0, fun i => (if i.val < 80 then (if i.val < 40 then (if i.val < 20 then (if i.val < 10 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then some 0 else none) else none) else (if i.val < 7 then (if i.val < 6 then some 20 else none) else none)) else (if i.val < 15 then (if i.val < 12 then (if i.val < 11 then some 5 else none) else none) else (if i.val < 17 then (if i.val < 16 then some 25 else none) else none))) else (if i.val < 30 then (if i.val < 25 then (if i.val < 22 then (if i.val < 21 then some 40 else none) else none) else (if i.val < 27 then (if i.val < 26 then some 60 else none) else none)) else (if i.val < 35 then (if i.val < 32 then (if i.val < 31 then some 45 else none) else none) else (if i.val < 37 then (if i.val < 36 then some 65 else none) else none)))) else (if i.val < 60 then (if i.val < 50 then (if i.val < 45 then (if i.val < 42 then (if i.val < 41 then some 10 else none) else none) else (if i.val < 47 then (if i.val < 46 then some 30 else none) else none)) else (if i.val < 55 then (if i.val < 52 then (if i.val < 51 then some 15 else none) else none) else (if i.val < 57 then (if i.val < 56 then some 35 else none) else none))) else (if i.val < 70 then (if i.val < 65 then (if i.val < 62 then (if i.val < 61 then some 50 else none) else none) else (if i.val < 67 then (if i.val < 66 then some 70 else none) else none)) else (if i.val < 75 then (if i.val < 72 then (if i.val < 71 then some 55 else none) else none) else (if i.val < 77 then (if i.val < 76 then some 75 else none) else none))))) else none)⟩
def fullMates124 : MateCertificate 160 := ⟨0, 76, fun i => (if i.val < 80 then (if i.val < 40 then (if i.val < 20 then (if i.val < 10 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then some 76 else some 118) else (if i.val < 3 then some 140 else (if i.val < 4 then some 152 else some 159))) else none) else none) else none) else none) else none)⟩
def fullMates125 : MateCertificate 160 := ⟨0, 76, fun i => (if i.val < 80 then (if i.val < 40 then (if i.val < 20 then (if i.val < 10 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then some 76 else some 159) else (if i.val < 3 then some 152 else (if i.val < 4 then some 140 else some 118))) else none) else none) else none) else none) else none)⟩
def fullAccept000 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm1 1 5602, .accepted fullMates2⟩,
  ⟨Pose.ofCodes perm2 1 5602, .accepted fullMates3⟩,
  ⟨Pose.ofCodes perm0 0 2801, .accepted fullMates124⟩,
  ⟨Pose.ofCodes perm3 0 2801, .accepted fullMates125⟩
]
theorem fullAccept000_checked : indexedValidate geometry fullAccept000 = true := by decide
theorem fullAccept000_length : fullAccept000.length = 4 := by rfl
def fullAccept000Output : List (Pose 5) := [Pose.ofCodes perm1 1 5602, Pose.ofCodes perm2 1 5602, Pose.ofCodes perm0 0 2801, Pose.ofCodes perm3 0 2801]
theorem fullAccept000_output : indexedAcceptedPoses fullAccept000 = fullAccept000Output := by rfl
#print axioms fullAccept000_checked
end SparseMonotiles.Contact.IndexedData5
