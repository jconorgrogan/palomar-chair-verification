module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates11433 : MateCertificate 160 := ⟨41, 158, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then (if i.val < 50 then (if i.val < 45 then (if i.val < 42 then (if i.val < 41 then none else some 158) else none) else (if i.val < 47 then (if i.val < 46 then none else some 136) else none)) else (if i.val < 55 then (if i.val < 52 then (if i.val < 51 then none else some 115) else none) else (if i.val < 57 then (if i.val < 56 then none else some 95) else none))) else (if i.val < 70 then (if i.val < 65 then (if i.val < 62 then (if i.val < 61 then none else some 74) else none) else (if i.val < 67 then (if i.val < 66 then none else some 54) else none)) else (if i.val < 75 then (if i.val < 72 then (if i.val < 71 then none else some 34) else none) else (if i.val < 77 then none else (if i.val < 78 then some 14 else none)))))) else (if i.val < 120 then none else (if i.val < 140 then (if i.val < 130 then (if i.val < 125 then (if i.val < 122 then none else (if i.val < 123 then none else (if i.val < 124 then some 147 else none))) else (if i.val < 127 then none else (if i.val < 128 then none else (if i.val < 129 then some 126 else none)))) else (if i.val < 135 then (if i.val < 132 then none else (if i.val < 133 then none else (if i.val < 134 then some 105 else none))) else (if i.val < 137 then none else (if i.val < 138 then none else (if i.val < 139 then some 85 else none))))) else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then none else (if i.val < 143 then none else (if i.val < 144 then none else some 64))) else (if i.val < 147 then none else (if i.val < 148 then none else (if i.val < 149 then none else some 44)))) else (if i.val < 155 then none else (if i.val < 157 then (if i.val < 156 then some 24 else none) else none))))))⟩
def fullMates11434 : MateCertificate 160 := ⟨41, 158, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then (if i.val < 50 then (if i.val < 45 then (if i.val < 42 then (if i.val < 41 then none else some 158) else none) else (if i.val < 47 then (if i.val < 46 then none else some 115) else none)) else (if i.val < 55 then (if i.val < 52 then (if i.val < 51 then none else some 136) else none) else (if i.val < 57 then (if i.val < 56 then none else some 95) else none))) else (if i.val < 70 then (if i.val < 65 then (if i.val < 62 then (if i.val < 61 then none else some 147) else none) else (if i.val < 67 then (if i.val < 66 then none else some 105) else none)) else (if i.val < 75 then (if i.val < 72 then (if i.val < 71 then none else some 126) else none) else (if i.val < 77 then none else (if i.val < 78 then some 85 else none)))))) else (if i.val < 120 then none else (if i.val < 140 then (if i.val < 130 then (if i.val < 125 then (if i.val < 122 then none else (if i.val < 123 then none else (if i.val < 124 then some 74 else none))) else (if i.val < 127 then none else (if i.val < 128 then none else (if i.val < 129 then some 34 else none)))) else (if i.val < 135 then (if i.val < 132 then none else (if i.val < 133 then none else (if i.val < 134 then some 54 else none))) else (if i.val < 137 then none else (if i.val < 138 then none else (if i.val < 139 then some 14 else none))))) else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then none else (if i.val < 143 then none else (if i.val < 144 then none else some 64))) else (if i.val < 147 then none else (if i.val < 148 then none else (if i.val < 149 then none else some 24)))) else (if i.val < 155 then none else (if i.val < 157 then (if i.val < 156 then some 44 else none) else none))))))⟩
def fullMates12470 : MateCertificate 160 := ⟨45, 76, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then (if i.val < 50 then (if i.val < 45 then none else (if i.val < 47 then (if i.val < 46 then some 76 else some 159) else (if i.val < 48 then some 152 else (if i.val < 49 then some 140 else some 118)))) else none) else none)) else none)⟩
def fullMates12471 : MateCertificate 160 := ⟨45, 76, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then (if i.val < 50 then (if i.val < 45 then none else (if i.val < 47 then (if i.val < 46 then some 76 else some 118) else (if i.val < 48 then some 140 else (if i.val < 49 then some 152 else some 159)))) else none) else none)) else none)⟩
def fullAccept039 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm15 29 11204, .accepted fullMates11433⟩,
  ⟨Pose.ofCodes perm3 29 11204, .accepted fullMates11434⟩,
  ⟨Pose.ofCodes perm3 18 12433, .accepted fullMates12470⟩,
  ⟨Pose.ofCodes perm0 18 12433, .accepted fullMates12471⟩
]
theorem fullAccept039_checked : indexedValidate geometry fullAccept039 = true := by decide
theorem fullAccept039_length : fullAccept039.length = 4 := by rfl
def fullAccept039Output : List (Pose 5) := [Pose.ofCodes perm15 29 11204, Pose.ofCodes perm3 29 11204, Pose.ofCodes perm3 18 12433, Pose.ofCodes perm0 18 12433]
theorem fullAccept039_output : indexedAcceptedPoses fullAccept039 = fullAccept039Output := by rfl
#print axioms fullAccept039_checked
end SparseMonotiles.Contact.IndexedData5
