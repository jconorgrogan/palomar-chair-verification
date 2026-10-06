module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates6336 : MateCertificate 160 := ⟨20, 118, fun i => (if i.val < 80 then (if i.val < 40 then (if i.val < 20 then none else (if i.val < 30 then (if i.val < 25 then (if i.val < 22 then (if i.val < 21 then some 118 else some 152) else (if i.val < 23 then some 76 else (if i.val < 24 then some 140 else some 159))) else none) else none)) else none) else none)⟩
def fullMates6383 : MateCertificate 160 := ⟨20, 159, fun i => (if i.val < 80 then (if i.val < 40 then (if i.val < 20 then none else (if i.val < 30 then (if i.val < 25 then (if i.val < 22 then (if i.val < 21 then some 159 else some 140) else (if i.val < 23 then some 76 else (if i.val < 24 then some 152 else some 118))) else none) else none)) else none) else none)⟩
def fullMates6608 : MateCertificate 160 := ⟨22, 9, fun i => (if i.val < 80 then (if i.val < 40 then (if i.val < 20 then none else (if i.val < 30 then (if i.val < 25 then (if i.val < 22 then none else (if i.val < 23 then some 9 else none)) else (if i.val < 27 then none else (if i.val < 28 then some 19 else none))) else (if i.val < 35 then (if i.val < 32 then none else (if i.val < 33 then some 49 else none)) else (if i.val < 37 then none else (if i.val < 38 then some 59 else none))))) else (if i.val < 60 then none else (if i.val < 70 then (if i.val < 65 then (if i.val < 62 then none else (if i.val < 63 then some 29 else none)) else (if i.val < 67 then none else (if i.val < 68 then some 39 else none))) else (if i.val < 75 then (if i.val < 72 then none else (if i.val < 73 then some 69 else none)) else (if i.val < 77 then none else (if i.val < 78 then none else (if i.val < 79 then some 80 else none))))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then (if i.val < 105 then (if i.val < 102 then none else (if i.val < 103 then none else (if i.val < 104 then some 90 else none))) else (if i.val < 107 then none else (if i.val < 108 then none else (if i.val < 109 then some 100 else none)))) else (if i.val < 115 then (if i.val < 112 then none else (if i.val < 113 then none else (if i.val < 114 then some 131 else none))) else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then none else some 142)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then none else (if i.val < 147 then (if i.val < 146 then some 110 else none) else none)) else (if i.val < 155 then (if i.val < 152 then (if i.val < 151 then some 121 else none) else none) else (if i.val < 157 then (if i.val < 156 then none else some 153) else none))))))⟩
def fullMates6609 : MateCertificate 160 := ⟨22, 9, fun i => (if i.val < 80 then (if i.val < 40 then (if i.val < 20 then none else (if i.val < 30 then (if i.val < 25 then (if i.val < 22 then none else (if i.val < 23 then some 9 else none)) else (if i.val < 27 then none else (if i.val < 28 then some 90 else none))) else (if i.val < 35 then (if i.val < 32 then none else (if i.val < 33 then some 29 else none)) else (if i.val < 37 then none else (if i.val < 38 then some 110 else none))))) else (if i.val < 60 then none else (if i.val < 70 then (if i.val < 65 then (if i.val < 62 then none else (if i.val < 63 then some 49 else none)) else (if i.val < 67 then none else (if i.val < 68 then some 131 else none))) else (if i.val < 75 then (if i.val < 72 then none else (if i.val < 73 then some 69 else none)) else (if i.val < 77 then none else (if i.val < 78 then none else (if i.val < 79 then some 153 else none))))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then (if i.val < 105 then (if i.val < 102 then none else (if i.val < 103 then none else (if i.val < 104 then some 19 else none))) else (if i.val < 107 then none else (if i.val < 108 then none else (if i.val < 109 then some 100 else none)))) else (if i.val < 115 then (if i.val < 112 then none else (if i.val < 113 then none else (if i.val < 114 then some 39 else none))) else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then none else some 121)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then none else (if i.val < 147 then (if i.val < 146 then some 59 else none) else none)) else (if i.val < 155 then (if i.val < 152 then (if i.val < 151 then some 142 else none) else none) else (if i.val < 157 then (if i.val < 156 then none else some 80) else none))))))⟩
def fullAccept027 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm6 4 2997, .accepted fullMates6336⟩,
  ⟨Pose.ofCodes perm18 4 2997, .accepted fullMates6383⟩,
  ⟨Pose.ofCodes perm1 4 5798, .accepted fullMates6608⟩,
  ⟨Pose.ofCodes perm13 4 5798, .accepted fullMates6609⟩
]
theorem fullAccept027_checked : indexedValidate geometry fullAccept027 = true := by decide
theorem fullAccept027_length : fullAccept027.length = 4 := by rfl
def fullAccept027Output : List (Pose 5) := [Pose.ofCodes perm6 4 2997, Pose.ofCodes perm18 4 2997, Pose.ofCodes perm1 4 5798, Pose.ofCodes perm13 4 5798]
theorem fullAccept027_output : indexedAcceptedPoses fullAccept027 = fullAccept027Output := by rfl
#print axioms fullAccept027_checked
end SparseMonotiles.Contact.IndexedData5
