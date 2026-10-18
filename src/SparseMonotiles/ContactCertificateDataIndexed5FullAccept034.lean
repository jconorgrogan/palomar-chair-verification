module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates11167 : MateCertificate 160 := ⟨40, 140, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then (if i.val < 50 then (if i.val < 45 then (if i.val < 42 then (if i.val < 41 then some 140 else some 76) else (if i.val < 43 then some 152 else (if i.val < 44 then some 118 else some 159))) else none) else none) else none)) else none)⟩
def fullMates11178 : MateCertificate 160 := ⟨40, 152, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then (if i.val < 50 then (if i.val < 45 then (if i.val < 42 then (if i.val < 41 then some 152 else some 76) else (if i.val < 43 then some 140 else (if i.val < 44 then some 159 else some 118))) else none) else none) else none)) else none)⟩
def fullMates11198 : MateCertificate 160 := ⟨41, 9, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then (if i.val < 50 then (if i.val < 45 then (if i.val < 42 then (if i.val < 41 then none else some 9) else none) else (if i.val < 47 then (if i.val < 46 then none else some 19) else none)) else (if i.val < 55 then (if i.val < 52 then (if i.val < 51 then none else some 90) else none) else (if i.val < 57 then (if i.val < 56 then none else some 100) else none))) else (if i.val < 70 then (if i.val < 65 then (if i.val < 62 then (if i.val < 61 then none else some 29) else none) else (if i.val < 67 then (if i.val < 66 then none else some 39) else none)) else (if i.val < 75 then (if i.val < 72 then (if i.val < 71 then none else some 110) else none) else (if i.val < 77 then none else (if i.val < 78 then some 121 else none)))))) else (if i.val < 120 then none else (if i.val < 140 then (if i.val < 130 then (if i.val < 125 then (if i.val < 122 then none else (if i.val < 123 then none else (if i.val < 124 then some 49 else none))) else (if i.val < 127 then none else (if i.val < 128 then none else (if i.val < 129 then some 59 else none)))) else (if i.val < 135 then (if i.val < 132 then none else (if i.val < 133 then none else (if i.val < 134 then some 131 else none))) else (if i.val < 137 then none else (if i.val < 138 then none else (if i.val < 139 then some 142 else none))))) else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then none else (if i.val < 143 then none else (if i.val < 144 then none else some 69))) else (if i.val < 147 then none else (if i.val < 148 then none else (if i.val < 149 then none else some 80)))) else (if i.val < 155 then none else (if i.val < 157 then (if i.val < 156 then some 153 else none) else none))))))⟩
def fullMates11199 : MateCertificate 160 := ⟨41, 9, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then (if i.val < 50 then (if i.val < 45 then (if i.val < 42 then (if i.val < 41 then none else some 9) else none) else (if i.val < 47 then (if i.val < 46 then none else some 90) else none)) else (if i.val < 55 then (if i.val < 52 then (if i.val < 51 then none else some 19) else none) else (if i.val < 57 then (if i.val < 56 then none else some 100) else none))) else (if i.val < 70 then (if i.val < 65 then (if i.val < 62 then (if i.val < 61 then none else some 49) else none) else (if i.val < 67 then (if i.val < 66 then none else some 131) else none)) else (if i.val < 75 then (if i.val < 72 then (if i.val < 71 then none else some 59) else none) else (if i.val < 77 then none else (if i.val < 78 then some 142 else none)))))) else (if i.val < 120 then none else (if i.val < 140 then (if i.val < 130 then (if i.val < 125 then (if i.val < 122 then none else (if i.val < 123 then none else (if i.val < 124 then some 29 else none))) else (if i.val < 127 then none else (if i.val < 128 then none else (if i.val < 129 then some 110 else none)))) else (if i.val < 135 then (if i.val < 132 then none else (if i.val < 133 then none else (if i.val < 134 then some 39 else none))) else (if i.val < 137 then none else (if i.val < 138 then none else (if i.val < 139 then some 121 else none))))) else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then none else (if i.val < 143 then none else (if i.val < 144 then none else some 69))) else (if i.val < 147 then none else (if i.val < 148 then none else (if i.val < 149 then none else some 153)))) else (if i.val < 155 then none else (if i.val < 157 then (if i.val < 156 then some 80 else none) else none))))))⟩
def fullAccept034 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm8 2 2829, .accepted fullMates11167⟩,
  ⟨Pose.ofCodes perm12 2 2829, .accepted fullMates11178⟩,
  ⟨Pose.ofCodes perm7 2 5630, .accepted fullMates11198⟩,
  ⟨Pose.ofCodes perm11 2 5630, .accepted fullMates11199⟩
]
theorem fullAccept034_checked : indexedValidate geometry fullAccept034 = true := by decide
theorem fullAccept034_length : fullAccept034.length = 4 := by rfl
def fullAccept034Output : List (Pose 5) := [Pose.ofCodes perm8 2 2829, Pose.ofCodes perm12 2 2829, Pose.ofCodes perm7 2 5630, Pose.ofCodes perm11 2 5630]
theorem fullAccept034_output : indexedAcceptedPoses fullAccept034 = fullAccept034Output := by rfl
#print axioms fullAccept034_checked
end SparseMonotiles.Contact.IndexedData5
