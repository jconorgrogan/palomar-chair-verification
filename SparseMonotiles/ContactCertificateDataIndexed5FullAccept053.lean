module

public import SparseMonotiles.ContactCertificateDataIndexed5Base
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMates19671 : MateCertificate 160 := ⟨76, 102, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 102) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 103 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 104 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 105 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 101))))))))⟩
def fullMates19672 : MateCertificate 160 := ⟨76, 102, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 102) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 101 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 105 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 104 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 103))))))))⟩
def fullMates19680 : MateCertificate 160 := ⟨76, 108, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 108) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 110 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 107 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 109 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 106))))))))⟩
def fullMates19681 : MateCertificate 160 := ⟨76, 108, fun i => (if i.val < 80 then (if i.val < 40 then none else (if i.val < 60 then none else (if i.val < 70 then none else (if i.val < 75 then none else (if i.val < 77 then (if i.val < 76 then none else some 108) else none))))) else (if i.val < 120 then (if i.val < 100 then none else (if i.val < 110 then none else (if i.val < 115 then none else (if i.val < 117 then none else (if i.val < 118 then none else (if i.val < 119 then some 106 else none)))))) else (if i.val < 140 then none else (if i.val < 150 then (if i.val < 145 then (if i.val < 142 then (if i.val < 141 then some 109 else none) else none) else none) else (if i.val < 155 then (if i.val < 152 then none else (if i.val < 153 then some 107 else none)) else (if i.val < 157 then none else (if i.val < 158 then none else (if i.val < 159 then none else some 110))))))))⟩
def fullAccept053 : List (IndexedRow 5 160) := [
  ⟨Pose.ofCodes perm5 18 13219, .accepted fullMates19671⟩,
  ⟨Pose.ofCodes perm4 18 13219, .accepted fullMates19672⟩,
  ⟨Pose.ofCodes perm11 19 13221, .accepted fullMates19680⟩,
  ⟨Pose.ofCodes perm8 19 13221, .accepted fullMates19681⟩
]
theorem fullAccept053_checked : indexedValidate geometry fullAccept053 = true := by decide +kernel
theorem fullAccept053_length : fullAccept053.length = 4 := by rfl
def fullAccept053Output : List (Pose 5) := [Pose.ofCodes perm5 18 13219, Pose.ofCodes perm4 18 13219, Pose.ofCodes perm11 19 13221, Pose.ofCodes perm8 19 13221]
theorem fullAccept053_output : indexedAcceptedPoses fullAccept053 = fullAccept053Output := by rfl
#print axioms fullAccept053_checked
end SparseMonotiles.Contact.IndexedData5
