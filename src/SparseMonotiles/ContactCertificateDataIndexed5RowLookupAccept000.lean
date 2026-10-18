module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept000

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept000PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm1 1 5602 else Pose.ofCodes perm2 1 5602) else (if i.val < 3 then Pose.ofCodes perm0 0 2801 else Pose.ofCodes perm3 0 2801))
theorem fullAccept000PoseLookup_binding : List.ofFn fullAccept000PoseLookup = fullAccept000.map IndexedRow.pose := by rfl
theorem fullAccept000PoseLookup_mem (i : Fin 4) : fullAccept000PoseLookup i ∈ fullAccept000.map IndexedRow.pose := by
  rw [← fullAccept000PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept000PoseLookup_binding
#print axioms fullAccept000PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
