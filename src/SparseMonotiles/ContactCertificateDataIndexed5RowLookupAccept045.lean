module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept045

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept045PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm8 1 8405 else Pose.ofCodes perm11 1 8405) else (if i.val < 3 then Pose.ofCodes perm14 18 13219 else Pose.ofCodes perm15 18 13219))
theorem fullAccept045PoseLookup_binding : List.ofFn fullAccept045PoseLookup = fullAccept045.map IndexedRow.pose := by rfl
theorem fullAccept045PoseLookup_mem (i : Fin 4) : fullAccept045PoseLookup i ∈ fullAccept045.map IndexedRow.pose := by
  rw [← fullAccept045PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept045PoseLookup_binding
#print axioms fullAccept045PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
