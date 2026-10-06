module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept047

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept047PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm7 1 8405 else Pose.ofCodes perm6 1 8405) else (if i.val < 3 then Pose.ofCodes perm3 18 13219 else Pose.ofCodes perm0 18 13219))
theorem fullAccept047PoseLookup_binding : List.ofFn fullAccept047PoseLookup = fullAccept047.map IndexedRow.pose := by rfl
theorem fullAccept047PoseLookup_mem (i : Fin 4) : fullAccept047PoseLookup i ∈ fullAccept047.map IndexedRow.pose := by
  rw [← fullAccept047PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept047PoseLookup_binding
#print axioms fullAccept047PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
