module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept044

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept044PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm12 1 8405 else Pose.ofCodes perm13 1 8405) else (if i.val < 3 then Pose.ofCodes perm4 12 9187 else Pose.ofCodes perm5 12 9187))
theorem fullAccept044PoseLookup_binding : List.ofFn fullAccept044PoseLookup = fullAccept044.map IndexedRow.pose := by rfl
theorem fullAccept044PoseLookup_mem (i : Fin 4) : fullAccept044PoseLookup i ∈ fullAccept044.map IndexedRow.pose := by
  rw [← fullAccept044PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept044PoseLookup_binding
#print axioms fullAccept044PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
