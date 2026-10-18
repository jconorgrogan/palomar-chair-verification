module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept052

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept052PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm19 18 13219 else Pose.ofCodes perm16 18 13219) else (if i.val < 3 then Pose.ofCodes perm18 13 9189 else Pose.ofCodes perm17 13 9189))
theorem fullAccept052PoseLookup_binding : List.ofFn fullAccept052PoseLookup = fullAccept052.map IndexedRow.pose := by rfl
theorem fullAccept052PoseLookup_mem (i : Fin 4) : fullAccept052PoseLookup i ∈ fullAccept052.map IndexedRow.pose := by
  rw [← fullAccept052PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept052PoseLookup_binding
#print axioms fullAccept052PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
