module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept032

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept032PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm10 27 11204 else Pose.ofCodes perm4 27 11204) else (if i.val < 3 then Pose.ofCodes perm10 20 12601 else Pose.ofCodes perm14 20 12601))
theorem fullAccept032PoseLookup_binding : List.ofFn fullAccept032PoseLookup = fullAccept032.map IndexedRow.pose := by rfl
theorem fullAccept032PoseLookup_mem (i : Fin 4) : fullAccept032PoseLookup i ∈ fullAccept032.map IndexedRow.pose := by
  rw [← fullAccept032PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept032PoseLookup_binding
#print axioms fullAccept032PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
