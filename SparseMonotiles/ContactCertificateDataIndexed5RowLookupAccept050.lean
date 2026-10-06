module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept050

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept050PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm8 13 9189 else Pose.ofCodes perm11 13 9189) else (if i.val < 3 then Pose.ofCodes perm3 30 14003 else Pose.ofCodes perm0 30 14003))
theorem fullAccept050PoseLookup_binding : List.ofFn fullAccept050PoseLookup = fullAccept050.map IndexedRow.pose := by rfl
theorem fullAccept050PoseLookup_mem (i : Fin 4) : fullAccept050PoseLookup i ∈ fullAccept050.map IndexedRow.pose := by
  rw [← fullAccept050PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept050PoseLookup_binding
#print axioms fullAccept050PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
