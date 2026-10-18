module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept028

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept028PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm8 4 5798 else Pose.ofCodes perm17 4 5798) else (if i.val < 3 then Pose.ofCodes perm12 4 5798 else Pose.ofCodes perm7 4 5798))
theorem fullAccept028PoseLookup_binding : List.ofFn fullAccept028PoseLookup = fullAccept028.map IndexedRow.pose := by rfl
theorem fullAccept028PoseLookup_mem (i : Fin 4) : fullAccept028PoseLookup i ∈ fullAccept028.map IndexedRow.pose := by
  rw [← fullAccept028PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept028PoseLookup_binding
#print axioms fullAccept028PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
