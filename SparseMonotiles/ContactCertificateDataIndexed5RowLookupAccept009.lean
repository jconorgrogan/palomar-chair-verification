module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept009

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept009PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm3 27 11008 else Pose.ofCodes perm10 27 11008) else (if i.val < 3 then Pose.ofCodes perm15 27 11008 else Pose.ofCodes perm4 27 11008))
theorem fullAccept009PoseLookup_binding : List.ofFn fullAccept009PoseLookup = fullAccept009.map IndexedRow.pose := by rfl
theorem fullAccept009PoseLookup_mem (i : Fin 4) : fullAccept009PoseLookup i ∈ fullAccept009.map IndexedRow.pose := by
  rw [← fullAccept009PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept009PoseLookup_binding
#print axioms fullAccept009PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
