module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept060

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept060PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm7 1 5606 else Pose.ofCodes perm6 1 5606) else (if i.val < 3 then Pose.ofCodes perm3 30 11204 else Pose.ofCodes perm0 30 11204))
theorem fullAccept060PoseLookup_binding : List.ofFn fullAccept060PoseLookup = fullAccept060.map IndexedRow.pose := by rfl
theorem fullAccept060PoseLookup_mem (i : Fin 4) : fullAccept060PoseLookup i ∈ fullAccept060.map IndexedRow.pose := by
  rw [← fullAccept060PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept060PoseLookup_binding
#print axioms fullAccept060PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
