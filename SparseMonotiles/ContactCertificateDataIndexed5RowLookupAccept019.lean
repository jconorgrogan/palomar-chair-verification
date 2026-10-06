module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept019

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept019PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm2 8 6974 else Pose.ofCodes perm12 8 6974) else (if i.val < 3 then Pose.ofCodes perm11 8 6974 else Pose.ofCodes perm18 8 6974))
theorem fullAccept019PoseLookup_binding : List.ofFn fullAccept019PoseLookup = fullAccept019.map IndexedRow.pose := by rfl
theorem fullAccept019PoseLookup_mem (i : Fin 4) : fullAccept019PoseLookup i ∈ fullAccept019.map IndexedRow.pose := by
  rw [← fullAccept019PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept019PoseLookup_binding
#print axioms fullAccept019PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
