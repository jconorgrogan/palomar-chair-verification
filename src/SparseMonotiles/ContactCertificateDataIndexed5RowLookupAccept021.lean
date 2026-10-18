module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept021

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept021PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm14 23 11204 else Pose.ofCodes perm10 23 11204) else (if i.val < 3 then Pose.ofCodes perm7 8 6974 else Pose.ofCodes perm17 8 6974))
theorem fullAccept021PoseLookup_binding : List.ofFn fullAccept021PoseLookup = fullAccept021.map IndexedRow.pose := by rfl
theorem fullAccept021PoseLookup_mem (i : Fin 4) : fullAccept021PoseLookup i ∈ fullAccept021.map IndexedRow.pose := by
  rw [← fullAccept021PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept021PoseLookup_binding
#print axioms fullAccept021PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
