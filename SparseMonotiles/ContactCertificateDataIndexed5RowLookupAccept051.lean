module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept051

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept051PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm1 1 8405 else Pose.ofCodes perm2 1 8405) else (if i.val < 3 then Pose.ofCodes perm9 12 9187 else Pose.ofCodes perm10 12 9187))
theorem fullAccept051PoseLookup_binding : List.ofFn fullAccept051PoseLookup = fullAccept051.map IndexedRow.pose := by rfl
theorem fullAccept051PoseLookup_mem (i : Fin 4) : fullAccept051PoseLookup i ∈ fullAccept051.map IndexedRow.pose := by
  rw [← fullAccept051PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept051PoseLookup_binding
#print axioms fullAccept051PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
