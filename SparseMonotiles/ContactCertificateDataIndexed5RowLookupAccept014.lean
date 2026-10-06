module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept014

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept014PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm1 16 15206 else Pose.ofCodes perm7 16 15206) else (if i.val < 3 then Pose.ofCodes perm2 16 15206 else Pose.ofCodes perm17 16 15206))
theorem fullAccept014PoseLookup_binding : List.ofFn fullAccept014PoseLookup = fullAccept014.map IndexedRow.pose := by rfl
theorem fullAccept014PoseLookup_mem (i : Fin 4) : fullAccept014PoseLookup i ∈ fullAccept014.map IndexedRow.pose := by
  rw [← fullAccept014PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept014PoseLookup_binding
#print axioms fullAccept014PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
