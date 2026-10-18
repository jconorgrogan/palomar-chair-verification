module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept001

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept001PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm1 2 5602 else Pose.ofCodes perm2 2 5602) else (if i.val < 3 then Pose.ofCodes perm2 4 5602 else Pose.ofCodes perm1 4 5602))
theorem fullAccept001PoseLookup_binding : List.ofFn fullAccept001PoseLookup = fullAccept001.map IndexedRow.pose := by rfl
theorem fullAccept001PoseLookup_mem (i : Fin 4) : fullAccept001PoseLookup i ∈ fullAccept001.map IndexedRow.pose := by
  rw [← fullAccept001PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept001PoseLookup_binding
#print axioms fullAccept001PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
