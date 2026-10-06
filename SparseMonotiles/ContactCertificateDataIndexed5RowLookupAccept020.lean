module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept020

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept020PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm13 8 6974 else Pose.ofCodes perm6 8 6974) else (if i.val < 3 then Pose.ofCodes perm1 8 6974 else Pose.ofCodes perm8 8 6974))
theorem fullAccept020PoseLookup_binding : List.ofFn fullAccept020PoseLookup = fullAccept020.map IndexedRow.pose := by rfl
theorem fullAccept020PoseLookup_mem (i : Fin 4) : fullAccept020PoseLookup i ∈ fullAccept020.map IndexedRow.pose := by
  rw [← fullAccept020PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept020PoseLookup_binding
#print axioms fullAccept020PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
