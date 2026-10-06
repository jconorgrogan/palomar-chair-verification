module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept064

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept064PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm9 17 12409 else Pose.ofCodes perm15 17 12409) else (if i.val < 3 then Pose.ofCodes perm5 9 4177 else Pose.ofCodes perm19 9 4177))
theorem fullAccept064PoseLookup_binding : List.ofFn fullAccept064PoseLookup = fullAccept064.map IndexedRow.pose := by rfl
theorem fullAccept064PoseLookup_mem (i : Fin 4) : fullAccept064PoseLookup i ∈ fullAccept064.map IndexedRow.pose := by
  rw [← fullAccept064PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept064PoseLookup_binding
#print axioms fullAccept064PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
