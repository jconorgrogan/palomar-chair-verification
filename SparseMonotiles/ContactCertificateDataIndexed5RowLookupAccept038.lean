module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept038

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept038PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm5 29 11204 else Pose.ofCodes perm14 29 11204) else (if i.val < 3 then Pose.ofCodes perm19 29 11204 else Pose.ofCodes perm10 29 11204))
theorem fullAccept038PoseLookup_binding : List.ofFn fullAccept038PoseLookup = fullAccept038.map IndexedRow.pose := by rfl
theorem fullAccept038PoseLookup_mem (i : Fin 4) : fullAccept038PoseLookup i ∈ fullAccept038.map IndexedRow.pose := by
  rw [← fullAccept038PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept038PoseLookup_binding
#print axioms fullAccept038PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
