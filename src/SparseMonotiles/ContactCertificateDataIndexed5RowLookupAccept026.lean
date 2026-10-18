module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept026

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept026PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm5 15 1600 else Pose.ofCodes perm9 15 1600) else (if i.val < 3 then Pose.ofCodes perm4 24 13777 else Pose.ofCodes perm16 24 13777))
theorem fullAccept026PoseLookup_binding : List.ofFn fullAccept026PoseLookup = fullAccept026.map IndexedRow.pose := by rfl
theorem fullAccept026PoseLookup_mem (i : Fin 4) : fullAccept026PoseLookup i ∈ fullAccept026.map IndexedRow.pose := by
  rw [← fullAccept026PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept026PoseLookup_binding
#print axioms fullAccept026PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
