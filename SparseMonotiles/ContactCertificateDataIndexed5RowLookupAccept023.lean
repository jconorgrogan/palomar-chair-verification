module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept023

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept023PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm4 23 11204 else Pose.ofCodes perm0 23 11204) else (if i.val < 3 then Pose.ofCodes perm9 23 11204 else Pose.ofCodes perm5 23 11204))
theorem fullAccept023PoseLookup_binding : List.ofFn fullAccept023PoseLookup = fullAccept023.map IndexedRow.pose := by rfl
theorem fullAccept023PoseLookup_mem (i : Fin 4) : fullAccept023PoseLookup i ∈ fullAccept023.map IndexedRow.pose := by
  rw [← fullAccept023PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept023PoseLookup_binding
#print axioms fullAccept023PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
