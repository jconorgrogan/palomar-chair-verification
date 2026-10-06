module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept062

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept062PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm5 30 11204 else Pose.ofCodes perm4 30 11204) else (if i.val < 3 then Pose.ofCodes perm9 30 11204 else Pose.ofCodes perm10 30 11204))
theorem fullAccept062PoseLookup_binding : List.ofFn fullAccept062PoseLookup = fullAccept062.map IndexedRow.pose := by rfl
theorem fullAccept062PoseLookup_mem (i : Fin 4) : fullAccept062PoseLookup i ∈ fullAccept062.map IndexedRow.pose := by
  rw [← fullAccept062PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept062PoseLookup_binding
#print axioms fullAccept062PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
