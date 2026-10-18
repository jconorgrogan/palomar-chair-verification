module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept003

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept003PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm5 30 11200 else Pose.ofCodes perm19 30 11200) else (if i.val < 3 then Pose.ofCodes perm3 30 11200 else Pose.ofCodes perm10 30 11200))
theorem fullAccept003PoseLookup_binding : List.ofFn fullAccept003PoseLookup = fullAccept003.map IndexedRow.pose := by rfl
theorem fullAccept003PoseLookup_mem (i : Fin 4) : fullAccept003PoseLookup i ∈ fullAccept003.map IndexedRow.pose := by
  rw [← fullAccept003PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept003PoseLookup_binding
#print axioms fullAccept003PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
