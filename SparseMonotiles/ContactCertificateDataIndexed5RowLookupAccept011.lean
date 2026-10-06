module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept011

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept011PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm19 23 9832 else Pose.ofCodes perm5 23 9832) else (if i.val < 3 then Pose.ofCodes perm10 23 9832 else Pose.ofCodes perm3 23 9832))
theorem fullAccept011PoseLookup_binding : List.ofFn fullAccept011PoseLookup = fullAccept011.map IndexedRow.pose := by rfl
theorem fullAccept011PoseLookup_mem (i : Fin 4) : fullAccept011PoseLookup i ∈ fullAccept011.map IndexedRow.pose := by
  rw [← fullAccept011PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept011PoseLookup_binding
#print axioms fullAccept011PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
