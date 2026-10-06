module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept012

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept012PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm15 23 9832 else Pose.ofCodes perm4 23 9832) else (if i.val < 3 then Pose.ofCodes perm16 23 9832 else Pose.ofCodes perm9 23 9832))
theorem fullAccept012PoseLookup_binding : List.ofFn fullAccept012PoseLookup = fullAccept012.map IndexedRow.pose := by rfl
theorem fullAccept012PoseLookup_mem (i : Fin 4) : fullAccept012PoseLookup i ∈ fullAccept012.map IndexedRow.pose := by
  rw [← fullAccept012PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept012PoseLookup_binding
#print axioms fullAccept012PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
