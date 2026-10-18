module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept061

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept061PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm1 1 2805 else Pose.ofCodes perm2 1 2805) else (if i.val < 3 then Pose.ofCodes perm1 1 5606 else Pose.ofCodes perm2 1 5606))
theorem fullAccept061PoseLookup_binding : List.ofFn fullAccept061PoseLookup = fullAccept061.map IndexedRow.pose := by rfl
theorem fullAccept061PoseLookup_mem (i : Fin 4) : fullAccept061PoseLookup i ∈ fullAccept061.map IndexedRow.pose := by
  rw [← fullAccept061PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept061PoseLookup_binding
#print axioms fullAccept061PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
