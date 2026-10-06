module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept058

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept058PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm19 30 14003 else Pose.ofCodes perm16 30 14003) else (if i.val < 3 then Pose.ofCodes perm17 1 5606 else Pose.ofCodes perm18 1 5606))
theorem fullAccept058PoseLookup_binding : List.ofFn fullAccept058PoseLookup = fullAccept058.map IndexedRow.pose := by rfl
theorem fullAccept058PoseLookup_mem (i : Fin 4) : fullAccept058PoseLookup i ∈ fullAccept058.map IndexedRow.pose := by
  rw [← fullAccept058PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept058PoseLookup_binding
#print axioms fullAccept058PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
