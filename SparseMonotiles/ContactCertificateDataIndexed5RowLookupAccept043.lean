module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept043

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept043PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm0 0 8403 else Pose.ofCodes perm3 0 8403) else (if i.val < 3 then Pose.ofCodes perm17 1 8405 else Pose.ofCodes perm18 1 8405))
theorem fullAccept043PoseLookup_binding : List.ofFn fullAccept043PoseLookup = fullAccept043.map IndexedRow.pose := by rfl
theorem fullAccept043PoseLookup_mem (i : Fin 4) : fullAccept043PoseLookup i ∈ fullAccept043.map IndexedRow.pose := by
  rw [← fullAccept043PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept043PoseLookup_binding
#print axioms fullAccept043PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
