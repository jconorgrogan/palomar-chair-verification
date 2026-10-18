module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept033

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept033PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm0 12 4369 else Pose.ofCodes perm3 12 4369) else (if i.val < 3 then Pose.ofCodes perm7 28 13973 else Pose.ofCodes perm17 28 13973))
theorem fullAccept033PoseLookup_binding : List.ofFn fullAccept033PoseLookup = fullAccept033.map IndexedRow.pose := by rfl
theorem fullAccept033PoseLookup_mem (i : Fin 4) : fullAccept033PoseLookup i ∈ fullAccept033.map IndexedRow.pose := by
  rw [← fullAccept033PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept033PoseLookup_binding
#print axioms fullAccept033PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
