module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept068

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept068PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm1 19 12437 else Pose.ofCodes perm2 19 12437) else (if i.val < 3 then Pose.ofCodes perm7 11 4205 else Pose.ofCodes perm17 11 4205))
theorem fullAccept068PoseLookup_binding : List.ofFn fullAccept068PoseLookup = fullAccept068.map IndexedRow.pose := by rfl
theorem fullAccept068PoseLookup_mem (i : Fin 4) : fullAccept068PoseLookup i ∈ fullAccept068.map IndexedRow.pose := by
  rw [← fullAccept068PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept068PoseLookup_binding
#print axioms fullAccept068PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
