module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept035

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept035PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm2 2 5630 else Pose.ofCodes perm6 2 5630) else (if i.val < 3 then Pose.ofCodes perm1 2 5630 else Pose.ofCodes perm18 2 5630))
theorem fullAccept035PoseLookup_binding : List.ofFn fullAccept035PoseLookup = fullAccept035.map IndexedRow.pose := by rfl
theorem fullAccept035PoseLookup_mem (i : Fin 4) : fullAccept035PoseLookup i ∈ fullAccept035.map IndexedRow.pose := by
  rw [← fullAccept035PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept035PoseLookup_binding
#print axioms fullAccept035PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
