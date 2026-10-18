module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept049

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept049PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm16 12 9187 else Pose.ofCodes perm19 12 9187) else (if i.val < 3 then Pose.ofCodes perm17 19 13221 else Pose.ofCodes perm18 19 13221))
theorem fullAccept049PoseLookup_binding : List.ofFn fullAccept049PoseLookup = fullAccept049.map IndexedRow.pose := by rfl
theorem fullAccept049PoseLookup_mem (i : Fin 4) : fullAccept049PoseLookup i ∈ fullAccept049.map IndexedRow.pose := by
  rw [← fullAccept049PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept049PoseLookup_binding
#print axioms fullAccept049PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
