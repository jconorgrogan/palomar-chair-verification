module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept005

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept005PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm13 16 12405 else Pose.ofCodes perm16 30 11200) else (if i.val < 3 then Pose.ofCodes perm0 30 11200 else Pose.ofCodes perm14 30 11200))
theorem fullAccept005PoseLookup_binding : List.ofFn fullAccept005PoseLookup = fullAccept005.map IndexedRow.pose := by rfl
theorem fullAccept005PoseLookup_mem (i : Fin 4) : fullAccept005PoseLookup i ∈ fullAccept005.map IndexedRow.pose := by
  rw [← fullAccept005PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept005PoseLookup_binding
#print axioms fullAccept005PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
