module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept007

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept007PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm4 29 11176 else Pose.ofCodes perm15 29 11176) else (if i.val < 3 then Pose.ofCodes perm16 29 11176 else Pose.ofCodes perm9 29 11176))
theorem fullAccept007PoseLookup_binding : List.ofFn fullAccept007PoseLookup = fullAccept007.map IndexedRow.pose := by rfl
theorem fullAccept007PoseLookup_mem (i : Fin 4) : fullAccept007PoseLookup i ∈ fullAccept007.map IndexedRow.pose := by
  rw [← fullAccept007PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept007PoseLookup_binding
#print axioms fullAccept007PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
