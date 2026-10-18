module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept004

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept004PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm4 30 11200 else Pose.ofCodes perm11 16 12405) else (if i.val < 3 then Pose.ofCodes perm15 30 11200 else Pose.ofCodes perm9 30 11200))
theorem fullAccept004PoseLookup_binding : List.ofFn fullAccept004PoseLookup = fullAccept004.map IndexedRow.pose := by rfl
theorem fullAccept004PoseLookup_mem (i : Fin 4) : fullAccept004PoseLookup i ∈ fullAccept004.map IndexedRow.pose := by
  rw [← fullAccept004PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept004PoseLookup_binding
#print axioms fullAccept004PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
