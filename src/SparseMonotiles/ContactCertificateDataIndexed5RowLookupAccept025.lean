module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept025

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept025PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm3 15 1600 else Pose.ofCodes perm16 15 1600) else (if i.val < 3 then Pose.ofCodes perm4 15 1600 else Pose.ofCodes perm0 15 1600))
theorem fullAccept025PoseLookup_binding : List.ofFn fullAccept025PoseLookup = fullAccept025.map IndexedRow.pose := by rfl
theorem fullAccept025PoseLookup_mem (i : Fin 4) : fullAccept025PoseLookup i ∈ fullAccept025.map IndexedRow.pose := by
  rw [← fullAccept025PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept025PoseLookup_binding
#print axioms fullAccept025PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
