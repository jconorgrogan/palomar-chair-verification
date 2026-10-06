module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept024

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept024PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm10 15 1600 else Pose.ofCodes perm14 15 1600) else (if i.val < 3 then Pose.ofCodes perm19 15 1600 else Pose.ofCodes perm15 15 1600))
theorem fullAccept024PoseLookup_binding : List.ofFn fullAccept024PoseLookup = fullAccept024.map IndexedRow.pose := by rfl
theorem fullAccept024PoseLookup_mem (i : Fin 4) : fullAccept024PoseLookup i ∈ fullAccept024.map IndexedRow.pose := by
  rw [← fullAccept024PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept024PoseLookup_binding
#print axioms fullAccept024PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
