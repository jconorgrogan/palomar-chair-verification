module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept056

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept056PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm13 19 13221 else Pose.ofCodes perm12 19 13221) else (if i.val < 3 then Pose.ofCodes perm9 30 14003 else Pose.ofCodes perm10 30 14003))
theorem fullAccept056PoseLookup_binding : List.ofFn fullAccept056PoseLookup = fullAccept056.map IndexedRow.pose := by rfl
theorem fullAccept056PoseLookup_mem (i : Fin 4) : fullAccept056PoseLookup i ∈ fullAccept056.map IndexedRow.pose := by
  rw [← fullAccept056PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept056PoseLookup_binding
#print axioms fullAccept056PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
