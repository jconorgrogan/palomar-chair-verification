module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept054

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept054PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm1 19 13221 else Pose.ofCodes perm2 19 13221) else (if i.val < 3 then Pose.ofCodes perm5 30 14003 else Pose.ofCodes perm4 30 14003))
theorem fullAccept054PoseLookup_binding : List.ofFn fullAccept054PoseLookup = fullAccept054.map IndexedRow.pose := by rfl
theorem fullAccept054PoseLookup_mem (i : Fin 4) : fullAccept054PoseLookup i ∈ fullAccept054.map IndexedRow.pose := by
  rw [← fullAccept054PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept054PoseLookup_binding
#print axioms fullAccept054PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
