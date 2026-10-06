module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept016

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept016PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm11 16 15206 else Pose.ofCodes perm13 16 15206) else (if i.val < 3 then Pose.ofCodes perm10 15 11204 else Pose.ofCodes perm3 15 11204))
theorem fullAccept016PoseLookup_binding : List.ofFn fullAccept016PoseLookup = fullAccept016.map IndexedRow.pose := by rfl
theorem fullAccept016PoseLookup_mem (i : Fin 4) : fullAccept016PoseLookup i ∈ fullAccept016.map IndexedRow.pose := by
  rw [← fullAccept016PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept016PoseLookup_binding
#print axioms fullAccept016PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
