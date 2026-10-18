module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept048

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept048PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm10 18 13219 else Pose.ofCodes perm9 18 13219) else (if i.val < 3 then Pose.ofCodes perm7 19 13221 else Pose.ofCodes perm6 19 13221))
theorem fullAccept048PoseLookup_binding : List.ofFn fullAccept048PoseLookup = fullAccept048.map IndexedRow.pose := by rfl
theorem fullAccept048PoseLookup_mem (i : Fin 4) : fullAccept048PoseLookup i ∈ fullAccept048.map IndexedRow.pose := by
  rw [← fullAccept048PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept048PoseLookup_binding
#print axioms fullAccept048PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
