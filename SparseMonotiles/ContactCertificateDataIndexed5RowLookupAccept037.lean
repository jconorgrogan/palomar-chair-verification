module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept037

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept037PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm8 2 5630 else Pose.ofCodes perm12 2 5630) else (if i.val < 3 then Pose.ofCodes perm9 29 11204 else Pose.ofCodes perm0 29 11204))
theorem fullAccept037PoseLookup_binding : List.ofFn fullAccept037PoseLookup = fullAccept037.map IndexedRow.pose := by rfl
theorem fullAccept037PoseLookup_mem (i : Fin 4) : fullAccept037PoseLookup i ∈ fullAccept037.map IndexedRow.pose := by
  rw [← fullAccept037PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept037PoseLookup_binding
#print axioms fullAccept037PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
