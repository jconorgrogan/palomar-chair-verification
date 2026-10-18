module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept010

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept010PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm9 27 11008 else Pose.ofCodes perm16 27 11008) else (if i.val < 3 then Pose.ofCodes perm14 27 11008 else Pose.ofCodes perm0 27 11008))
theorem fullAccept010PoseLookup_binding : List.ofFn fullAccept010PoseLookup = fullAccept010.map IndexedRow.pose := by rfl
theorem fullAccept010PoseLookup_mem (i : Fin 4) : fullAccept010PoseLookup i ∈ fullAccept010.map IndexedRow.pose := by
  rw [← fullAccept010PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept010PoseLookup_binding
#print axioms fullAccept010PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
