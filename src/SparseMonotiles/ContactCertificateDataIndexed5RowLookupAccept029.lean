module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept029

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept029PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm2 4 5798 else Pose.ofCodes perm11 4 5798) else (if i.val < 3 then Pose.ofCodes perm15 27 11204 else Pose.ofCodes perm9 27 11204))
theorem fullAccept029PoseLookup_binding : List.ofFn fullAccept029PoseLookup = fullAccept029.map IndexedRow.pose := by rfl
theorem fullAccept029PoseLookup_mem (i : Fin 4) : fullAccept029PoseLookup i ∈ fullAccept029.map IndexedRow.pose := by
  rw [← fullAccept029PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept029PoseLookup_binding
#print axioms fullAccept029PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
