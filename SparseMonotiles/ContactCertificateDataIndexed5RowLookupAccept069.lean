module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept069

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept069PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm9 27 13809 else Pose.ofCodes perm15 27 13809) else (if i.val < 3 then Pose.ofCodes perm8 7 3029 else Pose.ofCodes perm12 7 3029))
theorem fullAccept069PoseLookup_binding : List.ofFn fullAccept069PoseLookup = fullAccept069.map IndexedRow.pose := by rfl
theorem fullAccept069PoseLookup_mem (i : Fin 4) : fullAccept069PoseLookup i ∈ fullAccept069.map IndexedRow.pose := by
  rw [← fullAccept069PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept069PoseLookup_binding
#print axioms fullAccept069PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
