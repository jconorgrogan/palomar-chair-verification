module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept040

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept040PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm9 10 4201 else Pose.ofCodes perm15 10 4201) else (if i.val < 3 then Pose.ofCodes perm8 26 13805 else Pose.ofCodes perm12 26 13805))
theorem fullAccept040PoseLookup_binding : List.ofFn fullAccept040PoseLookup = fullAccept040.map IndexedRow.pose := by rfl
theorem fullAccept040PoseLookup_mem (i : Fin 4) : fullAccept040PoseLookup i ∈ fullAccept040.map IndexedRow.pose := by
  rw [← fullAccept040PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept040PoseLookup_binding
#print axioms fullAccept040PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
