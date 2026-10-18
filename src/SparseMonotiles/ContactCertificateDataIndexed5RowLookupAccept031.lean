module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept031

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept031PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm19 27 11204 else Pose.ofCodes perm0 27 11204) else (if i.val < 3 then Pose.ofCodes perm5 27 11204 else Pose.ofCodes perm3 27 11204))
theorem fullAccept031PoseLookup_binding : List.ofFn fullAccept031PoseLookup = fullAccept031.map IndexedRow.pose := by rfl
theorem fullAccept031PoseLookup_mem (i : Fin 4) : fullAccept031PoseLookup i ∈ fullAccept031.map IndexedRow.pose := by
  rw [← fullAccept031PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept031PoseLookup_binding
#print axioms fullAccept031PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
