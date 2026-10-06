module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept006

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept006PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm5 29 11176 else Pose.ofCodes perm19 29 11176) else (if i.val < 3 then Pose.ofCodes perm10 29 11176 else Pose.ofCodes perm3 29 11176))
theorem fullAccept006PoseLookup_binding : List.ofFn fullAccept006PoseLookup = fullAccept006.map IndexedRow.pose := by rfl
theorem fullAccept006PoseLookup_mem (i : Fin 4) : fullAccept006PoseLookup i ∈ fullAccept006.map IndexedRow.pose := by
  rw [← fullAccept006PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept006PoseLookup_binding
#print axioms fullAccept006PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
