module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept065

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept065PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm11 25 13781 else Pose.ofCodes perm13 25 13781) else (if i.val < 3 then Pose.ofCodes perm4 5 3001 else Pose.ofCodes perm16 5 3001))
theorem fullAccept065PoseLookup_binding : List.ofFn fullAccept065PoseLookup = fullAccept065.map IndexedRow.pose := by rfl
theorem fullAccept065PoseLookup_mem (i : Fin 4) : fullAccept065PoseLookup i ∈ fullAccept065.map IndexedRow.pose := by
  rw [← fullAccept065PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept065PoseLookup_binding
#print axioms fullAccept065PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
