module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept053

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept053PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm5 18 13219 else Pose.ofCodes perm4 18 13219) else (if i.val < 3 then Pose.ofCodes perm11 19 13221 else Pose.ofCodes perm8 19 13221))
theorem fullAccept053PoseLookup_binding : List.ofFn fullAccept053PoseLookup = fullAccept053.map IndexedRow.pose := by rfl
theorem fullAccept053PoseLookup_mem (i : Fin 4) : fullAccept053PoseLookup i ∈ fullAccept053.map IndexedRow.pose := by
  rw [← fullAccept053PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept053PoseLookup_binding
#print axioms fullAccept053PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
