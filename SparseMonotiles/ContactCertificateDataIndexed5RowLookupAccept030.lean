module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept030

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept030PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm6 4 5798 else Pose.ofCodes perm18 4 5798) else (if i.val < 3 then Pose.ofCodes perm14 27 11204 else Pose.ofCodes perm16 27 11204))
theorem fullAccept030PoseLookup_binding : List.ofFn fullAccept030PoseLookup = fullAccept030.map IndexedRow.pose := by rfl
theorem fullAccept030PoseLookup_mem (i : Fin 4) : fullAccept030PoseLookup i ∈ fullAccept030.map IndexedRow.pose := by
  rw [← fullAccept030PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept030PoseLookup_binding
#print axioms fullAccept030PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
