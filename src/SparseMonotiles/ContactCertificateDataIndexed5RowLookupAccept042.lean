module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept042

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept042PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm6 14 4397 else Pose.ofCodes perm18 14 4397) else (if i.val < 3 then Pose.ofCodes perm3 30 14001 else Pose.ofCodes perm0 30 14001))
theorem fullAccept042PoseLookup_binding : List.ofFn fullAccept042PoseLookup = fullAccept042.map IndexedRow.pose := by rfl
theorem fullAccept042PoseLookup_mem (i : Fin 4) : fullAccept042PoseLookup i ∈ fullAccept042.map IndexedRow.pose := by
  rw [← fullAccept042PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept042PoseLookup_binding
#print axioms fullAccept042PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
