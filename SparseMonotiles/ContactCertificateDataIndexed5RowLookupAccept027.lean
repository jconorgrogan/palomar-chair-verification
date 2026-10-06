module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept027

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept027PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm6 4 2997 else Pose.ofCodes perm18 4 2997) else (if i.val < 3 then Pose.ofCodes perm1 4 5798 else Pose.ofCodes perm13 4 5798))
theorem fullAccept027PoseLookup_binding : List.ofFn fullAccept027PoseLookup = fullAccept027.map IndexedRow.pose := by rfl
theorem fullAccept027PoseLookup_mem (i : Fin 4) : fullAccept027PoseLookup i ∈ fullAccept027.map IndexedRow.pose := by
  rw [← fullAccept027PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept027PoseLookup_binding
#print axioms fullAccept027PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
