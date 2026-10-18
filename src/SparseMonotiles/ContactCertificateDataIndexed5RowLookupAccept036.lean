module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept036

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept036PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm17 2 5630 else Pose.ofCodes perm13 2 5630) else (if i.val < 3 then Pose.ofCodes perm16 29 11204 else Pose.ofCodes perm4 29 11204))
theorem fullAccept036PoseLookup_binding : List.ofFn fullAccept036PoseLookup = fullAccept036.map IndexedRow.pose := by rfl
theorem fullAccept036PoseLookup_mem (i : Fin 4) : fullAccept036PoseLookup i ∈ fullAccept036.map IndexedRow.pose := by
  rw [← fullAccept036PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept036PoseLookup_binding
#print axioms fullAccept036PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
