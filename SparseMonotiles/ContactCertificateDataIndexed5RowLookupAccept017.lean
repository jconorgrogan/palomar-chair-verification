module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept017

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept017PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm4 15 11204 else Pose.ofCodes perm15 15 11204) else (if i.val < 3 then Pose.ofCodes perm16 15 11204 else Pose.ofCodes perm9 15 11204))
theorem fullAccept017PoseLookup_binding : List.ofFn fullAccept017PoseLookup = fullAccept017.map IndexedRow.pose := by rfl
theorem fullAccept017PoseLookup_mem (i : Fin 4) : fullAccept017PoseLookup i ∈ fullAccept017.map IndexedRow.pose := by
  rw [← fullAccept017PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept017PoseLookup_binding
#print axioms fullAccept017PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
