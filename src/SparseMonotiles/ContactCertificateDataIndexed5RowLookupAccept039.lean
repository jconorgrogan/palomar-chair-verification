module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept039

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept039PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm15 29 11204 else Pose.ofCodes perm3 29 11204) else (if i.val < 3 then Pose.ofCodes perm3 18 12433 else Pose.ofCodes perm0 18 12433))
theorem fullAccept039PoseLookup_binding : List.ofFn fullAccept039PoseLookup = fullAccept039.map IndexedRow.pose := by rfl
theorem fullAccept039PoseLookup_mem (i : Fin 4) : fullAccept039PoseLookup i ∈ fullAccept039.map IndexedRow.pose := by
  rw [← fullAccept039PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept039PoseLookup_binding
#print axioms fullAccept039PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
