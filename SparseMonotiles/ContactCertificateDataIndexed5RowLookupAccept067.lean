module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept067

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept067PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm4 29 13977 else Pose.ofCodes perm16 29 13977) else (if i.val < 3 then Pose.ofCodes perm10 3 2833 else Pose.ofCodes perm14 3 2833))
theorem fullAccept067PoseLookup_binding : List.ofFn fullAccept067PoseLookup = fullAccept067.map IndexedRow.pose := by rfl
theorem fullAccept067PoseLookup_mem (i : Fin 4) : fullAccept067PoseLookup i ∈ fullAccept067.map IndexedRow.pose := by
  rw [← fullAccept067PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept067PoseLookup_binding
#print axioms fullAccept067PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
