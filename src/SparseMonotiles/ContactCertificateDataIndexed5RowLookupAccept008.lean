module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept008

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept008PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm0 29 11176 else Pose.ofCodes perm14 29 11176) else (if i.val < 3 then Pose.ofCodes perm19 27 11008 else Pose.ofCodes perm5 27 11008))
theorem fullAccept008PoseLookup_binding : List.ofFn fullAccept008PoseLookup = fullAccept008.map IndexedRow.pose := by rfl
theorem fullAccept008PoseLookup_mem (i : Fin 4) : fullAccept008PoseLookup i ∈ fullAccept008.map IndexedRow.pose := by
  rw [← fullAccept008PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept008PoseLookup_binding
#print axioms fullAccept008PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
