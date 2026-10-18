module

public import SparseMonotiles.ContactCertificateDataIndexed5FullAccept002

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def fullAccept002PoseLookup : Fin 4 → Pose 5 := fun i =>
  (if i.val < 2 then (if i.val < 1 then Pose.ofCodes perm1 8 5602 else Pose.ofCodes perm2 8 5602) else (if i.val < 3 then Pose.ofCodes perm2 16 5602 else Pose.ofCodes perm1 16 5602))
theorem fullAccept002PoseLookup_binding : List.ofFn fullAccept002PoseLookup = fullAccept002.map IndexedRow.pose := by rfl
theorem fullAccept002PoseLookup_mem (i : Fin 4) : fullAccept002PoseLookup i ∈ fullAccept002.map IndexedRow.pose := by
  rw [← fullAccept002PoseLookup_binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩
#print axioms fullAccept002PoseLookup_binding
#print axioms fullAccept002PoseLookup_mem
end SparseMonotiles.Contact.IndexedData5
