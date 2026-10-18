module

public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

namespace SparseMonotiles.Contact

theorem indexedValidate_append_true {d n : ℕ} {g : IndexedGeometry d n}
    {a b : List (IndexedRow d n)}
    (ha : indexedValidate g a = true) (hb : indexedValidate g b = true) :
    indexedValidate g (a ++ b) = true := by
  rw [indexedValidate_append, ha, hb]
  rfl

theorem indexedOutput_append {d n : ℕ} {a b : List (IndexedRow d n)}
    {oa ob : List (Pose d)}
    (ha : indexedAcceptedPoses a = oa) (hb : indexedAcceptedPoses b = ob) :
    indexedAcceptedPoses (a ++ b) = oa ++ ob := by
  rw [indexedAcceptedPoses_append, ha, hb]

theorem list_length_append_of_eq {α : Type*} {a b : List α} {m n : ℕ}
    (ha : a.length = m) (hb : b.length = n) : (a ++ b).length = m + n := by
  rw [List.length_append, ha, hb]

#print axioms indexedValidate_append_true
#print axioms indexedOutput_append
end SparseMonotiles.Contact
