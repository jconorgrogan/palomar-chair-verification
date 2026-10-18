module

public import SparseMonotiles.CoarseContactCertificates

@[expose] public section

namespace SparseMonotiles.CarrierHierarchy
open Contact

/-- Checking F b = a k avoids evaluating an inverse at each coordinate. -/
def coarseProductMatchB {d : ℕ} (a b k F : Pose d) : Bool :=
  coarsePoseMatchB (compose F b) (compose a k)

theorem coarseProductMatchB_sound {d : ℕ} {a b k F : Pose d}
    (h : coarseProductMatchB a b k F = true) : parentCandidate a b k = F := by
  have hEq := coarsePoseMatchB_sound h
  have hh := congrArg (fun p => compose p (inversePose b)) hEq
  simpa only [compose_assoc, compose_inversePose, compose_root_right, parentCandidate]
    using hh.symm

def coarseProductAddressCheck {d : ℕ} {ρ : Type*} (lookup : ρ → Pose d)
    (a b k : Pose d) : Option ρ → Bool
  | none => decide (∃ i, (parentCandidate a b k).shift i % 2 ≠ 0)
  | some i => coarseProductMatchB a b k (lookup i)

theorem coarseProductAddressCheck_sound {d : ℕ} {ρ : Type*} (lookup : ρ → Pose d)
    {a b k : Pose d} {address : Option ρ}
    (h : coarseProductAddressCheck lookup a b k address = true)
    (heven : ∀ i, (parentCandidate a b k).shift i % 2 = 0) :
    ∃ i, parentCandidate a b k = lookup i := by
  cases address with
  | none =>
      obtain ⟨i, hi⟩ := of_decide_eq_true h
      exact False.elim (hi (heven i))
  | some i => exact ⟨i, coarseProductMatchB_sound h⟩

#print axioms coarseProductMatchB_sound
#print axioms coarseProductAddressCheck_sound
end SparseMonotiles.CarrierHierarchy
