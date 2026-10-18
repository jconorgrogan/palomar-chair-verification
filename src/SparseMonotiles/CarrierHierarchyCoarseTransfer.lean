module

public import SparseMonotiles.CarrierHierarchyCoarseChecker

@[expose] public section

/-! Two-language finite transfer API. T7 uses fine E318 and coarse M408;
this leaves the existing one-language T5 schema unchanged. -/
namespace SparseMonotiles.CarrierHierarchy
open Contact

def CoarseWitness.ValidBetween {d : ℕ} (C : Finset (Pose d))
    (Lfine Lcoarse : Set (Pose d)) (F : Pose d) : CoarseWitness d → Prop
  | .member => coarsePose (fun _ => 0) F ∈ Lcoarse
  | .overlap c => ParentOccupies (rootPose d) c ∧ ParentOccupies F c
  | .illegalChild a b c e => a ∈ C ∧ b ∈ C ∧ Occupies a c ∧
      Occupies (compose F b) e ∧ AdjacentCells c e ∧ normalize a (compose F b) ∉ Lfine

instance coarseDecidableValidBetween {d : ℕ} (C : Finset (Pose d))
    (Lfine Lcoarse : Set (Pose d)) [DecidablePred Lfine] [DecidablePred Lcoarse]
    (F : Pose d) (w : CoarseWitness d) : Decidable (w.ValidBetween C Lfine Lcoarse F) := by
  cases w with
  | member => exact ‹DecidablePred Lcoarse› _
  | overlap c => exact inferInstanceAs (Decidable (ParentOccupies (rootPose d) c ∧ ParentOccupies F c))
  | illegalChild a b c e =>
      exact inferInstanceAs (Decidable (a ∈ C ∧ b ∈ C ∧ Occupies a c ∧
        Occupies (compose F b) e ∧ AdjacentCells c e ∧ ¬ Lfine (normalize a (compose F b))))

theorem CoarseWitness.validBetween_same {d : ℕ} (C : Finset (Pose d))
    (L : Set (Pose d)) (F : Pose d) (w : CoarseWitness d) :
    w.ValidBetween C L L F ↔ w.Valid C L F := by cases w <;> rfl
end SparseMonotiles.CarrierHierarchy
