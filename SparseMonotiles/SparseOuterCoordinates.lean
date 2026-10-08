module
public import SparseMonotiles.ForwardSparseCoverage
public import SparseMonotiles.SparseBooleanBudget
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy
open Contact

/-- Lower coordinate contributed by one outer-child bit in output-row order. -/
def outerLowerChoice {d : ℕ} (parent : Pose d) (i : Fin d) (b : Bool) : ℤ :=
  2 * parent.shift i - (if parent.negative i then 2 else 0) +
    if b then 2 * parent.sign i else 0

/-- Crucially, the lower box never depends on the outer child's permutation. -/
theorem refinedOuter_boxLower {d : ℕ} (parent : Pose d) (a : Bits d)
    (σ : Equiv.Perm (Fin d)) (i : Fin d) :
    boxLower (compose (dilatePose parent) (outerPose a σ)) i =
      outerLowerChoice parent i (a (parent.perm i)) := by
  cases hp : parent.negative i <;> cases ha : a (parent.perm i) <;>
    simp [boxLower, compose, dilatePose, outerPose, outerLowerChoice, Pose.sign, bit, hp, ha] <;> omega

def centralLowerChoice {d : ℕ} (parent : Pose d) (i : Fin d) : ℤ :=
  2 * parent.shift i + parent.sign i - (if parent.negative i then 2 else 0)

theorem refinedCentral_boxLower {d : ℕ} (parent : Pose d) (i : Fin d) :
    boxLower (compose (dilatePose parent) (centralPose d)) i =
      centralLowerChoice parent i := by
  cases hp : parent.negative i <;>
    simp [boxLower, compose, dilatePose, centralPose, centralLowerChoice, Pose.sign, hp] <;> omega

/-- Natural nonnegative excess over a unit box interval. -/
def coordinateGapCost (x y : ℤ) : ℕ := (x - y).natAbs - 1

def outerCoordinateCost {d : ℕ} (root parent : Pose d) (i : Fin d) (b : Bool) : ℕ :=
  coordinateGapCost (boxLower root i) (outerLowerChoice parent i b)

theorem refinedOuter_gapCost {d : ℕ} (root parent : Pose d) (a : Bits d)
    (σ : Equiv.Perm (Fin d)) (i : Fin d) :
    coordinateGapCost (boxLower root i)
        (boxLower (compose (dilatePose parent) (outerPose a σ)) i) =
      outerCoordinateCost root parent i (a (parent.perm i)) := by
  rw [refinedOuter_boxLower]
  rfl

/-- A directly usable generator completeness bridge. The only geometric
premise is the sum-of-gap-cost bound; there is no scan over child roles. -/
theorem refinedOuter_assignment_generated {d : ℕ} (root parent : Pose d) (a : Bits d)
    (σ : Equiv.Perm (Fin d)) (budget : ℕ)
    (hcost : ((List.finRange d).map fun i =>
      coordinateGapCost (boxLower root i)
        (boxLower (compose (dilatePose parent) (outerPose a σ)) i)).sum ≤ budget) :
    (List.finRange d).map (fun i => a (parent.perm i)) ∈
      BooleanBudget.generate ((List.finRange d).map (outerCoordinateCost root parent)) budget := by
  apply (BooleanBudget.mem_generate_map _ _ _ _).mpr
  simpa only [refinedOuter_gapCost] using hcost

#print axioms refinedOuter_boxLower
#print axioms refinedCentral_boxLower
#print axioms refinedOuter_gapCost
#print axioms refinedOuter_assignment_generated
end SparseMonotiles.CarrierHierarchy
