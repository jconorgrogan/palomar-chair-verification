module
public import SparseMonotiles.SparseBudgetContact
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy
open Contact

/-- Restore the original source-coordinate order from the generator's output rows. -/
def decodeOuterAssignment {d : ℕ} (parent : Pose d) (bs : List Bool) : Bits d :=
  fun j => bs[(parent.perm.symm j).val]?.getD false

theorem decodeOuterAssignment_encode {d : ℕ} (parent : Pose d) (a : Bits d) :
    decodeOuterAssignment parent ((List.finRange d).map fun i => a (parent.perm i)) = a := by
  funext j
  simp [decodeOuterAssignment, (parent.perm.symm j).isLt]

/-- Sparse output in source-coordinate order. It does not enumerate all roles. -/
def generatedOuterBits {d : ℕ} (root parent : Pose d) : List (Bits d) :=
  (BooleanBudget.generate ((List.finRange d).map (outerCoordinateCost root parent)) 1).map
    (decodeOuterAssignment parent)

theorem cellContact_refinedOuter_generated {d : ℕ}
    (root parent : Pose d) (a : Bits d) (σ : Equiv.Perm (Fin d))
    (hc : CellContact root (compose (dilatePose parent) (outerPose a σ))) :
    a ∈ generatedOuterBits root parent := by
  apply List.mem_map.mpr
  exact ⟨_, cellContact_refinedOuter_assignment_generated root parent a σ hc,
    decodeOuterAssignment_encode parent a⟩

/-- Sparse proper outer poses for any fixed child-permutation family. -/
def generatedOuterChildren {d : ℕ} (root parent : Pose d)
    (σ : Bits d → Equiv.Perm (Fin d)) : List (Pose d) :=
  ((generatedOuterBits root parent).filter fun a => decide (Proper a)).map
    (fun a => outerPose a (σ a))

theorem cellContact_refinedOuter_child_generated {d : ℕ}
    (root parent : Pose d) (a : Bits d) (σ : Bits d → Equiv.Perm (Fin d))
    (ha : Proper a)
    (hc : CellContact root (compose (dilatePose parent) (outerPose a (σ a)))) :
    outerPose a (σ a) ∈ generatedOuterChildren root parent σ := by
  apply List.mem_map.mpr
  refine ⟨a, ?_, rfl⟩
  exact List.mem_filter.mpr ⟨cellContact_refinedOuter_generated root parent a (σ a) hc,
    by simpa only [decide_eq_true_eq] using ha⟩

/-- The central child has its own direct budget test. -/
def centralBudgetB {d : ℕ} (root parent : Pose d) : Bool :=
  decide (((List.finRange d).map fun i =>
    coordinateGapCost (boxLower root i) (centralLowerChoice parent i)).sum ≤ 1)

theorem cellContact_refinedCentral_budget {d : ℕ} (root parent : Pose d)
    (hc : CellContact root (compose (dilatePose parent) (centralPose d))) :
    centralBudgetB root parent = true := by
  apply decide_eq_true (by simpa only [refinedCentral_boxLower] using cellContact_gapCost_sum hc)

/-- Complete sparse canonical child list, with the central role kept separate. -/
def generatedChildren {d : ℕ} (root parent : Pose d)
    (σ : Bits d → Equiv.Perm (Fin d)) : List (Pose d) :=
  (if centralBudgetB root parent then [centralPose d] else []) ++
    generatedOuterChildren root parent σ

theorem cellContact_refinedCentral_child_generated {d : ℕ}
    (root parent : Pose d) (σ : Bits d → Equiv.Perm (Fin d))
    (hc : CellContact root (compose (dilatePose parent) (centralPose d))) :
    centralPose d ∈ generatedChildren root parent σ := by
  simp [generatedChildren, cellContact_refinedCentral_budget root parent hc]

#print axioms decodeOuterAssignment_encode
#print axioms cellContact_refinedOuter_generated
#print axioms cellContact_refinedOuter_child_generated
#print axioms cellContact_refinedCentral_budget
#print axioms cellContact_refinedCentral_child_generated
end SparseMonotiles.CarrierHierarchy
