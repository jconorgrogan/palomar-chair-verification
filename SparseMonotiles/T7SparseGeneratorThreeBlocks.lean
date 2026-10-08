module
public import SparseMonotiles.T7SparseGeneratedRoles
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7SparseGenerator
open Contact T7SparseForwardBlock
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Kernel reduction of the sparse generator, not an all-source coverage scan. -/
theorem zero_generated_exact : generatedCodes (sourceChild 0) (registry 0) = [] := by
  decide +kernel

theorem one_generated_exact : generatedCodes (sourceChild 63) (registry 0) = [115] := by
  decide +kernel

theorem eight_generated_exact :
    (generatedCodes (sourceChild 11) (registry 2)).toFinset =
      {63,95,111,119,123,125,126,127} := by
  decide +kernel

theorem eight_generated_list :
    generatedCodes (sourceChild 11) (registry 2) =
      [63,95,111,119,123,125,126,127] := by
  decide +kernel

/-- Number of recursive states visited, including successful leaf states. -/
def generatorVisits : List (Bool → ℕ) → ℕ → ℕ
  | [], _ => 1
  | c :: cs, budget => 1 +
      (if c false ≤ budget then generatorVisits cs (budget - c false) else 0) +
      (if c true ≤ budget then generatorVisits cs (budget - c true) else 0)

/-- Number of nonterminal states; each considers exactly two bit costs. -/
def generatorBranches : List (Bool → ℕ) → ℕ → ℕ
  | [], _ => 0
  | c :: cs, budget => 1 +
      (if c false ≤ budget then generatorBranches cs (budget - c false) else 0) +
      (if c true ≤ budget then generatorBranches cs (budget - c true) else 0)

def workCounts (root parent : Pose 7) : ℕ × ℕ × ℕ :=
  let costs := (List.finRange 7).map (outerCoordinateCost root parent)
  (generatorVisits costs 1, generatorBranches costs 1,
    (BooleanBudget.generate costs 1).length)

/-- Exact algorithmic work for the three bounded pilot blocks. Counts are
(visited states, nonterminal states, outer assignments before exclusion). -/
theorem three_work_counts :
    workCounts (sourceChild 0) (registry 0) = (2,2,0) ∧
    workCounts (sourceChild 63) (registry 0) = (29,28,1) ∧
    workCounts (sourceChild 11) (registry 2) = (36,28,8) := by
  decide +kernel

#print axioms zero_generated_exact
#print axioms one_generated_exact
#print axioms eight_generated_exact
#print axioms eight_generated_list
#print axioms three_work_counts
end SparseMonotiles.CarrierHierarchy.T7SparseGenerator
