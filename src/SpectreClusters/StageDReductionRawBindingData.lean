module

public import SpectreClusters.StageDReductionRows
public import SpectreClusters.StageDRawCaptureInterface

@[expose] public section

namespace SpectreClusters.StageD.Reduction
def originalCandidateIDs : ClusterKind → List Nat
  | .t7h => [23,35,47,49,98,126,135,153,164,177,179,229,241,258]
  | .t8h => [16,23,28,30,37,40,45,48,55,85,90,95,100,104,107,114,116,118,123,137,144,148,155,162,168,172,177,180,187,191,194,206,217,228,232,236,239,244,249,251,256]
  | .t6h => []
def originalID (k : ClusterKind) (n : Nat) : Nat :=
  (originalCandidateIDs k).getD n 0

def candidateBindingB (k : ClusterKind) : Bool :=
  (List.range (originalCandidateIDs k).length).all fun n =>
    Raw.poseEqB (compactAt k n) ((Raw.candidateList k).getD (originalID k n) Raw.fallback)

def rowBoundsB (k : ClusterKind) : Bool :=
  (compactRowIDs k).all fun row => row.all fun n => n < (originalCandidateIDs k).length

set_option maxRecDepth 100000 in
theorem candidate_binding_checked (k : ClusterKind) : candidateBindingB k = true := by
  cases k <;> rfl

set_option maxRecDepth 100000 in
theorem row_bounds_checked (k : ClusterKind) : rowBoundsB k = true := by
  cases k <;> rfl
end SpectreClusters.StageD.Reduction
