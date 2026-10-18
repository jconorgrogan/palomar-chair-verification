module

public import SpectreFinite.RadiusFiveRoot0Part0Segment04
public import SpectreFinite.RadiusFiveRoot0Step2Chunk6_4ProjectedRows

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
open HigherFastChecking
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem root0Node0Step2Chunk6_4_projected_slice1_checked :
    checkNarrowing ⟨table57Scope, root0Node0Step2Chunk6_4_projectedRows1⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)

#print axioms root0Node0Step2Chunk6_4_projected_slice1_checked
end SpectreFinite.HexSearch.RadiusFive
