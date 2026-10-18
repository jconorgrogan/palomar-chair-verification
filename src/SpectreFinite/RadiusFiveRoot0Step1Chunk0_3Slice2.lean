module

public import SpectreFinite.RadiusFiveRoot0Part0Segment00
public import SpectreFinite.RadiusFiveRoot0Step1Chunk0_3Rows

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
open HigherFastChecking
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root0Node0Step1Chunk0_3_slice2_checked :
    checkNarrowing ⟨table45Scope, RadiusFourPruning.stateRows0_3_2⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)

#print axioms root0Node0Step1Chunk0_3_slice2_checked
end SpectreFinite.HexSearch.RadiusFive
