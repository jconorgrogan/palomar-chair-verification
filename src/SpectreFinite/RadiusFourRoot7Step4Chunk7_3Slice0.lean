module

public import SpectreFinite.RadiusFourRoot7Part0Segment08
public import SpectreFinite.RadiusFourRoot7Step4Chunk7_3Rows

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
open HigherFastChecking
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root7Node0Step4Chunk7_3_slice0_checked :
    checkNarrowing ⟨table39Scope, RadiusThreePruning.stateRows7_3_0⟩
      root7Node0Domains3 root7Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains3 root7Node0Domains4
    root7Node0Domains3Fast root7Node0Domains4Fast
    root7Node0Domains3_fast_eq root7Node0Domains4_fast_eq (by decide)

#print axioms root7Node0Step4Chunk7_3_slice0_checked
end SpectreFinite.HexSearch.RadiusFour
