module

public import SpectreFinite.RadiusFourRoot7Step1Chunk7_0Slice0
public import SpectreFinite.RadiusFourRoot7Step1Chunk7_0Slice1
public import SpectreFinite.RadiusFourRoot7Step1Chunk7_0Slice2
public import SpectreFinite.RadiusFourRoot7Step1Chunk7_0Slice3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
open HigherFastChecking
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root7Node0Step1Chunk7_0_symbolic_pilot_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_0⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  rw [root7Node0Step1Chunk7_0_rows_exact]
  exact checkNarrowing_flatten table30Scope [RadiusThreePruning.stateRows7_0_0, RadiusThreePruning.stateRows7_0_1, RadiusThreePruning.stateRows7_0_2, RadiusThreePruning.stateRows7_0_3]
    root7Node0Domains0 root7Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node0Step1Chunk7_0_slice0_checked, root7Node0Step1Chunk7_0_slice1_checked, root7Node0Step1Chunk7_0_slice2_checked, root7Node0Step1Chunk7_0_slice3_checked, Bool.true_and])

#print axioms root7Node0Step1Chunk7_0_symbolic_pilot_checked
end SpectreFinite.HexSearch.RadiusFour
