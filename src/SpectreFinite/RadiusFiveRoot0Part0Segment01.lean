module

public import SpectreFinite.RadiusFiveRoot0Step1Chunk0_0Slice0
public import SpectreFinite.RadiusFiveRoot0Step1Chunk0_0Slice1
public import SpectreFinite.RadiusFiveRoot0Step1Chunk0_0Slice2
public import SpectreFinite.RadiusFiveRoot0Part0Segment00
public import SpectreFinite.RadiusFiveRoot0Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable2
public import SpectreFinite.RadiusFiveTable33
public import SpectreFinite.RadiusFiveTable45
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
theorem root0Node0Step1Chunk0_0_checked :
    checkNarrowing ⟨table45Scope, table45Rows0_0⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  rw [root0Node0Step1Chunk0_0_rows_exact]
  exact checkNarrowing_flatten table45Scope [RadiusFourPruning.stateRows0_0_0, RadiusFourPruning.stateRows0_0_1, RadiusFourPruning.stateRows0_0_2]
    root0Node0Domains0 root0Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node0Step1Chunk0_0_slice0_checked, root0Node0Step1Chunk0_0_slice1_checked, root0Node0Step1Chunk0_0_slice2_checked, Bool.true_and])

#print axioms root0Node0Step1Chunk0_0_checked
end SpectreFinite.HexSearch.RadiusFive
