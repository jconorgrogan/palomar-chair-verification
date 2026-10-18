module

public import SpectreFinite.RadiusFiveRoot0Step1Chunk0_1Slice0
public import SpectreFinite.RadiusFiveRoot0Step1Chunk0_1Slice1
public import SpectreFinite.RadiusFiveRoot0Step1Chunk0_1Slice2
public import SpectreFinite.RadiusFiveRoot0Step1Chunk0_2Slice0
public import SpectreFinite.RadiusFiveRoot0Step1Chunk0_2Slice1
public import SpectreFinite.RadiusFiveRoot0Step1Chunk0_2Slice2
public import SpectreFinite.RadiusFiveRoot0Step1Chunk0_3Slice0
public import SpectreFinite.RadiusFiveRoot0Step1Chunk0_3Slice1
public import SpectreFinite.RadiusFiveRoot0Step1Chunk0_3Slice2
public import SpectreFinite.RadiusFiveRoot0Step1Chunk0_4Slice0
public import SpectreFinite.RadiusFiveRoot0Step1Chunk0_4Slice1
public import SpectreFinite.RadiusFiveRoot0Step1Chunk0_4Slice2
public import SpectreFinite.RadiusFiveRoot0Step1Chunk0_5Slice0
public import SpectreFinite.RadiusFiveRoot0Step1Chunk0_5Slice1
public import SpectreFinite.RadiusFiveRoot0Step1Chunk0_5Slice2
public import SpectreFinite.RadiusFiveRoot0Part0Segment01
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
theorem root0Node0Step1Chunk0_1_checked :
    checkNarrowing ⟨table45Scope, table45Rows0_1⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  rw [root0Node0Step1Chunk0_1_rows_exact]
  exact checkNarrowing_flatten table45Scope [RadiusFourPruning.stateRows0_1_0, RadiusFourPruning.stateRows0_1_1, RadiusFourPruning.stateRows0_1_2]
    root0Node0Domains0 root0Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node0Step1Chunk0_1_slice0_checked, root0Node0Step1Chunk0_1_slice1_checked, root0Node0Step1Chunk0_1_slice2_checked, Bool.true_and])
theorem root0Node0Step1Chunk0_2_checked :
    checkNarrowing ⟨table45Scope, table45Rows0_2⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  rw [root0Node0Step1Chunk0_2_rows_exact]
  exact checkNarrowing_flatten table45Scope [RadiusFourPruning.stateRows0_2_0, RadiusFourPruning.stateRows0_2_1, RadiusFourPruning.stateRows0_2_2]
    root0Node0Domains0 root0Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node0Step1Chunk0_2_slice0_checked, root0Node0Step1Chunk0_2_slice1_checked, root0Node0Step1Chunk0_2_slice2_checked, Bool.true_and])
theorem root0Node0Step1Chunk0_3_checked :
    checkNarrowing ⟨table45Scope, table45Rows0_3⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  rw [root0Node0Step1Chunk0_3_rows_exact]
  exact checkNarrowing_flatten table45Scope [RadiusFourPruning.stateRows0_3_0, RadiusFourPruning.stateRows0_3_1, RadiusFourPruning.stateRows0_3_2]
    root0Node0Domains0 root0Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node0Step1Chunk0_3_slice0_checked, root0Node0Step1Chunk0_3_slice1_checked, root0Node0Step1Chunk0_3_slice2_checked, Bool.true_and])
theorem root0Node0Step1Chunk0_4_checked :
    checkNarrowing ⟨table45Scope, table45Rows0_4⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  rw [root0Node0Step1Chunk0_4_rows_exact]
  exact checkNarrowing_flatten table45Scope [RadiusFourPruning.stateRows0_4_0, RadiusFourPruning.stateRows0_4_1, RadiusFourPruning.stateRows0_4_2]
    root0Node0Domains0 root0Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node0Step1Chunk0_4_slice0_checked, root0Node0Step1Chunk0_4_slice1_checked, root0Node0Step1Chunk0_4_slice2_checked, Bool.true_and])
theorem root0Node0Step1Chunk0_5_checked :
    checkNarrowing ⟨table45Scope, table45Rows0_5⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  rw [root0Node0Step1Chunk0_5_rows_exact]
  exact checkNarrowing_flatten table45Scope [RadiusFourPruning.stateRows0_5_0, RadiusFourPruning.stateRows0_5_1, RadiusFourPruning.stateRows0_5_2]
    root0Node0Domains0 root0Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node0Step1Chunk0_5_slice0_checked, root0Node0Step1Chunk0_5_slice1_checked, root0Node0Step1Chunk0_5_slice2_checked, Bool.true_and])
theorem root0Node0Step1Chunk1_0_checked :
    checkNarrowing ⟨table45Scope, table45Rows1_0⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk1_1_checked :
    checkNarrowing ⟨table45Scope, table45Rows1_1⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk1_2_checked :
    checkNarrowing ⟨table45Scope, table45Rows1_2⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk1_3_checked :
    checkNarrowing ⟨table45Scope, table45Rows1_3⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk1_4_checked :
    checkNarrowing ⟨table45Scope, table45Rows1_4⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk1_5_checked :
    checkNarrowing ⟨table45Scope, table45Rows1_5⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk2_0_checked :
    checkNarrowing ⟨table45Scope, table45Rows2_0⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk2_1_checked :
    checkNarrowing ⟨table45Scope, table45Rows2_1⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk2_2_checked :
    checkNarrowing ⟨table45Scope, table45Rows2_2⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk2_3_checked :
    checkNarrowing ⟨table45Scope, table45Rows2_3⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk2_4_checked :
    checkNarrowing ⟨table45Scope, table45Rows2_4⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk2_5_checked :
    checkNarrowing ⟨table45Scope, table45Rows2_5⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk3_0_checked :
    checkNarrowing ⟨table45Scope, table45Rows3_0⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk3_1_checked :
    checkNarrowing ⟨table45Scope, table45Rows3_1⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk3_2_checked :
    checkNarrowing ⟨table45Scope, table45Rows3_2⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk3_3_checked :
    checkNarrowing ⟨table45Scope, table45Rows3_3⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk3_4_checked :
    checkNarrowing ⟨table45Scope, table45Rows3_4⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk3_5_checked :
    checkNarrowing ⟨table45Scope, table45Rows3_5⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk4_0_checked :
    checkNarrowing ⟨table45Scope, table45Rows4_0⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk4_1_checked :
    checkNarrowing ⟨table45Scope, table45Rows4_1⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
#print axioms root0Node0Step1Chunk0_1_checked
#print axioms root0Node0Step1Chunk0_2_checked
#print axioms root0Node0Step1Chunk0_3_checked
#print axioms root0Node0Step1Chunk0_4_checked
#print axioms root0Node0Step1Chunk0_5_checked
end SpectreFinite.HexSearch.RadiusFive
