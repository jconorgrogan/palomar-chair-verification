module

public import SpectreFinite.RadiusFiveRoot1Step1Chunk1_0Slice0
public import SpectreFinite.RadiusFiveRoot1Step1Chunk1_0Slice1
public import SpectreFinite.RadiusFiveRoot1Step1Chunk1_0Slice2
public import SpectreFinite.RadiusFiveRoot1Step1Chunk1_1Slice0
public import SpectreFinite.RadiusFiveRoot1Step1Chunk1_1Slice1
public import SpectreFinite.RadiusFiveRoot1Step1Chunk1_1Slice2
public import SpectreFinite.RadiusFiveRoot1Step1Chunk1_2Slice0
public import SpectreFinite.RadiusFiveRoot1Step1Chunk1_2Slice1
public import SpectreFinite.RadiusFiveRoot1Step1Chunk1_2Slice2
public import SpectreFinite.RadiusFiveRoot1Step1Chunk1_3Slice0
public import SpectreFinite.RadiusFiveRoot1Step1Chunk1_3Slice1
public import SpectreFinite.RadiusFiveRoot1Step1Chunk1_3Slice2
public import SpectreFinite.RadiusFiveRoot1Step1Chunk1_4Slice0
public import SpectreFinite.RadiusFiveRoot1Step1Chunk1_4Slice1
public import SpectreFinite.RadiusFiveRoot1Step1Chunk1_4Slice2
public import SpectreFinite.RadiusFiveRoot1Step1Chunk1_5Slice0
public import SpectreFinite.RadiusFiveRoot1Step1Chunk1_5Slice1
public import SpectreFinite.RadiusFiveRoot1Step1Chunk1_5Slice2
public import SpectreFinite.RadiusFiveRoot1Part0Segment01
public import SpectreFinite.RadiusFiveRoot1Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable2
public import SpectreFinite.RadiusFiveTable34
public import SpectreFinite.RadiusFiveTable52
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
theorem root1Node0Step1Chunk0_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_1⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk0_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_2⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk0_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_3⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk0_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_4⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk0_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_5⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk1_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_0⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  rw [root1Node0Step1Chunk1_0_rows_exact]
  exact checkNarrowing_flatten table34Scope [RadiusFourPruning.stateRows1_0_0, RadiusFourPruning.stateRows1_0_1, RadiusFourPruning.stateRows1_0_2]
    root1Node0Domains0 root1Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node0Step1Chunk1_0_slice0_checked, root1Node0Step1Chunk1_0_slice1_checked, root1Node0Step1Chunk1_0_slice2_checked, Bool.true_and])
theorem root1Node0Step1Chunk1_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_1⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  rw [root1Node0Step1Chunk1_1_rows_exact]
  exact checkNarrowing_flatten table34Scope [RadiusFourPruning.stateRows1_1_0, RadiusFourPruning.stateRows1_1_1, RadiusFourPruning.stateRows1_1_2]
    root1Node0Domains0 root1Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node0Step1Chunk1_1_slice0_checked, root1Node0Step1Chunk1_1_slice1_checked, root1Node0Step1Chunk1_1_slice2_checked, Bool.true_and])
theorem root1Node0Step1Chunk1_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_2⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  rw [root1Node0Step1Chunk1_2_rows_exact]
  exact checkNarrowing_flatten table34Scope [RadiusFourPruning.stateRows1_2_0, RadiusFourPruning.stateRows1_2_1, RadiusFourPruning.stateRows1_2_2]
    root1Node0Domains0 root1Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node0Step1Chunk1_2_slice0_checked, root1Node0Step1Chunk1_2_slice1_checked, root1Node0Step1Chunk1_2_slice2_checked, Bool.true_and])
theorem root1Node0Step1Chunk1_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_3⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  rw [root1Node0Step1Chunk1_3_rows_exact]
  exact checkNarrowing_flatten table34Scope [RadiusFourPruning.stateRows1_3_0, RadiusFourPruning.stateRows1_3_1, RadiusFourPruning.stateRows1_3_2]
    root1Node0Domains0 root1Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node0Step1Chunk1_3_slice0_checked, root1Node0Step1Chunk1_3_slice1_checked, root1Node0Step1Chunk1_3_slice2_checked, Bool.true_and])
theorem root1Node0Step1Chunk1_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_4⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  rw [root1Node0Step1Chunk1_4_rows_exact]
  exact checkNarrowing_flatten table34Scope [RadiusFourPruning.stateRows1_4_0, RadiusFourPruning.stateRows1_4_1, RadiusFourPruning.stateRows1_4_2]
    root1Node0Domains0 root1Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node0Step1Chunk1_4_slice0_checked, root1Node0Step1Chunk1_4_slice1_checked, root1Node0Step1Chunk1_4_slice2_checked, Bool.true_and])
theorem root1Node0Step1Chunk1_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_5⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  rw [root1Node0Step1Chunk1_5_rows_exact]
  exact checkNarrowing_flatten table34Scope [RadiusFourPruning.stateRows1_5_0, RadiusFourPruning.stateRows1_5_1, RadiusFourPruning.stateRows1_5_2]
    root1Node0Domains0 root1Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node0Step1Chunk1_5_slice0_checked, root1Node0Step1Chunk1_5_slice1_checked, root1Node0Step1Chunk1_5_slice2_checked, Bool.true_and])
theorem root1Node0Step1Chunk2_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_0⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk2_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_1⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk2_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_2⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk2_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_3⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk2_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_4⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk2_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_5⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk3_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_0⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk3_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_1⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk3_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_2⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk3_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_3⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk3_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_4⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk3_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_5⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk4_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_0⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk4_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_1⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
#print axioms root1Node0Step1Chunk1_0_checked
#print axioms root1Node0Step1Chunk1_1_checked
#print axioms root1Node0Step1Chunk1_2_checked
#print axioms root1Node0Step1Chunk1_3_checked
#print axioms root1Node0Step1Chunk1_4_checked
#print axioms root1Node0Step1Chunk1_5_checked
end SpectreFinite.HexSearch.RadiusFive
