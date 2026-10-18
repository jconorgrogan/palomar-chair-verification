module

public import SpectreFinite.RadiusFiveRoot4Step1Chunk4_2Slice0
public import SpectreFinite.RadiusFiveRoot4Step1Chunk4_2Slice1
public import SpectreFinite.RadiusFiveRoot4Step1Chunk4_2Slice2
public import SpectreFinite.RadiusFiveRoot4Step1Chunk4_3Slice0
public import SpectreFinite.RadiusFiveRoot4Step1Chunk4_3Slice1
public import SpectreFinite.RadiusFiveRoot4Step1Chunk4_3Slice2
public import SpectreFinite.RadiusFiveRoot4Step1Chunk4_4Slice0
public import SpectreFinite.RadiusFiveRoot4Step1Chunk4_4Slice1
public import SpectreFinite.RadiusFiveRoot4Step1Chunk4_4Slice2
public import SpectreFinite.RadiusFiveRoot4Step1Chunk4_5Slice0
public import SpectreFinite.RadiusFiveRoot4Step1Chunk4_5Slice1
public import SpectreFinite.RadiusFiveRoot4Step1Chunk4_5Slice2
public import SpectreFinite.RadiusFiveRoot4Part0Segment02
public import SpectreFinite.RadiusFiveRoot4Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable12
public import SpectreFinite.RadiusFiveTable33
public import SpectreFinite.RadiusFiveTable51
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
theorem root4Node0Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  rw [root4Node0Step1Chunk4_2_rows_exact]
  exact checkNarrowing_flatten table56Scope [RadiusFourPruning.stateRows4_2_0, RadiusFourPruning.stateRows4_2_1, RadiusFourPruning.stateRows4_2_2]
    root4Node0Domains0 root4Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node0Step1Chunk4_2_slice0_checked, root4Node0Step1Chunk4_2_slice1_checked, root4Node0Step1Chunk4_2_slice2_checked, Bool.true_and])
theorem root4Node0Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  rw [root4Node0Step1Chunk4_3_rows_exact]
  exact checkNarrowing_flatten table56Scope [RadiusFourPruning.stateRows4_3_0, RadiusFourPruning.stateRows4_3_1, RadiusFourPruning.stateRows4_3_2]
    root4Node0Domains0 root4Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node0Step1Chunk4_3_slice0_checked, root4Node0Step1Chunk4_3_slice1_checked, root4Node0Step1Chunk4_3_slice2_checked, Bool.true_and])
theorem root4Node0Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  rw [root4Node0Step1Chunk4_4_rows_exact]
  exact checkNarrowing_flatten table56Scope [RadiusFourPruning.stateRows4_4_0, RadiusFourPruning.stateRows4_4_1, RadiusFourPruning.stateRows4_4_2]
    root4Node0Domains0 root4Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node0Step1Chunk4_4_slice0_checked, root4Node0Step1Chunk4_4_slice1_checked, root4Node0Step1Chunk4_4_slice2_checked, Bool.true_and])
theorem root4Node0Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  rw [root4Node0Step1Chunk4_5_rows_exact]
  exact checkNarrowing_flatten table56Scope [RadiusFourPruning.stateRows4_5_0, RadiusFourPruning.stateRows4_5_1, RadiusFourPruning.stateRows4_5_2]
    root4Node0Domains0 root4Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node0Step1Chunk4_5_slice0_checked, root4Node0Step1Chunk4_5_slice1_checked, root4Node0Step1Chunk4_5_slice2_checked, Bool.true_and])
theorem root4Node0Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
#print axioms root4Node0Step1Chunk4_2_checked
#print axioms root4Node0Step1Chunk4_3_checked
#print axioms root4Node0Step1Chunk4_4_checked
#print axioms root4Node0Step1Chunk4_5_checked
end SpectreFinite.HexSearch.RadiusFive
