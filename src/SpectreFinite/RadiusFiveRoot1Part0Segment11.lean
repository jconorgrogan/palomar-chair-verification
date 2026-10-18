module

public import SpectreFinite.RadiusFiveRoot1Part0Segment10
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
theorem root1Node0Step4Chunk8_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_1⟩
      root1Node0Domains3 root1Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains3 root1Node0Domains4
    root1Node0Domains3Fast root1Node0Domains4Fast
    root1Node0Domains3_fast_eq root1Node0Domains4_fast_eq (by decide)
theorem root1Node0Step4Chunk8_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_2⟩
      root1Node0Domains3 root1Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains3 root1Node0Domains4
    root1Node0Domains3Fast root1Node0Domains4Fast
    root1Node0Domains3_fast_eq root1Node0Domains4_fast_eq (by decide)
theorem root1Node0Step4Chunk8_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_3⟩
      root1Node0Domains3 root1Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains3 root1Node0Domains4
    root1Node0Domains3Fast root1Node0Domains4Fast
    root1Node0Domains3_fast_eq root1Node0Domains4_fast_eq (by decide)
theorem root1Node0Step4Chunk8_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_4⟩
      root1Node0Domains3 root1Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains3 root1Node0Domains4
    root1Node0Domains3Fast root1Node0Domains4Fast
    root1Node0Domains3_fast_eq root1Node0Domains4_fast_eq (by decide)
theorem root1Node0Step4Chunk8_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_5⟩
      root1Node0Domains3 root1Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains3 root1Node0Domains4
    root1Node0Domains3Fast root1Node0Domains4Fast
    root1Node0Domains3_fast_eq root1Node0Domains4_fast_eq (by decide)
theorem root1Node0Step4Narrowing_checked :
    checkNarrowing table2 root1Node0Domains3 root1Node0Domains4 = true := by
  exact checkNarrowing_flatten table2Scope [table2Rows0_0,table2Rows0_1,table2Rows0_2,table2Rows0_3,table2Rows0_4,table2Rows0_5,table2Rows1_0,table2Rows1_1,table2Rows1_2,table2Rows1_3,table2Rows1_4,table2Rows1_5,table2Rows2_0,table2Rows2_1,table2Rows2_2,table2Rows2_3,table2Rows2_4,table2Rows2_5,table2Rows3_0,table2Rows3_1,table2Rows3_2,table2Rows3_3,table2Rows3_4,table2Rows3_5,table2Rows4_0,table2Rows4_1,table2Rows4_2,table2Rows4_3,table2Rows4_4,table2Rows4_5,table2Rows5_0,table2Rows5_1,table2Rows5_2,table2Rows5_3,table2Rows5_4,table2Rows5_5,table2Rows6_0,table2Rows6_1,table2Rows6_2,table2Rows6_3,table2Rows6_4,table2Rows6_5,table2Rows7_0,table2Rows7_1,table2Rows7_2,table2Rows7_3,table2Rows7_4,table2Rows7_5,table2Rows8_0,table2Rows8_1,table2Rows8_2,table2Rows8_3,table2Rows8_4,table2Rows8_5]
    root1Node0Domains3 root1Node0Domains4 (by
      simp only [List.all_cons, List.all_nil, root1Node0Step4Chunk0_0_checked, root1Node0Step4Chunk0_1_checked, root1Node0Step4Chunk0_2_checked, root1Node0Step4Chunk0_3_checked, root1Node0Step4Chunk0_4_checked, root1Node0Step4Chunk0_5_checked, root1Node0Step4Chunk1_0_checked, root1Node0Step4Chunk1_1_checked, root1Node0Step4Chunk1_2_checked, root1Node0Step4Chunk1_3_checked, root1Node0Step4Chunk1_4_checked, root1Node0Step4Chunk1_5_checked, root1Node0Step4Chunk2_0_checked, root1Node0Step4Chunk2_1_checked, root1Node0Step4Chunk2_2_checked, root1Node0Step4Chunk2_3_checked, root1Node0Step4Chunk2_4_checked, root1Node0Step4Chunk2_5_checked, root1Node0Step4Chunk3_0_checked, root1Node0Step4Chunk3_1_checked, root1Node0Step4Chunk3_2_checked, root1Node0Step4Chunk3_3_checked, root1Node0Step4Chunk3_4_checked, root1Node0Step4Chunk3_5_checked, root1Node0Step4Chunk4_0_checked, root1Node0Step4Chunk4_1_checked, root1Node0Step4Chunk4_2_checked, root1Node0Step4Chunk4_3_checked, root1Node0Step4Chunk4_4_checked, root1Node0Step4Chunk4_5_checked, root1Node0Step4Chunk5_0_checked, root1Node0Step4Chunk5_1_checked, root1Node0Step4Chunk5_2_checked, root1Node0Step4Chunk5_3_checked, root1Node0Step4Chunk5_4_checked, root1Node0Step4Chunk5_5_checked, root1Node0Step4Chunk6_0_checked, root1Node0Step4Chunk6_1_checked, root1Node0Step4Chunk6_2_checked, root1Node0Step4Chunk6_3_checked, root1Node0Step4Chunk6_4_checked, root1Node0Step4Chunk6_5_checked, root1Node0Step4Chunk7_0_checked, root1Node0Step4Chunk7_1_checked, root1Node0Step4Chunk7_2_checked, root1Node0Step4Chunk7_3_checked, root1Node0Step4Chunk7_4_checked, root1Node0Step4Chunk7_5_checked, root1Node0Step4Chunk8_0_checked, root1Node0Step4Chunk8_1_checked, root1Node0Step4Chunk8_2_checked, root1Node0Step4Chunk8_3_checked, root1Node0Step4Chunk8_4_checked, root1Node0Step4Chunk8_5_checked, Bool.true_and])
theorem root1Node0Step4_checked :
    checkReplacement table2 root1Node0Domains3 root1Node0Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root1Node0Domains3 root1Node0Domains4
    root1Node0Domains3Fast root1Node0Domains4Fast
    root1Node0Domains3_fast_eq root1Node0Domains4_fast_eq
    root1Node0Step4Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
