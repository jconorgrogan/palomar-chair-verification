module

public import SpectreFinite.RadiusFiveRoot5Part0Segment10
public import SpectreFinite.RadiusFiveRoot5Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable12
public import SpectreFinite.RadiusFiveTable25
public import SpectreFinite.RadiusFiveTable51
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
theorem root5Node0Step4Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Narrowing_checked :
    checkNarrowing table12 root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_flatten table12Scope [table12Rows0_0,table12Rows0_1,table12Rows0_2,table12Rows0_3,table12Rows0_4,table12Rows0_5,table12Rows1_0,table12Rows1_1,table12Rows1_2,table12Rows1_3,table12Rows1_4,table12Rows1_5,table12Rows2_0,table12Rows2_1,table12Rows2_2,table12Rows2_3,table12Rows2_4,table12Rows2_5,table12Rows3_0,table12Rows3_1,table12Rows3_2,table12Rows3_3,table12Rows3_4,table12Rows3_5,table12Rows4_0,table12Rows4_1,table12Rows4_2,table12Rows4_3,table12Rows4_4,table12Rows4_5,table12Rows5_0,table12Rows5_1,table12Rows5_2,table12Rows5_3,table12Rows5_4,table12Rows5_5,table12Rows6_0,table12Rows6_1,table12Rows6_2,table12Rows6_3,table12Rows6_4,table12Rows6_5,table12Rows7_0,table12Rows7_1,table12Rows7_2,table12Rows7_3,table12Rows7_4,table12Rows7_5,table12Rows8_0,table12Rows8_1,table12Rows8_2,table12Rows8_3,table12Rows8_4,table12Rows8_5]
    root5Node0Domains3 root5Node0Domains4 (by
      simp only [List.all_cons, List.all_nil, root5Node0Step4Chunk0_0_checked, root5Node0Step4Chunk0_1_checked, root5Node0Step4Chunk0_2_checked, root5Node0Step4Chunk0_3_checked, root5Node0Step4Chunk0_4_checked, root5Node0Step4Chunk0_5_checked, root5Node0Step4Chunk1_0_checked, root5Node0Step4Chunk1_1_checked, root5Node0Step4Chunk1_2_checked, root5Node0Step4Chunk1_3_checked, root5Node0Step4Chunk1_4_checked, root5Node0Step4Chunk1_5_checked, root5Node0Step4Chunk2_0_checked, root5Node0Step4Chunk2_1_checked, root5Node0Step4Chunk2_2_checked, root5Node0Step4Chunk2_3_checked, root5Node0Step4Chunk2_4_checked, root5Node0Step4Chunk2_5_checked, root5Node0Step4Chunk3_0_checked, root5Node0Step4Chunk3_1_checked, root5Node0Step4Chunk3_2_checked, root5Node0Step4Chunk3_3_checked, root5Node0Step4Chunk3_4_checked, root5Node0Step4Chunk3_5_checked, root5Node0Step4Chunk4_0_checked, root5Node0Step4Chunk4_1_checked, root5Node0Step4Chunk4_2_checked, root5Node0Step4Chunk4_3_checked, root5Node0Step4Chunk4_4_checked, root5Node0Step4Chunk4_5_checked, root5Node0Step4Chunk5_0_checked, root5Node0Step4Chunk5_1_checked, root5Node0Step4Chunk5_2_checked, root5Node0Step4Chunk5_3_checked, root5Node0Step4Chunk5_4_checked, root5Node0Step4Chunk5_5_checked, root5Node0Step4Chunk6_0_checked, root5Node0Step4Chunk6_1_checked, root5Node0Step4Chunk6_2_checked, root5Node0Step4Chunk6_3_checked, root5Node0Step4Chunk6_4_checked, root5Node0Step4Chunk6_5_checked, root5Node0Step4Chunk7_0_checked, root5Node0Step4Chunk7_1_checked, root5Node0Step4Chunk7_2_checked, root5Node0Step4Chunk7_3_checked, root5Node0Step4Chunk7_4_checked, root5Node0Step4Chunk7_5_checked, root5Node0Step4Chunk8_0_checked, root5Node0Step4Chunk8_1_checked, root5Node0Step4Chunk8_2_checked, root5Node0Step4Chunk8_3_checked, root5Node0Step4Chunk8_4_checked, root5Node0Step4Chunk8_5_checked, Bool.true_and])
theorem root5Node0Step4_checked :
    checkReplacement table12 root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq
    root5Node0Step4Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
