module

public import SpectreFinite.RadiusFiveRoot0Part1Segment08
public import SpectreFinite.RadiusFiveRoot0Part0
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable34
public import SpectreFinite.RadiusFiveTable52
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
theorem root0Node1Step3Chunk7_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_0⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk7_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_1⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk7_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_2⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk7_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_3⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk7_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_4⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk7_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_5⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk8_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_0⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk8_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_1⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk8_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_2⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk8_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_3⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk8_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_4⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk8_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_5⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Narrowing_checked :
    checkNarrowing table52 root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_flatten table52Scope [table52Rows0_0,table52Rows0_1,table52Rows0_2,table52Rows0_3,table52Rows0_4,table52Rows0_5,table52Rows1_0,table52Rows1_1,table52Rows1_2,table52Rows1_3,table52Rows1_4,table52Rows1_5,table52Rows2_0,table52Rows2_1,table52Rows2_2,table52Rows2_3,table52Rows2_4,table52Rows2_5,table52Rows3_0,table52Rows3_1,table52Rows3_2,table52Rows3_3,table52Rows3_4,table52Rows3_5,table52Rows4_0,table52Rows4_1,table52Rows4_2,table52Rows4_3,table52Rows4_4,table52Rows4_5,table52Rows5_0,table52Rows5_1,table52Rows5_2,table52Rows5_3,table52Rows5_4,table52Rows5_5,table52Rows6_0,table52Rows6_1,table52Rows6_2,table52Rows6_3,table52Rows6_4,table52Rows6_5,table52Rows7_0,table52Rows7_1,table52Rows7_2,table52Rows7_3,table52Rows7_4,table52Rows7_5,table52Rows8_0,table52Rows8_1,table52Rows8_2,table52Rows8_3,table52Rows8_4,table52Rows8_5]
    root0Node1Domains2 root0Node1Domains3 (by
      simp only [List.all_cons, List.all_nil, root0Node1Step3Chunk0_0_checked, root0Node1Step3Chunk0_1_checked, root0Node1Step3Chunk0_2_checked, root0Node1Step3Chunk0_3_checked, root0Node1Step3Chunk0_4_checked, root0Node1Step3Chunk0_5_checked, root0Node1Step3Chunk1_0_checked, root0Node1Step3Chunk1_1_checked, root0Node1Step3Chunk1_2_checked, root0Node1Step3Chunk1_3_checked, root0Node1Step3Chunk1_4_checked, root0Node1Step3Chunk1_5_checked, root0Node1Step3Chunk2_0_checked, root0Node1Step3Chunk2_1_checked, root0Node1Step3Chunk2_2_checked, root0Node1Step3Chunk2_3_checked, root0Node1Step3Chunk2_4_checked, root0Node1Step3Chunk2_5_checked, root0Node1Step3Chunk3_0_checked, root0Node1Step3Chunk3_1_checked, root0Node1Step3Chunk3_2_checked, root0Node1Step3Chunk3_3_checked, root0Node1Step3Chunk3_4_checked, root0Node1Step3Chunk3_5_checked, root0Node1Step3Chunk4_0_checked, root0Node1Step3Chunk4_1_checked, root0Node1Step3Chunk4_2_checked, root0Node1Step3Chunk4_3_checked, root0Node1Step3Chunk4_4_checked, root0Node1Step3Chunk4_5_checked, root0Node1Step3Chunk5_0_checked, root0Node1Step3Chunk5_1_checked, root0Node1Step3Chunk5_2_checked, root0Node1Step3Chunk5_3_checked, root0Node1Step3Chunk5_4_checked, root0Node1Step3Chunk5_5_checked, root0Node1Step3Chunk6_0_checked, root0Node1Step3Chunk6_1_checked, root0Node1Step3Chunk6_2_checked, root0Node1Step3Chunk6_3_checked, root0Node1Step3Chunk6_4_checked, root0Node1Step3Chunk6_5_checked, root0Node1Step3Chunk7_0_checked, root0Node1Step3Chunk7_1_checked, root0Node1Step3Chunk7_2_checked, root0Node1Step3Chunk7_3_checked, root0Node1Step3Chunk7_4_checked, root0Node1Step3Chunk7_5_checked, root0Node1Step3Chunk8_0_checked, root0Node1Step3Chunk8_1_checked, root0Node1Step3Chunk8_2_checked, root0Node1Step3Chunk8_3_checked, root0Node1Step3Chunk8_4_checked, root0Node1Step3Chunk8_5_checked, Bool.true_and])
theorem root0Node1Step3_checked :
    checkReplacement table52 root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq
    root0Node1Step3Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
