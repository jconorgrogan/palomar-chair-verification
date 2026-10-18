module

public import SpectreFinite.RadiusFiveRoot5Part0Segment04
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
theorem root5Node0Step2Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFive
