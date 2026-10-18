module

public import SpectreFinite.RadiusFiveRoot0Part2Segment02
public import SpectreFinite.RadiusFiveRoot0Part1
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable2
public import SpectreFinite.RadiusFiveTable46
public import SpectreFinite.RadiusFiveTable65
public import SpectreFinite.RadiusFiveTable8

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
theorem root0Node2Step1Chunk1_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_4⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk1_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_5⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk2_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_0⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk2_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_1⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk2_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_2⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk2_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_3⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk2_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_4⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk2_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_5⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk3_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_0⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk3_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_1⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk3_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_2⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk3_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_3⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk3_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_4⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk3_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_5⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk4_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_0⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk4_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_1⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk4_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_2⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk4_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_3⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk4_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_4⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk4_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_5⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk5_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_0⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk5_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_1⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk5_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_2⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk5_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_3⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk5_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_4⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFive
