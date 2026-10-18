module

public import SpectreFinite.RadiusFiveRoot0Part1Segment02
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
theorem root0Node1Step1Chunk1_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_4⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk1_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_5⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk2_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_0⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk2_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_1⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk2_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_2⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk2_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_3⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk2_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_4⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk2_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_5⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk3_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_0⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk3_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_1⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk3_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_2⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk3_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_3⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk3_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_4⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk3_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_5⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk4_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_0⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk4_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_1⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk4_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_2⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk4_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_3⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk4_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_4⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk4_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_5⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk5_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_0⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk5_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_1⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk5_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_2⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk5_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_3⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk5_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_4⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFive
