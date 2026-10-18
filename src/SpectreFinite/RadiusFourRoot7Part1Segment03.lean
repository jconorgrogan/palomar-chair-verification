module

public import SpectreFinite.RadiusFourRoot7Part1Segment02
public import SpectreFinite.RadiusFourRoot7Part0
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable1
public import SpectreFinite.RadiusFourTable20
public import SpectreFinite.RadiusFourTable31
public import SpectreFinite.RadiusFourTable46
public import SpectreFinite.RadiusFourTable7

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
theorem root7Node1Step2Chunk1_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_5⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk2_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_0⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk2_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_1⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk2_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_2⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk2_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_3⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk2_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_4⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk2_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_5⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk3_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_0⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk3_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_1⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk3_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_2⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk3_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_3⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk3_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_4⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk3_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_5⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk4_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_0⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk4_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_1⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk4_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_2⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk4_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_3⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk4_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_4⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk4_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_5⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk5_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_0⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk5_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_1⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk5_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_2⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk5_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_3⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk5_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_4⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk5_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_5⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFour
