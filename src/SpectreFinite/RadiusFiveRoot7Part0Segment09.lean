module

public import SpectreFinite.RadiusFiveRoot7Part0Segment08
public import SpectreFinite.RadiusFiveRoot7Data
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
theorem root7Node0Domains4_fast_eq : root7Node0Domains4 = expandDomains root7Node0Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node0Domains4 v = expandDomains root7Node0Domains4Fast v from by decide) v
theorem root7Node0Step4Chunk0_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_0⟩
      root7Node0Domains3 root7Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains3 root7Node0Domains4
    root7Node0Domains3Fast root7Node0Domains4Fast
    root7Node0Domains3_fast_eq root7Node0Domains4_fast_eq (by decide)
theorem root7Node0Step4Chunk0_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_1⟩
      root7Node0Domains3 root7Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains3 root7Node0Domains4
    root7Node0Domains3Fast root7Node0Domains4Fast
    root7Node0Domains3_fast_eq root7Node0Domains4_fast_eq (by decide)
theorem root7Node0Step4Chunk0_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_2⟩
      root7Node0Domains3 root7Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains3 root7Node0Domains4
    root7Node0Domains3Fast root7Node0Domains4Fast
    root7Node0Domains3_fast_eq root7Node0Domains4_fast_eq (by decide)
theorem root7Node0Step4Chunk0_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_3⟩
      root7Node0Domains3 root7Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains3 root7Node0Domains4
    root7Node0Domains3Fast root7Node0Domains4Fast
    root7Node0Domains3_fast_eq root7Node0Domains4_fast_eq (by decide)
theorem root7Node0Step4Chunk0_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_4⟩
      root7Node0Domains3 root7Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains3 root7Node0Domains4
    root7Node0Domains3Fast root7Node0Domains4Fast
    root7Node0Domains3_fast_eq root7Node0Domains4_fast_eq (by decide)
theorem root7Node0Step4Chunk0_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_5⟩
      root7Node0Domains3 root7Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains3 root7Node0Domains4
    root7Node0Domains3Fast root7Node0Domains4Fast
    root7Node0Domains3_fast_eq root7Node0Domains4_fast_eq (by decide)
theorem root7Node0Step4Chunk1_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_0⟩
      root7Node0Domains3 root7Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains3 root7Node0Domains4
    root7Node0Domains3Fast root7Node0Domains4Fast
    root7Node0Domains3_fast_eq root7Node0Domains4_fast_eq (by decide)
theorem root7Node0Step4Chunk1_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_1⟩
      root7Node0Domains3 root7Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains3 root7Node0Domains4
    root7Node0Domains3Fast root7Node0Domains4Fast
    root7Node0Domains3_fast_eq root7Node0Domains4_fast_eq (by decide)
theorem root7Node0Step4Chunk1_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_2⟩
      root7Node0Domains3 root7Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains3 root7Node0Domains4
    root7Node0Domains3Fast root7Node0Domains4Fast
    root7Node0Domains3_fast_eq root7Node0Domains4_fast_eq (by decide)
theorem root7Node0Step4Chunk1_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_3⟩
      root7Node0Domains3 root7Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains3 root7Node0Domains4
    root7Node0Domains3Fast root7Node0Domains4Fast
    root7Node0Domains3_fast_eq root7Node0Domains4_fast_eq (by decide)
theorem root7Node0Step4Chunk1_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_4⟩
      root7Node0Domains3 root7Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains3 root7Node0Domains4
    root7Node0Domains3Fast root7Node0Domains4Fast
    root7Node0Domains3_fast_eq root7Node0Domains4_fast_eq (by decide)
theorem root7Node0Step4Chunk1_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_5⟩
      root7Node0Domains3 root7Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains3 root7Node0Domains4
    root7Node0Domains3Fast root7Node0Domains4Fast
    root7Node0Domains3_fast_eq root7Node0Domains4_fast_eq (by decide)
theorem root7Node0Step4Chunk2_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_0⟩
      root7Node0Domains3 root7Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains3 root7Node0Domains4
    root7Node0Domains3Fast root7Node0Domains4Fast
    root7Node0Domains3_fast_eq root7Node0Domains4_fast_eq (by decide)
theorem root7Node0Step4Chunk2_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_1⟩
      root7Node0Domains3 root7Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains3 root7Node0Domains4
    root7Node0Domains3Fast root7Node0Domains4Fast
    root7Node0Domains3_fast_eq root7Node0Domains4_fast_eq (by decide)
theorem root7Node0Step4Chunk2_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_2⟩
      root7Node0Domains3 root7Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains3 root7Node0Domains4
    root7Node0Domains3Fast root7Node0Domains4Fast
    root7Node0Domains3_fast_eq root7Node0Domains4_fast_eq (by decide)
theorem root7Node0Step4Chunk2_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_3⟩
      root7Node0Domains3 root7Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains3 root7Node0Domains4
    root7Node0Domains3Fast root7Node0Domains4Fast
    root7Node0Domains3_fast_eq root7Node0Domains4_fast_eq (by decide)
theorem root7Node0Step4Chunk2_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_4⟩
      root7Node0Domains3 root7Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains3 root7Node0Domains4
    root7Node0Domains3Fast root7Node0Domains4Fast
    root7Node0Domains3_fast_eq root7Node0Domains4_fast_eq (by decide)
theorem root7Node0Step4Chunk2_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_5⟩
      root7Node0Domains3 root7Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains3 root7Node0Domains4
    root7Node0Domains3Fast root7Node0Domains4Fast
    root7Node0Domains3_fast_eq root7Node0Domains4_fast_eq (by decide)
theorem root7Node0Step4Chunk3_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_0⟩
      root7Node0Domains3 root7Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains3 root7Node0Domains4
    root7Node0Domains3Fast root7Node0Domains4Fast
    root7Node0Domains3_fast_eq root7Node0Domains4_fast_eq (by decide)
theorem root7Node0Step4Chunk3_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_1⟩
      root7Node0Domains3 root7Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains3 root7Node0Domains4
    root7Node0Domains3Fast root7Node0Domains4Fast
    root7Node0Domains3_fast_eq root7Node0Domains4_fast_eq (by decide)
theorem root7Node0Step4Chunk3_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_2⟩
      root7Node0Domains3 root7Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains3 root7Node0Domains4
    root7Node0Domains3Fast root7Node0Domains4Fast
    root7Node0Domains3_fast_eq root7Node0Domains4_fast_eq (by decide)
theorem root7Node0Step4Chunk3_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_3⟩
      root7Node0Domains3 root7Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains3 root7Node0Domains4
    root7Node0Domains3Fast root7Node0Domains4Fast
    root7Node0Domains3_fast_eq root7Node0Domains4_fast_eq (by decide)
theorem root7Node0Step4Chunk3_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_4⟩
      root7Node0Domains3 root7Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains3 root7Node0Domains4
    root7Node0Domains3Fast root7Node0Domains4Fast
    root7Node0Domains3_fast_eq root7Node0Domains4_fast_eq (by decide)
theorem root7Node0Step4Chunk3_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_5⟩
      root7Node0Domains3 root7Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains3 root7Node0Domains4
    root7Node0Domains3Fast root7Node0Domains4Fast
    root7Node0Domains3_fast_eq root7Node0Domains4_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFive
