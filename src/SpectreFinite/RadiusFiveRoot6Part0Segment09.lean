module

public import SpectreFinite.RadiusFiveRoot6Part0Segment08
public import SpectreFinite.RadiusFiveRoot6Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable0
public import SpectreFinite.RadiusFiveTable35
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
theorem root6Node0Domains4_fast_eq : root6Node0Domains4 = expandDomains root6Node0Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node0Domains4 v = expandDomains root6Node0Domains4Fast v from by decide) v
theorem root6Node0Step4Chunk0_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_0⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk0_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_1⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk0_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_2⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk0_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_3⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk0_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_4⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk0_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_5⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk1_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_0⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk1_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_1⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk1_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_2⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk1_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_3⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk1_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_4⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk1_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_5⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk2_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_0⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk2_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_1⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk2_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_2⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk2_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_3⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk2_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_4⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk2_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_5⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk3_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_0⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk3_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_1⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk3_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_2⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk3_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_3⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk3_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_4⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk3_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_5⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFive
