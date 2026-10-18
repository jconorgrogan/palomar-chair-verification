module

public import SpectreFinite.RadiusFiveRoot5Part0Segment08
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
theorem root5Node0Domains4_fast_eq : root5Node0Domains4 = expandDomains root5Node0Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node0Domains4 v = expandDomains root5Node0Domains4Fast v from by decide) v
theorem root5Node0Step4Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFive
