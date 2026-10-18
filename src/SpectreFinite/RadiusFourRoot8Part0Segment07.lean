module

public import SpectreFinite.RadiusFourRoot8Part0Segment06
public import SpectreFinite.RadiusFourRoot8Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable11
public import SpectreFinite.RadiusFourTable14
public import SpectreFinite.RadiusFourTable16
public import SpectreFinite.RadiusFourTable30
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
theorem root8Node0Step3Chunk8_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_5⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3_checked :
    checkReplacement table14 root8Node0Domains2 root8Node0Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node0Step3Chunk0_0_checked, root8Node0Step3Chunk0_1_checked, root8Node0Step3Chunk0_2_checked, root8Node0Step3Chunk0_3_checked, root8Node0Step3Chunk0_4_checked, root8Node0Step3Chunk0_5_checked, root8Node0Step3Chunk1_0_checked, root8Node0Step3Chunk1_1_checked, root8Node0Step3Chunk1_2_checked, root8Node0Step3Chunk1_3_checked, root8Node0Step3Chunk1_4_checked, root8Node0Step3Chunk1_5_checked, root8Node0Step3Chunk2_0_checked, root8Node0Step3Chunk2_1_checked, root8Node0Step3Chunk2_2_checked, root8Node0Step3Chunk2_3_checked, root8Node0Step3Chunk2_4_checked, root8Node0Step3Chunk2_5_checked, root8Node0Step3Chunk3_0_checked, root8Node0Step3Chunk3_1_checked, root8Node0Step3Chunk3_2_checked, root8Node0Step3Chunk3_3_checked, root8Node0Step3Chunk3_4_checked, root8Node0Step3Chunk3_5_checked, root8Node0Step3Chunk4_0_checked, root8Node0Step3Chunk4_1_checked, root8Node0Step3Chunk4_2_checked, root8Node0Step3Chunk4_3_checked, root8Node0Step3Chunk4_4_checked, root8Node0Step3Chunk4_5_checked, root8Node0Step3Chunk5_0_checked, root8Node0Step3Chunk5_1_checked, root8Node0Step3Chunk5_2_checked, root8Node0Step3Chunk5_3_checked, root8Node0Step3Chunk5_4_checked, root8Node0Step3Chunk5_5_checked, root8Node0Step3Chunk6_0_checked, root8Node0Step3Chunk6_1_checked, root8Node0Step3Chunk6_2_checked, root8Node0Step3Chunk6_3_checked, root8Node0Step3Chunk6_4_checked, root8Node0Step3Chunk6_5_checked, root8Node0Step3Chunk7_0_checked, root8Node0Step3Chunk7_1_checked, root8Node0Step3Chunk7_2_checked, root8Node0Step3Chunk7_3_checked, root8Node0Step3Chunk7_4_checked, root8Node0Step3Chunk7_5_checked, root8Node0Step3Chunk8_0_checked, root8Node0Step3Chunk8_1_checked, root8Node0Step3Chunk8_2_checked, root8Node0Step3Chunk8_3_checked, root8Node0Step3Chunk8_4_checked, root8Node0Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node0Domains4 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 1 => [(0,3),(1,1),(6,1),(7,1)]
  | 2 => [(4,1),(5,1),(7,5),(8,1)]
  | 3 => [(0,1),(0,2),(1,5),(6,0),(6,5)]
  | 4 => [(0,4),(1,1),(6,1),(6,2),(7,1)]
  | 5 => [(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(7,3),(8,5)]
  | 6 => [(4,0),(4,2),(7,0),(8,0)]
  | 7 => [(5,3),(7,3),(8,3)]
  | 8 => [(5,2),(5,5),(8,2),(8,5)]
  | 9 => [(1,0),(7,0),(8,0)]
  | 10 => [(2,3),(4,3),(7,1),(7,3),(8,3)]
  | 11 => [(0,0),(0,3),(0,4),(0,5),(6,1),(6,2),(6,3),(6,4)]
  | 12 => [(1,2),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 13 => [(0,1),(1,4),(7,4)]
  | 14 => [(0,5),(6,2),(6,3)]
  | 15 => [(4,4),(7,2),(8,4)]
  | 16 => [(1,4),(4,0),(6,4),(7,4)]
  | 17 => [(0,5),(1,2),(1,3),(6,3),(7,3)]
  | 18 => [(0,2),(1,0),(1,5),(3,5),(4,2),(6,0),(7,0),(7,5)]
  | 19 => [(0,3),(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 20 => [(4,1),(7,5),(8,5)]
  | 21 => [(0,2),(1,0),(6,0)]
  | 22 => [(1,1),(7,1)]
  | 23 => [(4,1),(5,1),(7,5),(8,1)]
  | 24 => [(0,1),(0,2),(0,3),(6,0),(6,5)]
  | 25 => stateChoices
  | 26 => [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 27 => [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 28 => [(1,3),(3,3),(7,3)]
  | 29 => [(5,2),(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3),(8,3)]
  | 32 => [(4,2),(5,2),(5,5),(8,2)]
  | 33 => [(1,0),(3,0),(5,0),(5,3),(7,0)]
  | 34 => stateChoices
  | 35 => [(1,1),(3,1),(5,1),(7,1),(8,1)]
  | 36 => [(0,1),(6,5)]
  | 37 => [(0,4),(6,2)]
  | 38 => [(5,4),(8,4)]
  | 39 => [(1,4),(6,4)]
  | 40 => [(0,5),(1,2)]
  | 41 => [(4,4),(7,4),(8,4)]
  | 42 => stateChoices
  | 43 => [(4,5),(5,5),(8,5)]
  | 44 => [(1,0),(7,0)]
  | 45 => [(4,3),(7,1)]
  | 46 => [(3,5),(7,5)]
  | 47 => [(0,3),(6,0)]
  | 48 => [(4,1),(7,1),(8,1)]
  | 49 => [(0,2),(1,5),(6,5),(7,5)]
  | 50 => [(4,4),(7,2),(8,2)]
  | 51 => [(1,4),(4,0),(7,4),(8,0)]
  | 52 => [(0,5),(1,3),(6,3),(7,3)]
  | 53 => [(2,2),(2,4),(4,2),(8,2)]
  | 54 => [(1,3),(3,3),(5,0),(5,3),(8,0)]
  | 55 => [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 56 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 57 => [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 58 => [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 59 => [(0,1),(1,4),(3,4),(5,4),(6,5),(7,4),(8,4)]
  | _ => [(0,0),(0,4),(0,5),(6,2),(6,3),(6,4)]
def root8Node0Domains4Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 1 => some [(0,3),(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(5,1),(7,5),(8,1)]
  | 3 => some [(0,1),(0,2),(1,5),(6,0),(6,5)]
  | 4 => some [(0,4),(1,1),(6,1),(6,2),(7,1)]
  | 5 => some [(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(7,3),(8,5)]
  | 6 => some [(4,0),(4,2),(7,0),(8,0)]
  | 7 => some [(5,3),(7,3),(8,3)]
  | 8 => some [(5,2),(5,5),(8,2),(8,5)]
  | 9 => some [(1,0),(7,0),(8,0)]
  | 10 => some [(2,3),(4,3),(7,1),(7,3),(8,3)]
  | 11 => some [(0,0),(0,3),(0,4),(0,5),(6,1),(6,2),(6,3),(6,4)]
  | 12 => some [(1,2),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 13 => some [(0,1),(1,4),(7,4)]
  | 14 => some [(0,5),(6,2),(6,3)]
  | 15 => some [(4,4),(7,2),(8,4)]
  | 16 => some [(1,4),(4,0),(6,4),(7,4)]
  | 17 => some [(0,5),(1,2),(1,3),(6,3),(7,3)]
  | 18 => some [(0,2),(1,0),(1,5),(3,5),(4,2),(6,0),(7,0),(7,5)]
  | 19 => some [(0,3),(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 20 => some [(4,1),(7,5),(8,5)]
  | 21 => some [(0,2),(1,0),(6,0)]
  | 22 => some [(1,1),(7,1)]
  | 23 => some [(4,1),(5,1),(7,5),(8,1)]
  | 24 => some [(0,1),(0,2),(0,3),(6,0),(6,5)]
  | 25 => none
  | 26 => some [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 27 => some [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 28 => some [(1,3),(3,3),(7,3)]
  | 29 => some [(5,2),(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(4,2),(5,2),(5,5),(8,2)]
  | 33 => some [(1,0),(3,0),(5,0),(5,3),(7,0)]
  | 34 => none
  | 35 => some [(1,1),(3,1),(5,1),(7,1),(8,1)]
  | 36 => some [(0,1),(6,5)]
  | 37 => some [(0,4),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(0,5),(1,2)]
  | 41 => some [(4,4),(7,4),(8,4)]
  | 42 => none
  | 43 => some [(4,5),(5,5),(8,5)]
  | 44 => some [(1,0),(7,0)]
  | 45 => some [(4,3),(7,1)]
  | 46 => some [(3,5),(7,5)]
  | 47 => some [(0,3),(6,0)]
  | 48 => some [(4,1),(7,1),(8,1)]
  | 49 => some [(0,2),(1,5),(6,5),(7,5)]
  | 50 => some [(4,4),(7,2),(8,2)]
  | 51 => some [(1,4),(4,0),(7,4),(8,0)]
  | 52 => some [(0,5),(1,3),(6,3),(7,3)]
  | 53 => some [(2,2),(2,4),(4,2),(8,2)]
  | 54 => some [(1,3),(3,3),(5,0),(5,3),(8,0)]
  | 55 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 56 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 57 => some [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 58 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 59 => some [(0,1),(1,4),(3,4),(5,4),(6,5),(7,4),(8,4)]
  | _ => some [(0,0),(0,4),(0,5),(6,2),(6,3),(6,4)]
theorem root8Node0Domains4_fast_eq : root8Node0Domains4 = expandDomains root8Node0Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node0Domains4 v = expandDomains root8Node0Domains4Fast v from by decide) v
theorem root8Node0Step4Chunk0_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_0⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk0_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_1⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk0_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_2⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk0_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_3⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk0_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_4⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk0_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_5⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk1_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_0⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk1_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_1⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk1_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_2⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk1_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_3⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk1_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_4⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk1_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_5⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk2_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_0⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk2_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_1⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk2_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_2⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk2_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_3⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk2_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_4⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk2_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_5⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk3_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_0⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk3_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_1⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFour
