module

public import SpectreFinite.RadiusFiveRoot1Part0Segment05
public import SpectreFinite.RadiusFiveRoot1Data
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
theorem root1Node0Step2Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Narrowing_checked :
    checkNarrowing table57 root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root1Node0Domains1 root1Node0Domains2 (by
      simp only [List.all_cons, List.all_nil, root1Node0Step2Chunk0_0_checked, root1Node0Step2Chunk0_1_checked, root1Node0Step2Chunk0_2_checked, root1Node0Step2Chunk0_3_checked, root1Node0Step2Chunk0_4_checked, root1Node0Step2Chunk0_5_checked, root1Node0Step2Chunk1_0_checked, root1Node0Step2Chunk1_1_checked, root1Node0Step2Chunk1_2_checked, root1Node0Step2Chunk1_3_checked, root1Node0Step2Chunk1_4_checked, root1Node0Step2Chunk1_5_checked, root1Node0Step2Chunk2_0_checked, root1Node0Step2Chunk2_1_checked, root1Node0Step2Chunk2_2_checked, root1Node0Step2Chunk2_3_checked, root1Node0Step2Chunk2_4_checked, root1Node0Step2Chunk2_5_checked, root1Node0Step2Chunk3_0_checked, root1Node0Step2Chunk3_1_checked, root1Node0Step2Chunk3_2_checked, root1Node0Step2Chunk3_3_checked, root1Node0Step2Chunk3_4_checked, root1Node0Step2Chunk3_5_checked, root1Node0Step2Chunk4_0_checked, root1Node0Step2Chunk4_1_checked, root1Node0Step2Chunk4_2_checked, root1Node0Step2Chunk4_3_checked, root1Node0Step2Chunk4_4_checked, root1Node0Step2Chunk4_5_checked, root1Node0Step2Chunk5_0_checked, root1Node0Step2Chunk5_1_checked, root1Node0Step2Chunk5_2_checked, root1Node0Step2Chunk5_3_checked, root1Node0Step2Chunk5_4_checked, root1Node0Step2Chunk5_5_checked, root1Node0Step2Chunk6_0_checked, root1Node0Step2Chunk6_1_checked, root1Node0Step2Chunk6_2_checked, root1Node0Step2Chunk6_3_checked, root1Node0Step2Chunk6_4_checked, root1Node0Step2Chunk6_5_checked, root1Node0Step2Chunk7_0_checked, root1Node0Step2Chunk7_1_checked, root1Node0Step2Chunk7_2_checked, root1Node0Step2Chunk7_3_checked, root1Node0Step2Chunk7_4_checked, root1Node0Step2Chunk7_5_checked, root1Node0Step2Chunk8_0_checked, root1Node0Step2Chunk8_1_checked, root1Node0Step2Chunk8_2_checked, root1Node0Step2Chunk8_3_checked, root1Node0Step2Chunk8_4_checked, root1Node0Step2Chunk8_5_checked, Bool.true_and])
theorem root1Node0Step2_checked :
    checkReplacement table57 root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq
    root1Node0Step2Narrowing_checked (by decide)
def root1Node0Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,0),(2,2),(4,0),(4,2),(8,2)]
  | 1 => [(3,3),(5,0),(5,3),(7,3),(8,0)]
  | 2 => [(4,5),(5,2),(5,5),(7,3),(8,2),(8,5)]
  | 3 => [(4,2),(7,0),(8,0)]
  | 4 => [(4,3),(5,3),(7,3),(8,3)]
  | 5 => stateChoices
  | 6 => [(0,4),(1,1),(3,1),(5,1),(6,2)]
  | 7 => [(0,1),(1,4),(3,4),(5,4),(7,4)]
  | 8 => [(0,0),(0,5),(6,2),(6,3),(6,4)]
  | 9 => [(1,2),(4,4),(7,2),(8,4)]
  | 10 => [(1,4),(6,4),(7,4)]
  | 11 => [(0,5),(1,2),(6,3)]
  | 12 => stateChoices
  | 13 => [(1,0),(3,0),(5,0),(5,3),(7,0),(8,3)]
  | 14 => [(2,1),(2,3),(2,5),(4,3),(4,5),(8,5)]
  | 15 => [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 16 => [(0,3),(1,1),(6,1),(7,1)]
  | 17 => [(4,1),(7,5)]
  | 18 => [(0,2),(0,3),(6,0)]
  | 19 => [(1,1),(3,1),(7,1),(8,1)]
  | 20 => [(0,1),(1,5),(4,1),(5,1),(6,5),(7,5),(8,1)]
  | 21 => [(4,4),(7,2),(7,4),(8,4)]
  | 22 => [(0,0),(1,4),(6,3),(6,4),(7,4)]
  | 23 => [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 24 => [(2,0),(2,2),(4,0)]
  | 25 => [(3,3),(7,3)]
  | 26 => [(4,2),(5,2),(8,2)]
  | 27 => [(5,0),(5,3),(8,0)]
  | 28 => [(4,5),(7,3),(8,3),(8,5)]
  | 29 => [(1,0),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 30 => [(1,1),(4,1),(7,1),(8,1)]
  | 31 => [(0,2),(1,5),(4,1),(7,5)]
  | 32 => [(0,2),(0,3),(1,1),(6,0),(6,1)]
  | 33 => [(1,1),(3,1),(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(7,4),(8,4)]
  | 37 => [(0,0),(1,4),(6,3),(6,4)]
  | 38 => [(0,5),(1,2),(7,2)]
  | 39 => [(4,0),(4,4),(7,4),(8,4)]
  | 40 => [(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(8,0)]
  | 41 => [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 42 => [(4,2),(5,2),(7,0),(8,0),(8,2)]
  | 43 => [(5,0),(5,3),(8,3)]
  | 44 => [(4,5),(5,5),(8,5)]
  | 45 => [(1,0)]
  | 46 => [(2,1),(7,1)]
  | 47 => [(0,2),(1,5),(7,5)]
  | 48 => [(0,3),(1,1),(6,0),(6,1)]
  | 49 => [(4,1),(5,1),(7,1),(8,1)]
  | 50 => [(0,1),(0,2),(1,5),(6,5),(7,5)]
  | 51 => [(0,0),(0,1),(0,4),(0,5),(6,2),(6,3),(6,4)]
  | 52 => [(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 53 => [(1,4),(7,4),(8,4)]
  | 54 => [(0,0),(0,5),(1,3),(6,3)]
  | 55 => [(4,4),(7,2),(8,2)]
  | 56 => [(0,0),(4,0),(5,0),(8,0)]
  | 57 => [(3,2),(4,5),(7,3)]
  | 58 => [(4,0),(4,2),(7,0),(8,2)]
  | 59 => [(5,0),(5,3),(7,3),(8,0),(8,3)]
  | 60 => [(4,5),(5,2),(7,3),(8,5)]
  | 61 => [(0,3),(1,0),(1,1),(4,3),(6,1),(7,1)]
  | 62 => [(4,1),(7,1),(7,5),(8,1)]
  | 63 => [(0,2),(1,5),(6,0),(6,5)]
  | 64 => [(0,4),(1,1),(6,1),(7,1)]
  | 65 => [(1,5),(5,1),(5,4)]
  | 66 => [(0,0),(0,1),(6,1),(6,4)]
  | 67 => [(1,2),(5,1),(6,2),(7,2)]
  | 68 => [(0,1),(7,4),(8,4)]
  | 69 => [(0,0),(6,2),(6,3),(6,4)]
  | 70 => [(1,3),(3,3),(5,0),(5,3),(7,3),(8,3)]
  | 71 => [(4,5),(5,2),(5,5),(8,2),(8,5)]
  | 72 => [(5,0),(7,0),(8,0)]
  | 73 => [(4,3),(4,5),(8,3)]
  | 74 => [(1,5),(3,5),(5,5),(7,0),(7,5),(8,5)]
  | 75 => [(0,3),(1,0),(6,1),(8,3)]
  | 76 => [(2,1),(4,1),(7,1),(8,1),(8,5)]
  | 77 => [(0,2),(1,0),(1,5),(7,5)]
  | 78 => [(0,0),(0,4),(0,5),(1,2),(6,2),(6,3)]
  | 79 => [(4,4),(5,4),(7,2),(8,4)]
  | 80 => [(0,0),(1,4),(7,4)]
  | 81 => [(0,5),(1,3),(6,3),(7,2)]
  | 82 => [(2,0),(2,2),(2,4),(4,2),(4,4),(7,2),(7,4),(8,2)]
  | 83 => [(0,0),(1,3),(3,3),(4,0),(5,0),(5,3),(6,3),(7,3),(8,0)]
  | 84 => [(3,2),(4,5),(5,2),(5,5),(7,2),(7,3),(8,2),(8,5)]
  | 85 => [(1,1),(4,3),(6,1),(7,1),(8,1)]
  | 86 => [(1,5),(4,1),(7,5),(8,1)]
  | 87 => [(0,2),(6,0),(6,1),(6,5)]
  | 88 => [(0,4),(1,1),(3,1),(4,1),(7,1),(8,1)]
  | 89 => [(0,1),(0,2),(1,4),(1,5),(3,4),(5,1),(5,4),(6,5)]
  | _ => [(0,0),(0,1),(0,4),(0,5),(1,1),(6,1),(6,2),(6,3),(6,4)]
def root1Node0Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,0),(2,2),(4,0),(4,2),(8,2)]
  | 1 => some [(3,3),(5,0),(5,3),(7,3),(8,0)]
  | 2 => some [(4,5),(5,2),(5,5),(7,3),(8,2),(8,5)]
  | 3 => some [(4,2),(7,0),(8,0)]
  | 4 => some [(4,3),(5,3),(7,3),(8,3)]
  | 5 => none
  | 6 => some [(0,4),(1,1),(3,1),(5,1),(6,2)]
  | 7 => some [(0,1),(1,4),(3,4),(5,4),(7,4)]
  | 8 => some [(0,0),(0,5),(6,2),(6,3),(6,4)]
  | 9 => some [(1,2),(4,4),(7,2),(8,4)]
  | 10 => some [(1,4),(6,4),(7,4)]
  | 11 => some [(0,5),(1,2),(6,3)]
  | 12 => none
  | 13 => some [(1,0),(3,0),(5,0),(5,3),(7,0),(8,3)]
  | 14 => some [(2,1),(2,3),(2,5),(4,3),(4,5),(8,5)]
  | 15 => some [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 16 => some [(0,3),(1,1),(6,1),(7,1)]
  | 17 => some [(4,1),(7,5)]
  | 18 => some [(0,2),(0,3),(6,0)]
  | 19 => some [(1,1),(3,1),(7,1),(8,1)]
  | 20 => some [(0,1),(1,5),(4,1),(5,1),(6,5),(7,5),(8,1)]
  | 21 => some [(4,4),(7,2),(7,4),(8,4)]
  | 22 => some [(0,0),(1,4),(6,3),(6,4),(7,4)]
  | 23 => some [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 24 => some [(2,0),(2,2),(4,0)]
  | 25 => some [(3,3),(7,3)]
  | 26 => some [(4,2),(5,2),(8,2)]
  | 27 => some [(5,0),(5,3),(8,0)]
  | 28 => some [(4,5),(7,3),(8,3),(8,5)]
  | 29 => some [(1,0),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 30 => some [(1,1),(4,1),(7,1),(8,1)]
  | 31 => some [(0,2),(1,5),(4,1),(7,5)]
  | 32 => some [(0,2),(0,3),(1,1),(6,0),(6,1)]
  | 33 => some [(1,1),(3,1),(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(7,4),(8,4)]
  | 37 => some [(0,0),(1,4),(6,3),(6,4)]
  | 38 => some [(0,5),(1,2),(7,2)]
  | 39 => some [(4,0),(4,4),(7,4),(8,4)]
  | 40 => some [(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(8,0)]
  | 41 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 42 => some [(4,2),(5,2),(7,0),(8,0),(8,2)]
  | 43 => some [(5,0),(5,3),(8,3)]
  | 44 => some [(4,5),(5,5),(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(2,1),(7,1)]
  | 47 => some [(0,2),(1,5),(7,5)]
  | 48 => some [(0,3),(1,1),(6,0),(6,1)]
  | 49 => some [(4,1),(5,1),(7,1),(8,1)]
  | 50 => some [(0,1),(0,2),(1,5),(6,5),(7,5)]
  | 51 => some [(0,0),(0,1),(0,4),(0,5),(6,2),(6,3),(6,4)]
  | 52 => some [(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 53 => some [(1,4),(7,4),(8,4)]
  | 54 => some [(0,0),(0,5),(1,3),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2)]
  | 56 => some [(0,0),(4,0),(5,0),(8,0)]
  | 57 => some [(3,2),(4,5),(7,3)]
  | 58 => some [(4,0),(4,2),(7,0),(8,2)]
  | 59 => some [(5,0),(5,3),(7,3),(8,0),(8,3)]
  | 60 => some [(4,5),(5,2),(7,3),(8,5)]
  | 61 => some [(0,3),(1,0),(1,1),(4,3),(6,1),(7,1)]
  | 62 => some [(4,1),(7,1),(7,5),(8,1)]
  | 63 => some [(0,2),(1,5),(6,0),(6,5)]
  | 64 => some [(0,4),(1,1),(6,1),(7,1)]
  | 65 => some [(1,5),(5,1),(5,4)]
  | 66 => some [(0,0),(0,1),(6,1),(6,4)]
  | 67 => some [(1,2),(5,1),(6,2),(7,2)]
  | 68 => some [(0,1),(7,4),(8,4)]
  | 69 => some [(0,0),(6,2),(6,3),(6,4)]
  | 70 => some [(1,3),(3,3),(5,0),(5,3),(7,3),(8,3)]
  | 71 => some [(4,5),(5,2),(5,5),(8,2),(8,5)]
  | 72 => some [(5,0),(7,0),(8,0)]
  | 73 => some [(4,3),(4,5),(8,3)]
  | 74 => some [(1,5),(3,5),(5,5),(7,0),(7,5),(8,5)]
  | 75 => some [(0,3),(1,0),(6,1),(8,3)]
  | 76 => some [(2,1),(4,1),(7,1),(8,1),(8,5)]
  | 77 => some [(0,2),(1,0),(1,5),(7,5)]
  | 78 => some [(0,0),(0,4),(0,5),(1,2),(6,2),(6,3)]
  | 79 => some [(4,4),(5,4),(7,2),(8,4)]
  | 80 => some [(0,0),(1,4),(7,4)]
  | 81 => some [(0,5),(1,3),(6,3),(7,2)]
  | 82 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(7,2),(7,4),(8,2)]
  | 83 => some [(0,0),(1,3),(3,3),(4,0),(5,0),(5,3),(6,3),(7,3),(8,0)]
  | 84 => some [(3,2),(4,5),(5,2),(5,5),(7,2),(7,3),(8,2),(8,5)]
  | 85 => some [(1,1),(4,3),(6,1),(7,1),(8,1)]
  | 86 => some [(1,5),(4,1),(7,5),(8,1)]
  | 87 => some [(0,2),(6,0),(6,1),(6,5)]
  | 88 => some [(0,4),(1,1),(3,1),(4,1),(7,1),(8,1)]
  | 89 => some [(0,1),(0,2),(1,4),(1,5),(3,4),(5,1),(5,4),(6,5)]
  | _ => some [(0,0),(0,1),(0,4),(0,5),(1,1),(6,1),(6,2),(6,3),(6,4)]
theorem root1Node0Domains3_fast_eq : root1Node0Domains3 = expandDomains root1Node0Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node0Domains3 v = expandDomains root1Node0Domains3Fast v from by decide) v
theorem root1Node0Step3Chunk0_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_0⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk0_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_1⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk0_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_2⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk0_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_3⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk0_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_4⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk0_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_5⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk1_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_0⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk1_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_1⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFive
