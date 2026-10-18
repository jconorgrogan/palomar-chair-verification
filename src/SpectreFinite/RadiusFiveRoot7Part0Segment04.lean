module

public import SpectreFinite.RadiusFiveRoot7Part0Segment03
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
theorem root7Node0Step1Chunk8_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_3⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Chunk8_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_4⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Chunk8_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_5⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Narrowing_checked :
    checkNarrowing table34 root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_flatten table34Scope [table34Rows0_0,table34Rows0_1,table34Rows0_2,table34Rows0_3,table34Rows0_4,table34Rows0_5,table34Rows1_0,table34Rows1_1,table34Rows1_2,table34Rows1_3,table34Rows1_4,table34Rows1_5,table34Rows2_0,table34Rows2_1,table34Rows2_2,table34Rows2_3,table34Rows2_4,table34Rows2_5,table34Rows3_0,table34Rows3_1,table34Rows3_2,table34Rows3_3,table34Rows3_4,table34Rows3_5,table34Rows4_0,table34Rows4_1,table34Rows4_2,table34Rows4_3,table34Rows4_4,table34Rows4_5,table34Rows5_0,table34Rows5_1,table34Rows5_2,table34Rows5_3,table34Rows5_4,table34Rows5_5,table34Rows6_0,table34Rows6_1,table34Rows6_2,table34Rows6_3,table34Rows6_4,table34Rows6_5,table34Rows7_0,table34Rows7_1,table34Rows7_2,table34Rows7_3,table34Rows7_4,table34Rows7_5,table34Rows8_0,table34Rows8_1,table34Rows8_2,table34Rows8_3,table34Rows8_4,table34Rows8_5]
    root7Node0Domains0 root7Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node0Step1Chunk0_0_checked, root7Node0Step1Chunk0_1_checked, root7Node0Step1Chunk0_2_checked, root7Node0Step1Chunk0_3_checked, root7Node0Step1Chunk0_4_checked, root7Node0Step1Chunk0_5_checked, root7Node0Step1Chunk1_0_checked, root7Node0Step1Chunk1_1_checked, root7Node0Step1Chunk1_2_checked, root7Node0Step1Chunk1_3_checked, root7Node0Step1Chunk1_4_checked, root7Node0Step1Chunk1_5_checked, root7Node0Step1Chunk2_0_checked, root7Node0Step1Chunk2_1_checked, root7Node0Step1Chunk2_2_checked, root7Node0Step1Chunk2_3_checked, root7Node0Step1Chunk2_4_checked, root7Node0Step1Chunk2_5_checked, root7Node0Step1Chunk3_0_checked, root7Node0Step1Chunk3_1_checked, root7Node0Step1Chunk3_2_checked, root7Node0Step1Chunk3_3_checked, root7Node0Step1Chunk3_4_checked, root7Node0Step1Chunk3_5_checked, root7Node0Step1Chunk4_0_checked, root7Node0Step1Chunk4_1_checked, root7Node0Step1Chunk4_2_checked, root7Node0Step1Chunk4_3_checked, root7Node0Step1Chunk4_4_checked, root7Node0Step1Chunk4_5_checked, root7Node0Step1Chunk5_0_checked, root7Node0Step1Chunk5_1_checked, root7Node0Step1Chunk5_2_checked, root7Node0Step1Chunk5_3_checked, root7Node0Step1Chunk5_4_checked, root7Node0Step1Chunk5_5_checked, root7Node0Step1Chunk6_0_checked, root7Node0Step1Chunk6_1_checked, root7Node0Step1Chunk6_2_checked, root7Node0Step1Chunk6_3_checked, root7Node0Step1Chunk6_4_checked, root7Node0Step1Chunk6_5_checked, root7Node0Step1Chunk7_0_checked, root7Node0Step1Chunk7_1_checked, root7Node0Step1Chunk7_2_checked, root7Node0Step1Chunk7_3_checked, root7Node0Step1Chunk7_4_checked, root7Node0Step1Chunk7_5_checked, root7Node0Step1Chunk8_0_checked, root7Node0Step1Chunk8_1_checked, root7Node0Step1Chunk8_2_checked, root7Node0Step1Chunk8_3_checked, root7Node0Step1Chunk8_4_checked, root7Node0Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node0Step1_checked :
    checkReplacement table34 root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq
    root7Node0Step1Narrowing_checked (by decide)
def root7Node0Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,4),(4,4),(7,2),(7,4),(8,2),(8,4)]
  | 1 => [(0,0),(1,3),(1,4),(4,0),(6,4),(7,4),(8,0)]
  | 2 => [(0,5),(1,2),(1,3),(3,2),(5,2),(6,3),(7,2),(7,3),(8,2)]
  | 3 => [(2,0),(2,2),(2,4),(4,0),(4,2),(4,4),(8,0)]
  | 4 => [(0,0),(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 5 => stateChoices
  | 6 => [(0,4),(1,1),(6,1),(7,1),(8,1)]
  | 7 => [(1,5),(4,1),(5,1),(5,4),(6,5),(7,5),(8,1)]
  | 8 => [(0,1),(0,2),(0,3),(0,4),(6,0),(6,1),(6,4),(6,5)]
  | 9 => [(0,4),(1,1),(1,2),(3,1),(5,1),(5,4),(6,2),(7,1)]
  | 10 => [(0,1),(1,4),(1,5),(6,4),(6,5),(7,4)]
  | 11 => [(0,4),(0,5),(1,2),(6,1),(6,2),(6,3)]
  | 12 => stateChoices
  | 13 => [(4,0),(5,0),(5,3),(7,0),(8,0),(8,3)]
  | 14 => [(4,3),(4,5),(7,3),(8,3),(8,5)]
  | 15 => [(3,5),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 16 => [(0,3),(1,0),(3,0),(4,3),(5,0),(5,3),(8,3)]
  | 17 => [(2,1),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 18 => [(0,2),(0,3),(1,0),(6,0),(7,0)]
  | 19 => [(1,1),(4,3),(7,1),(8,1),(8,3)]
  | 20 => [(1,5),(4,1),(5,1),(6,5),(7,5),(8,1),(8,5)]
  | 21 => [(4,4),(5,1),(5,4),(7,4),(8,4)]
  | 22 => [(0,0),(0,1),(1,4),(6,3),(6,4)]
  | 23 => [(0,5),(1,2),(6,2),(7,2)]
  | 24 => [(2,4),(4,4),(7,4),(8,4)]
  | 25 => [(0,0),(1,3)]
  | 26 => [(3,2),(4,2),(5,2),(7,2),(8,2)]
  | 27 => [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 28 => [(1,3),(4,5),(7,3),(8,3),(8,5)]
  | 29 => [(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 30 => [(4,1),(4,3),(5,3),(7,1),(8,1),(8,3)]
  | 31 => [(0,2),(1,5),(7,5),(8,5)]
  | 32 => [(0,3),(1,0),(1,1),(6,0),(6,1)]
  | 33 => [(7,1),(8,1)]
  | 34 => [(1,5),(6,5)]
  | 35 => [(0,4),(6,1)]
  | 36 => [(3,4),(5,1),(5,4),(8,1)]
  | 37 => [(0,0),(0,1),(1,4),(6,3),(6,4),(6,5)]
  | 38 => [(0,4),(0,5),(1,2),(6,2),(7,2)]
  | 39 => [(1,4),(3,4),(4,4),(5,4),(7,4),(8,4)]
  | 40 => stateChoices
  | 41 => [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 42 => [(4,2),(7,0),(8,0),(8,2)]
  | 43 => [(5,0),(5,3),(8,3)]
  | 44 => [(4,5),(5,5),(8,5)]
  | 45 => [(7,0)]
  | 46 => [(2,3),(4,3),(8,3)]
  | 47 => [(0,2),(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 48 => [(0,3),(1,0),(1,1),(3,0),(6,0),(6,1),(7,0)]
  | 49 => [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(8,1)]
  | 50 => [(0,2),(1,5),(3,5),(6,0),(6,5),(7,5)]
  | 51 => stateChoices
  | 52 => [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 53 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 54 => [(0,0),(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,4),(6,4),(7,4)]
  | 57 => [(0,5),(1,2),(1,3),(6,3)]
  | 58 => [(2,0),(2,2),(2,4),(4,0),(4,2),(4,4),(7,2),(8,2)]
  | 59 => [(0,0),(1,3),(1,4),(3,3),(4,0),(5,0),(5,3),(6,4),(7,3),(7,4),(8,0)]
  | 60 => [(0,5),(1,2),(1,3),(3,2),(4,5),(5,2),(5,5),(6,3),(7,2),(7,3),(8,5)]
  | 61 => stateChoices
  | 62 => [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(7,5),(8,1)]
  | 63 => [(0,2),(1,5),(6,0)]
  | 64 => [(1,1),(6,1),(7,1)]
  | 65 => [(4,1),(7,5),(8,1)]
  | 66 => [(0,2),(0,3),(6,0),(6,5)]
  | 67 => [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 68 => [(0,1),(1,4),(1,5),(3,4),(4,1),(5,1),(5,4),(6,5),(7,5),(8,1)]
  | 69 => [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5)]
  | 70 => stateChoices
  | 71 => [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 72 => [(2,0),(4,0),(7,0),(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | 75 => [(3,0),(5,0),(5,3),(7,0),(8,0)]
  | 76 => [(2,3),(2,5),(4,3),(4,5),(7,3),(8,3),(8,5)]
  | 77 => [(0,2),(1,0),(1,5),(3,5),(4,2),(5,2),(5,5),(6,0),(7,0),(7,5),(8,2)]
  | 78 => stateChoices
  | 79 => stateChoices
  | 80 => [(0,1),(1,4),(6,4),(7,4)]
  | 81 => [(0,5),(1,2),(6,2),(6,3)]
  | 82 => [(4,4),(7,2),(7,4),(8,4)]
  | 83 => [(0,0),(1,3),(1,4),(6,3),(6,4),(7,4)]
  | 84 => [(0,5),(1,2),(1,3),(6,3),(7,2),(8,2)]
  | 85 => stateChoices
  | 86 => stateChoices
  | 87 => [(0,2),(0,3),(1,0),(6,0)]
  | 88 => [(1,1),(4,1),(7,1),(8,1)]
  | 89 => [(0,2),(1,5),(4,1),(6,5),(7,5),(8,1)]
  | _ => [(0,2),(0,3),(0,4),(1,1),(6,0),(6,1),(6,5)]
def root7Node0Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4),(4,4),(7,2),(7,4),(8,2),(8,4)]
  | 1 => some [(0,0),(1,3),(1,4),(4,0),(6,4),(7,4),(8,0)]
  | 2 => some [(0,5),(1,2),(1,3),(3,2),(5,2),(6,3),(7,2),(7,3),(8,2)]
  | 3 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(4,4),(8,0)]
  | 4 => some [(0,0),(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 5 => none
  | 6 => some [(0,4),(1,1),(6,1),(7,1),(8,1)]
  | 7 => some [(1,5),(4,1),(5,1),(5,4),(6,5),(7,5),(8,1)]
  | 8 => some [(0,1),(0,2),(0,3),(0,4),(6,0),(6,1),(6,4),(6,5)]
  | 9 => some [(0,4),(1,1),(1,2),(3,1),(5,1),(5,4),(6,2),(7,1)]
  | 10 => some [(0,1),(1,4),(1,5),(6,4),(6,5),(7,4)]
  | 11 => some [(0,4),(0,5),(1,2),(6,1),(6,2),(6,3)]
  | 12 => none
  | 13 => some [(4,0),(5,0),(5,3),(7,0),(8,0),(8,3)]
  | 14 => some [(4,3),(4,5),(7,3),(8,3),(8,5)]
  | 15 => some [(3,5),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 16 => some [(0,3),(1,0),(3,0),(4,3),(5,0),(5,3),(8,3)]
  | 17 => some [(2,1),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 18 => some [(0,2),(0,3),(1,0),(6,0),(7,0)]
  | 19 => some [(1,1),(4,3),(7,1),(8,1),(8,3)]
  | 20 => some [(1,5),(4,1),(5,1),(6,5),(7,5),(8,1),(8,5)]
  | 21 => some [(4,4),(5,1),(5,4),(7,4),(8,4)]
  | 22 => some [(0,0),(0,1),(1,4),(6,3),(6,4)]
  | 23 => some [(0,5),(1,2),(6,2),(7,2)]
  | 24 => some [(2,4),(4,4),(7,4),(8,4)]
  | 25 => some [(0,0),(1,3)]
  | 26 => some [(3,2),(4,2),(5,2),(7,2),(8,2)]
  | 27 => some [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 28 => some [(1,3),(4,5),(7,3),(8,3),(8,5)]
  | 29 => some [(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 30 => some [(4,1),(4,3),(5,3),(7,1),(8,1),(8,3)]
  | 31 => some [(0,2),(1,5),(7,5),(8,5)]
  | 32 => some [(0,3),(1,0),(1,1),(6,0),(6,1)]
  | 33 => some [(7,1),(8,1)]
  | 34 => some [(1,5),(6,5)]
  | 35 => some [(0,4),(6,1)]
  | 36 => some [(3,4),(5,1),(5,4),(8,1)]
  | 37 => some [(0,0),(0,1),(1,4),(6,3),(6,4),(6,5)]
  | 38 => some [(0,4),(0,5),(1,2),(6,2),(7,2)]
  | 39 => some [(1,4),(3,4),(4,4),(5,4),(7,4),(8,4)]
  | 40 => none
  | 41 => some [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 42 => some [(4,2),(7,0),(8,0),(8,2)]
  | 43 => some [(5,0),(5,3),(8,3)]
  | 44 => some [(4,5),(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(2,3),(4,3),(8,3)]
  | 47 => some [(0,2),(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 48 => some [(0,3),(1,0),(1,1),(3,0),(6,0),(6,1),(7,0)]
  | 49 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(8,1)]
  | 50 => some [(0,2),(1,5),(3,5),(6,0),(6,5),(7,5)]
  | 51 => none
  | 52 => some [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 53 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 54 => some [(0,0),(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(6,4),(7,4)]
  | 57 => some [(0,5),(1,2),(1,3),(6,3)]
  | 58 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(4,4),(7,2),(8,2)]
  | 59 => some [(0,0),(1,3),(1,4),(3,3),(4,0),(5,0),(5,3),(6,4),(7,3),(7,4),(8,0)]
  | 60 => some [(0,5),(1,2),(1,3),(3,2),(4,5),(5,2),(5,5),(6,3),(7,2),(7,3),(8,5)]
  | 61 => none
  | 62 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(7,5),(8,1)]
  | 63 => some [(0,2),(1,5),(6,0)]
  | 64 => some [(1,1),(6,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(0,3),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 68 => some [(0,1),(1,4),(1,5),(3,4),(4,1),(5,1),(5,4),(6,5),(7,5),(8,1)]
  | 69 => some [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5)]
  | 70 => none
  | 71 => some [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 72 => some [(2,0),(4,0),(7,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | 75 => some [(3,0),(5,0),(5,3),(7,0),(8,0)]
  | 76 => some [(2,3),(2,5),(4,3),(4,5),(7,3),(8,3),(8,5)]
  | 77 => some [(0,2),(1,0),(1,5),(3,5),(4,2),(5,2),(5,5),(6,0),(7,0),(7,5),(8,2)]
  | 78 => none
  | 79 => none
  | 80 => some [(0,1),(1,4),(6,4),(7,4)]
  | 81 => some [(0,5),(1,2),(6,2),(6,3)]
  | 82 => some [(4,4),(7,2),(7,4),(8,4)]
  | 83 => some [(0,0),(1,3),(1,4),(6,3),(6,4),(7,4)]
  | 84 => some [(0,5),(1,2),(1,3),(6,3),(7,2),(8,2)]
  | 85 => none
  | 86 => none
  | 87 => some [(0,2),(0,3),(1,0),(6,0)]
  | 88 => some [(1,1),(4,1),(7,1),(8,1)]
  | 89 => some [(0,2),(1,5),(4,1),(6,5),(7,5),(8,1)]
  | _ => some [(0,2),(0,3),(0,4),(1,1),(6,0),(6,1),(6,5)]
theorem root7Node0Domains2_fast_eq : root7Node0Domains2 = expandDomains root7Node0Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node0Domains2 v = expandDomains root7Node0Domains2Fast v from by decide) v
theorem root7Node0Step2Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFive
