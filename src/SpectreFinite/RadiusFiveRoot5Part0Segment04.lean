module

public import SpectreFinite.RadiusFiveRoot5Part0Segment03
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
theorem root5Node0Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Narrowing_checked :
    checkNarrowing table56 root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root5Node0Domains0 root5Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root5Node0Step1Chunk0_0_checked, root5Node0Step1Chunk0_1_checked, root5Node0Step1Chunk0_2_checked, root5Node0Step1Chunk0_3_checked, root5Node0Step1Chunk0_4_checked, root5Node0Step1Chunk0_5_checked, root5Node0Step1Chunk1_0_checked, root5Node0Step1Chunk1_1_checked, root5Node0Step1Chunk1_2_checked, root5Node0Step1Chunk1_3_checked, root5Node0Step1Chunk1_4_checked, root5Node0Step1Chunk1_5_checked, root5Node0Step1Chunk2_0_checked, root5Node0Step1Chunk2_1_checked, root5Node0Step1Chunk2_2_checked, root5Node0Step1Chunk2_3_checked, root5Node0Step1Chunk2_4_checked, root5Node0Step1Chunk2_5_checked, root5Node0Step1Chunk3_0_checked, root5Node0Step1Chunk3_1_checked, root5Node0Step1Chunk3_2_checked, root5Node0Step1Chunk3_3_checked, root5Node0Step1Chunk3_4_checked, root5Node0Step1Chunk3_5_checked, root5Node0Step1Chunk4_0_checked, root5Node0Step1Chunk4_1_checked, root5Node0Step1Chunk4_2_checked, root5Node0Step1Chunk4_3_checked, root5Node0Step1Chunk4_4_checked, root5Node0Step1Chunk4_5_checked, root5Node0Step1Chunk5_0_checked, root5Node0Step1Chunk5_1_checked, root5Node0Step1Chunk5_2_checked, root5Node0Step1Chunk5_3_checked, root5Node0Step1Chunk5_4_checked, root5Node0Step1Chunk5_5_checked, root5Node0Step1Chunk6_0_checked, root5Node0Step1Chunk6_1_checked, root5Node0Step1Chunk6_2_checked, root5Node0Step1Chunk6_3_checked, root5Node0Step1Chunk6_4_checked, root5Node0Step1Chunk6_5_checked, root5Node0Step1Chunk7_0_checked, root5Node0Step1Chunk7_1_checked, root5Node0Step1Chunk7_2_checked, root5Node0Step1Chunk7_3_checked, root5Node0Step1Chunk7_4_checked, root5Node0Step1Chunk7_5_checked, root5Node0Step1Chunk8_0_checked, root5Node0Step1Chunk8_1_checked, root5Node0Step1Chunk8_2_checked, root5Node0Step1Chunk8_3_checked, root5Node0Step1Chunk8_4_checked, root5Node0Step1Chunk8_5_checked, Bool.true_and])
theorem root5Node0Step1_checked :
    checkReplacement table56 root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq
    root5Node0Step1Narrowing_checked (by decide)
def root5Node0Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(3,4),(7,4),(8,4)]
  | 1 => [(0,0),(0,5),(1,3),(6,2),(6,3)]
  | 2 => [(4,4),(7,2),(8,2),(8,4)]
  | 3 => [(1,4),(4,0),(5,0),(7,4),(8,0)]
  | 4 => [(0,5),(1,3),(4,5),(6,3),(7,3)]
  | 5 => [(2,0),(2,2),(2,4),(4,2),(4,4),(7,0)]
  | 6 => [(2,1),(2,3),(2,5),(4,1),(4,5),(8,1)]
  | 7 => [(0,2),(1,0),(1,5),(6,0),(6,5)]
  | 8 => [(0,4),(1,1),(6,1),(7,1)]
  | 9 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 10 => [(0,0),(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 11 => [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 12 => [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 13 => [(0,0),(1,3),(3,3),(5,3),(6,4),(7,3),(8,3)]
  | 14 => [(1,2),(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 15 => [(4,0),(7,0),(8,0)]
  | 16 => [(4,3),(7,3),(8,3)]
  | 17 => [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 18 => [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 19 => [(2,1),(2,5),(4,1),(4,5)]
  | 20 => [(0,2),(1,0),(6,0),(7,0)]
  | 21 => [(0,1),(1,4),(1,5),(3,4),(6,5),(7,4),(7,5)]
  | 22 => [(0,3),(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 23 => [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 24 => [(0,1),(1,4),(7,4)]
  | 25 => [(0,5),(6,2),(6,3)]
  | 26 => [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 27 => [(0,0),(1,3),(3,3),(7,3)]
  | 28 => [(3,2),(5,2),(7,2)]
  | 29 => [(4,0),(7,4),(8,0)]
  | 30 => stateChoices
  | 31 => [(0,2),(1,0),(4,2),(6,0),(7,0)]
  | 32 => [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 33 => [(4,1),(7,5),(8,5)]
  | 34 => [(0,2),(1,0),(6,0)]
  | 35 => [(1,1),(3,1),(7,1)]
  | 36 => [(0,1),(1,5),(6,5)]
  | 37 => [(0,4),(6,1),(6,2)]
  | 38 => [(5,1),(5,4),(8,1),(8,4)]
  | 39 => stateChoices
  | 40 => stateChoices
  | 41 => stateChoices
  | 42 => [(4,0),(7,4),(8,0)]
  | 43 => [(1,3),(7,3)]
  | 44 => [(5,2),(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(1,0),(7,0)]
  | 48 => [(4,3),(7,1),(8,3)]
  | 49 => [(7,5),(8,5)]
  | 50 => stateChoices
  | 51 => stateChoices
  | 52 => [(5,1),(5,4),(8,1),(8,4)]
  | 53 => [(0,1),(6,4),(6,5)]
  | 54 => [(0,4),(1,2),(6,2)]
  | 55 => [(5,4),(8,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(4,0),(7,4)]
  | 59 => [(1,3),(6,3),(7,3)]
  | 60 => [(4,2),(7,2),(8,2)]
  | 61 => stateChoices
  | 62 => [(5,5),(7,5),(8,5)]
  | 63 => [(0,3),(1,0),(7,0)]
  | 64 => [(4,3),(7,1),(8,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(4,1),(5,1),(8,1)]
  | 68 => [(0,1),(0,2),(6,5)]
  | 69 => [(0,4),(1,1),(6,2)]
  | 70 => stateChoices
  | 71 => [(4,2),(4,4),(8,2)]
  | 72 => [(1,4),(5,0),(5,3)]
  | 73 => [(0,5),(4,5),(5,5),(8,5)]
  | 74 => [(2,0),(7,0)]
  | 75 => [(7,3),(8,3)]
  | 76 => [(5,2),(5,5),(8,5)]
  | 77 => [(1,0),(3,0),(7,0),(8,0)]
  | 78 => stateChoices
  | 79 => [(1,4),(3,4),(5,4),(7,4),(7,5)]
  | 80 => [(0,0),(0,5),(6,0),(6,3)]
  | 81 => [(3,1),(4,4),(7,2)]
  | 82 => [(0,1),(1,4),(7,4)]
  | 83 => [(0,5),(1,3),(6,2),(6,3)]
  | 84 => [(4,4),(7,2),(8,2),(8,4)]
  | 85 => stateChoices
  | 86 => [(0,2),(1,5),(6,0),(8,2)]
  | 87 => [(1,1),(5,0),(6,1),(7,1)]
  | 88 => [(4,1),(4,5),(7,5),(8,1)]
  | 89 => [(0,2),(1,0),(6,0),(6,5)]
  | _ => [(0,4),(1,1),(7,1)]
def root5Node0Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(3,4),(7,4),(8,4)]
  | 1 => some [(0,0),(0,5),(1,3),(6,2),(6,3)]
  | 2 => some [(4,4),(7,2),(8,2),(8,4)]
  | 3 => some [(1,4),(4,0),(5,0),(7,4),(8,0)]
  | 4 => some [(0,5),(1,3),(4,5),(6,3),(7,3)]
  | 5 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(7,0)]
  | 6 => some [(2,1),(2,3),(2,5),(4,1),(4,5),(8,1)]
  | 7 => some [(0,2),(1,0),(1,5),(6,0),(6,5)]
  | 8 => some [(0,4),(1,1),(6,1),(7,1)]
  | 9 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 10 => some [(0,0),(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 11 => some [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 12 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 13 => some [(0,0),(1,3),(3,3),(5,3),(6,4),(7,3),(8,3)]
  | 14 => some [(1,2),(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 15 => some [(4,0),(7,0),(8,0)]
  | 16 => some [(4,3),(7,3),(8,3)]
  | 17 => some [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 18 => some [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 19 => some [(2,1),(2,5),(4,1),(4,5)]
  | 20 => some [(0,2),(1,0),(6,0),(7,0)]
  | 21 => some [(0,1),(1,4),(1,5),(3,4),(6,5),(7,4),(7,5)]
  | 22 => some [(0,3),(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 23 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 24 => some [(0,1),(1,4),(7,4)]
  | 25 => some [(0,5),(6,2),(6,3)]
  | 26 => some [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 27 => some [(0,0),(1,3),(3,3),(7,3)]
  | 28 => some [(3,2),(5,2),(7,2)]
  | 29 => some [(4,0),(7,4),(8,0)]
  | 30 => none
  | 31 => some [(0,2),(1,0),(4,2),(6,0),(7,0)]
  | 32 => some [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 33 => some [(4,1),(7,5),(8,5)]
  | 34 => some [(0,2),(1,0),(6,0)]
  | 35 => some [(1,1),(3,1),(7,1)]
  | 36 => some [(0,1),(1,5),(6,5)]
  | 37 => some [(0,4),(6,1),(6,2)]
  | 38 => some [(5,1),(5,4),(8,1),(8,4)]
  | 39 => none
  | 40 => none
  | 41 => none
  | 42 => some [(4,0),(7,4),(8,0)]
  | 43 => some [(1,3),(7,3)]
  | 44 => some [(5,2),(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0),(7,0)]
  | 48 => some [(4,3),(7,1),(8,3)]
  | 49 => some [(7,5),(8,5)]
  | 50 => none
  | 51 => none
  | 52 => some [(5,1),(5,4),(8,1),(8,4)]
  | 53 => some [(0,1),(6,4),(6,5)]
  | 54 => some [(0,4),(1,2),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0),(7,4)]
  | 59 => some [(1,3),(6,3),(7,3)]
  | 60 => some [(4,2),(7,2),(8,2)]
  | 61 => none
  | 62 => some [(5,5),(7,5),(8,5)]
  | 63 => some [(0,3),(1,0),(7,0)]
  | 64 => some [(4,3),(7,1),(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1),(5,1),(8,1)]
  | 68 => some [(0,1),(0,2),(6,5)]
  | 69 => some [(0,4),(1,1),(6,2)]
  | 70 => none
  | 71 => some [(4,2),(4,4),(8,2)]
  | 72 => some [(1,4),(5,0),(5,3)]
  | 73 => some [(0,5),(4,5),(5,5),(8,5)]
  | 74 => some [(2,0),(7,0)]
  | 75 => some [(7,3),(8,3)]
  | 76 => some [(5,2),(5,5),(8,5)]
  | 77 => some [(1,0),(3,0),(7,0),(8,0)]
  | 78 => none
  | 79 => some [(1,4),(3,4),(5,4),(7,4),(7,5)]
  | 80 => some [(0,0),(0,5),(6,0),(6,3)]
  | 81 => some [(3,1),(4,4),(7,2)]
  | 82 => some [(0,1),(1,4),(7,4)]
  | 83 => some [(0,5),(1,3),(6,2),(6,3)]
  | 84 => some [(4,4),(7,2),(8,2),(8,4)]
  | 85 => none
  | 86 => some [(0,2),(1,5),(6,0),(8,2)]
  | 87 => some [(1,1),(5,0),(6,1),(7,1)]
  | 88 => some [(4,1),(4,5),(7,5),(8,1)]
  | 89 => some [(0,2),(1,0),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root5Node0Domains2_fast_eq : root5Node0Domains2 = expandDomains root5Node0Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node0Domains2 v = expandDomains root5Node0Domains2Fast v from by decide) v
theorem root5Node0Step2Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFive
