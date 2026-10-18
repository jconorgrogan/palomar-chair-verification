module

public import SpectreFinite.RadiusFiveRoot0Part0Segment03
public import SpectreFinite.RadiusFiveRoot0Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable2
public import SpectreFinite.RadiusFiveTable33
public import SpectreFinite.RadiusFiveTable45
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
theorem root0Node0Step1Chunk8_3_checked :
    checkNarrowing ⟨table45Scope, table45Rows8_3⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk8_4_checked :
    checkNarrowing ⟨table45Scope, table45Rows8_4⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk8_5_checked :
    checkNarrowing ⟨table45Scope, table45Rows8_5⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Narrowing_checked :
    checkNarrowing table45 root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_flatten table45Scope [table45Rows0_0,table45Rows0_1,table45Rows0_2,table45Rows0_3,table45Rows0_4,table45Rows0_5,table45Rows1_0,table45Rows1_1,table45Rows1_2,table45Rows1_3,table45Rows1_4,table45Rows1_5,table45Rows2_0,table45Rows2_1,table45Rows2_2,table45Rows2_3,table45Rows2_4,table45Rows2_5,table45Rows3_0,table45Rows3_1,table45Rows3_2,table45Rows3_3,table45Rows3_4,table45Rows3_5,table45Rows4_0,table45Rows4_1,table45Rows4_2,table45Rows4_3,table45Rows4_4,table45Rows4_5,table45Rows5_0,table45Rows5_1,table45Rows5_2,table45Rows5_3,table45Rows5_4,table45Rows5_5,table45Rows6_0,table45Rows6_1,table45Rows6_2,table45Rows6_3,table45Rows6_4,table45Rows6_5,table45Rows7_0,table45Rows7_1,table45Rows7_2,table45Rows7_3,table45Rows7_4,table45Rows7_5,table45Rows8_0,table45Rows8_1,table45Rows8_2,table45Rows8_3,table45Rows8_4,table45Rows8_5]
    root0Node0Domains0 root0Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node0Step1Chunk0_0_checked, root0Node0Step1Chunk0_1_checked, root0Node0Step1Chunk0_2_checked, root0Node0Step1Chunk0_3_checked, root0Node0Step1Chunk0_4_checked, root0Node0Step1Chunk0_5_checked, root0Node0Step1Chunk1_0_checked, root0Node0Step1Chunk1_1_checked, root0Node0Step1Chunk1_2_checked, root0Node0Step1Chunk1_3_checked, root0Node0Step1Chunk1_4_checked, root0Node0Step1Chunk1_5_checked, root0Node0Step1Chunk2_0_checked, root0Node0Step1Chunk2_1_checked, root0Node0Step1Chunk2_2_checked, root0Node0Step1Chunk2_3_checked, root0Node0Step1Chunk2_4_checked, root0Node0Step1Chunk2_5_checked, root0Node0Step1Chunk3_0_checked, root0Node0Step1Chunk3_1_checked, root0Node0Step1Chunk3_2_checked, root0Node0Step1Chunk3_3_checked, root0Node0Step1Chunk3_4_checked, root0Node0Step1Chunk3_5_checked, root0Node0Step1Chunk4_0_checked, root0Node0Step1Chunk4_1_checked, root0Node0Step1Chunk4_2_checked, root0Node0Step1Chunk4_3_checked, root0Node0Step1Chunk4_4_checked, root0Node0Step1Chunk4_5_checked, root0Node0Step1Chunk5_0_checked, root0Node0Step1Chunk5_1_checked, root0Node0Step1Chunk5_2_checked, root0Node0Step1Chunk5_3_checked, root0Node0Step1Chunk5_4_checked, root0Node0Step1Chunk5_5_checked, root0Node0Step1Chunk6_0_checked, root0Node0Step1Chunk6_1_checked, root0Node0Step1Chunk6_2_checked, root0Node0Step1Chunk6_3_checked, root0Node0Step1Chunk6_4_checked, root0Node0Step1Chunk6_5_checked, root0Node0Step1Chunk7_0_checked, root0Node0Step1Chunk7_1_checked, root0Node0Step1Chunk7_2_checked, root0Node0Step1Chunk7_3_checked, root0Node0Step1Chunk7_4_checked, root0Node0Step1Chunk7_5_checked, root0Node0Step1Chunk8_0_checked, root0Node0Step1Chunk8_1_checked, root0Node0Step1Chunk8_2_checked, root0Node0Step1Chunk8_3_checked, root0Node0Step1Chunk8_4_checked, root0Node0Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node0Step1_checked :
    checkReplacement table45 root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq
    root0Node0Step1Narrowing_checked (by decide)
def root0Node0Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => stateChoices
  | 2 => stateChoices
  | 3 => stateChoices
  | 4 => stateChoices
  | 5 => stateChoices
  | 6 => stateChoices
  | 7 => [(1,0),(4,0),(7,0),(8,0)]
  | 8 => [(4,3),(7,1),(7,3),(8,3)]
  | 9 => [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 10 => [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 11 => [(2,1),(2,5),(4,1),(4,5),(8,1)]
  | 12 => stateChoices
  | 13 => stateChoices
  | 14 => [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 15 => [(0,1),(1,4),(4,0),(7,4)]
  | 16 => [(0,5),(1,3),(6,2),(6,3),(7,3)]
  | 17 => [(2,0),(2,2),(2,4),(4,2),(4,4),(8,4)]
  | 18 => [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 19 => [(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 20 => [(4,0),(7,0),(7,4),(8,0)]
  | 21 => stateChoices
  | 22 => [(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 23 => [(4,1),(5,1),(7,5),(8,1),(8,5)]
  | 24 => [(0,1),(0,2),(1,0),(6,0),(6,5)]
  | 25 => [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 26 => [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 27 => [(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 28 => [(4,4),(5,1),(5,4),(7,2),(8,1),(8,4)]
  | 29 => [(0,1),(1,4),(6,4),(6,5),(7,4)]
  | 30 => stateChoices
  | 31 => [(4,0),(7,0),(7,4),(8,0)]
  | 32 => [(1,3),(7,3),(8,3)]
  | 33 => [(5,2),(5,5),(8,2)]
  | 34 => [(1,0),(3,0),(5,0)]
  | 35 => [(2,1),(2,5),(4,5)]
  | 36 => [(0,2),(1,0),(6,0),(7,0)]
  | 37 => [(1,1),(4,3),(7,1),(8,3)]
  | 38 => [(4,1),(7,5),(8,5)]
  | 39 => [(0,2),(0,3),(1,0),(6,0),(7,0)]
  | 40 => stateChoices
  | 41 => [(4,4),(5,1),(5,4),(8,1),(8,4)]
  | 42 => [(0,1),(1,4),(6,4),(6,5)]
  | 43 => [(0,4),(0,5),(1,2),(6,2)]
  | 44 => [(4,4),(5,4),(8,4)]
  | 45 => [(0,0)]
  | 46 => [(3,2),(7,2)]
  | 47 => [(4,0),(7,4)]
  | 48 => [(1,3),(6,3),(7,3)]
  | 49 => [(4,2),(5,2),(7,2),(8,2)]
  | 50 => [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 51 => stateChoices
  | 52 => [(5,5),(7,5),(8,5)]
  | 53 => [(0,3),(1,0),(6,0),(7,0)]
  | 54 => [(4,3),(7,1),(8,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(4,1),(5,1),(8,1)]
  | 58 => [(0,1),(0,2),(6,5)]
  | 59 => [(0,4),(1,1),(6,2)]
  | 60 => [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(8,1),(8,4)]
  | 61 => stateChoices
  | 62 => [(4,2),(4,4),(8,2)]
  | 63 => [(1,4),(5,0),(5,3)]
  | 64 => [(0,5),(4,5),(5,5),(8,5)]
  | 65 => [(2,0),(7,0)]
  | 66 => [(7,3),(8,3)]
  | 67 => [(5,2),(5,5),(8,5)]
  | 68 => [(1,0),(3,0),(7,0),(8,0)]
  | 69 => [(2,1),(2,3),(2,5),(4,3),(7,1),(7,3),(8,3)]
  | 70 => stateChoices
  | 71 => [(1,4),(3,4),(5,4),(7,4),(7,5),(8,4)]
  | 72 => [(0,0),(0,5),(6,0),(6,3)]
  | 73 => [(3,1),(4,4),(7,2)]
  | 74 => [(0,1),(1,4),(7,4)]
  | 75 => [(0,5),(1,3),(6,2),(6,3)]
  | 76 => [(4,4),(7,2),(8,2),(8,4)]
  | 77 => [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 78 => stateChoices
  | 79 => [(0,2),(1,5),(6,0),(8,2)]
  | 80 => [(1,1),(5,0),(6,1),(7,1)]
  | 81 => [(4,1),(4,5),(7,5),(8,1)]
  | 82 => [(0,2),(1,0),(6,0),(6,5)]
  | 83 => [(0,4),(1,1),(7,1)]
  | 84 => [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 85 => stateChoices
  | 86 => stateChoices
  | 87 => [(0,0),(7,3),(8,3)]
  | 88 => [(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 89 => [(4,0),(5,0),(7,0),(8,0)]
  | _ => [(4,3),(4,5),(7,3),(8,3)]
def root0Node0Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => none
  | 1 => none
  | 2 => none
  | 3 => none
  | 4 => none
  | 5 => none
  | 6 => none
  | 7 => some [(1,0),(4,0),(7,0),(8,0)]
  | 8 => some [(4,3),(7,1),(7,3),(8,3)]
  | 9 => some [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 10 => some [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 11 => some [(2,1),(2,5),(4,1),(4,5),(8,1)]
  | 12 => none
  | 13 => none
  | 14 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 15 => some [(0,1),(1,4),(4,0),(7,4)]
  | 16 => some [(0,5),(1,3),(6,2),(6,3),(7,3)]
  | 17 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(8,4)]
  | 18 => some [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 19 => some [(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 20 => some [(4,0),(7,0),(7,4),(8,0)]
  | 21 => none
  | 22 => some [(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 23 => some [(4,1),(5,1),(7,5),(8,1),(8,5)]
  | 24 => some [(0,1),(0,2),(1,0),(6,0),(6,5)]
  | 25 => some [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 26 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 27 => some [(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 28 => some [(4,4),(5,1),(5,4),(7,2),(8,1),(8,4)]
  | 29 => some [(0,1),(1,4),(6,4),(6,5),(7,4)]
  | 30 => none
  | 31 => some [(4,0),(7,0),(7,4),(8,0)]
  | 32 => some [(1,3),(7,3),(8,3)]
  | 33 => some [(5,2),(5,5),(8,2)]
  | 34 => some [(1,0),(3,0),(5,0)]
  | 35 => some [(2,1),(2,5),(4,5)]
  | 36 => some [(0,2),(1,0),(6,0),(7,0)]
  | 37 => some [(1,1),(4,3),(7,1),(8,3)]
  | 38 => some [(4,1),(7,5),(8,5)]
  | 39 => some [(0,2),(0,3),(1,0),(6,0),(7,0)]
  | 40 => none
  | 41 => some [(4,4),(5,1),(5,4),(8,1),(8,4)]
  | 42 => some [(0,1),(1,4),(6,4),(6,5)]
  | 43 => some [(0,4),(0,5),(1,2),(6,2)]
  | 44 => some [(4,4),(5,4),(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(3,2),(7,2)]
  | 47 => some [(4,0),(7,4)]
  | 48 => some [(1,3),(6,3),(7,3)]
  | 49 => some [(4,2),(5,2),(7,2),(8,2)]
  | 50 => some [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 51 => none
  | 52 => some [(5,5),(7,5),(8,5)]
  | 53 => some [(0,3),(1,0),(6,0),(7,0)]
  | 54 => some [(4,3),(7,1),(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(4,1),(5,1),(8,1)]
  | 58 => some [(0,1),(0,2),(6,5)]
  | 59 => some [(0,4),(1,1),(6,2)]
  | 60 => some [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(8,1),(8,4)]
  | 61 => none
  | 62 => some [(4,2),(4,4),(8,2)]
  | 63 => some [(1,4),(5,0),(5,3)]
  | 64 => some [(0,5),(4,5),(5,5),(8,5)]
  | 65 => some [(2,0),(7,0)]
  | 66 => some [(7,3),(8,3)]
  | 67 => some [(5,2),(5,5),(8,5)]
  | 68 => some [(1,0),(3,0),(7,0),(8,0)]
  | 69 => some [(2,1),(2,3),(2,5),(4,3),(7,1),(7,3),(8,3)]
  | 70 => none
  | 71 => some [(1,4),(3,4),(5,4),(7,4),(7,5),(8,4)]
  | 72 => some [(0,0),(0,5),(6,0),(6,3)]
  | 73 => some [(3,1),(4,4),(7,2)]
  | 74 => some [(0,1),(1,4),(7,4)]
  | 75 => some [(0,5),(1,3),(6,2),(6,3)]
  | 76 => some [(4,4),(7,2),(8,2),(8,4)]
  | 77 => some [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 78 => none
  | 79 => some [(0,2),(1,5),(6,0),(8,2)]
  | 80 => some [(1,1),(5,0),(6,1),(7,1)]
  | 81 => some [(4,1),(4,5),(7,5),(8,1)]
  | 82 => some [(0,2),(1,0),(6,0),(6,5)]
  | 83 => some [(0,4),(1,1),(7,1)]
  | 84 => some [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 85 => none
  | 86 => none
  | 87 => some [(0,0),(7,3),(8,3)]
  | 88 => some [(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 89 => some [(4,0),(5,0),(7,0),(8,0)]
  | _ => some [(4,3),(4,5),(7,3),(8,3)]
theorem root0Node0Domains2_fast_eq : root0Node0Domains2 = expandDomains root0Node0Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node0Domains2 v = expandDomains root0Node0Domains2Fast v from by decide) v
theorem root0Node0Step2Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFive
