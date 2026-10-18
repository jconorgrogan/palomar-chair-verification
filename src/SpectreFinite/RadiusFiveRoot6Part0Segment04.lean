module

public import SpectreFinite.RadiusFiveRoot6Part0Segment03
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
theorem root6Node0Step1Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains0 root6Node0Domains1
    root6Node0Domains0Fast root6Node0Domains1Fast
    root6Node0Domains0_fast_eq root6Node0Domains1_fast_eq (by decide)
theorem root6Node0Step1Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains0 root6Node0Domains1
    root6Node0Domains0Fast root6Node0Domains1Fast
    root6Node0Domains0_fast_eq root6Node0Domains1_fast_eq (by decide)
theorem root6Node0Step1Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains0 root6Node0Domains1
    root6Node0Domains0Fast root6Node0Domains1Fast
    root6Node0Domains0_fast_eq root6Node0Domains1_fast_eq (by decide)
theorem root6Node0Step1Narrowing_checked :
    checkNarrowing table35 root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkNarrowing_flatten table35Scope [table35Rows0_0,table35Rows0_1,table35Rows0_2,table35Rows0_3,table35Rows0_4,table35Rows0_5,table35Rows1_0,table35Rows1_1,table35Rows1_2,table35Rows1_3,table35Rows1_4,table35Rows1_5,table35Rows2_0,table35Rows2_1,table35Rows2_2,table35Rows2_3,table35Rows2_4,table35Rows2_5,table35Rows3_0,table35Rows3_1,table35Rows3_2,table35Rows3_3,table35Rows3_4,table35Rows3_5,table35Rows4_0,table35Rows4_1,table35Rows4_2,table35Rows4_3,table35Rows4_4,table35Rows4_5,table35Rows5_0,table35Rows5_1,table35Rows5_2,table35Rows5_3,table35Rows5_4,table35Rows5_5,table35Rows6_0,table35Rows6_1,table35Rows6_2,table35Rows6_3,table35Rows6_4,table35Rows6_5,table35Rows7_0,table35Rows7_1,table35Rows7_2,table35Rows7_3,table35Rows7_4,table35Rows7_5,table35Rows8_0,table35Rows8_1,table35Rows8_2,table35Rows8_3,table35Rows8_4,table35Rows8_5]
    root6Node0Domains0 root6Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node0Step1Chunk0_0_checked, root6Node0Step1Chunk0_1_checked, root6Node0Step1Chunk0_2_checked, root6Node0Step1Chunk0_3_checked, root6Node0Step1Chunk0_4_checked, root6Node0Step1Chunk0_5_checked, root6Node0Step1Chunk1_0_checked, root6Node0Step1Chunk1_1_checked, root6Node0Step1Chunk1_2_checked, root6Node0Step1Chunk1_3_checked, root6Node0Step1Chunk1_4_checked, root6Node0Step1Chunk1_5_checked, root6Node0Step1Chunk2_0_checked, root6Node0Step1Chunk2_1_checked, root6Node0Step1Chunk2_2_checked, root6Node0Step1Chunk2_3_checked, root6Node0Step1Chunk2_4_checked, root6Node0Step1Chunk2_5_checked, root6Node0Step1Chunk3_0_checked, root6Node0Step1Chunk3_1_checked, root6Node0Step1Chunk3_2_checked, root6Node0Step1Chunk3_3_checked, root6Node0Step1Chunk3_4_checked, root6Node0Step1Chunk3_5_checked, root6Node0Step1Chunk4_0_checked, root6Node0Step1Chunk4_1_checked, root6Node0Step1Chunk4_2_checked, root6Node0Step1Chunk4_3_checked, root6Node0Step1Chunk4_4_checked, root6Node0Step1Chunk4_5_checked, root6Node0Step1Chunk5_0_checked, root6Node0Step1Chunk5_1_checked, root6Node0Step1Chunk5_2_checked, root6Node0Step1Chunk5_3_checked, root6Node0Step1Chunk5_4_checked, root6Node0Step1Chunk5_5_checked, root6Node0Step1Chunk6_0_checked, root6Node0Step1Chunk6_1_checked, root6Node0Step1Chunk6_2_checked, root6Node0Step1Chunk6_3_checked, root6Node0Step1Chunk6_4_checked, root6Node0Step1Chunk6_5_checked, root6Node0Step1Chunk7_0_checked, root6Node0Step1Chunk7_1_checked, root6Node0Step1Chunk7_2_checked, root6Node0Step1Chunk7_3_checked, root6Node0Step1Chunk7_4_checked, root6Node0Step1Chunk7_5_checked, root6Node0Step1Chunk8_0_checked, root6Node0Step1Chunk8_1_checked, root6Node0Step1Chunk8_2_checked, root6Node0Step1Chunk8_3_checked, root6Node0Step1Chunk8_4_checked, root6Node0Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node0Step1_checked :
    checkReplacement table35 root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node0Domains0 root6Node0Domains1
    root6Node0Domains0Fast root6Node0Domains1Fast
    root6Node0Domains0_fast_eq root6Node0Domains1_fast_eq
    root6Node0Step1Narrowing_checked (by decide)
def root6Node0Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => [(4,3),(5,0),(5,3),(8,0),(8,3)]
  | 2 => [(4,5),(7,3),(7,5),(8,5)]
  | 3 => [(1,0),(4,2),(5,2),(6,0),(7,0),(8,2)]
  | 4 => [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 5 => [(1,5),(4,5),(7,5),(8,5)]
  | 6 => stateChoices
  | 7 => [(5,4),(7,4),(8,4)]
  | 8 => [(0,0),(1,3),(6,3),(6,4)]
  | 9 => [(1,2),(7,2),(8,2)]
  | 10 => [(4,0),(5,0),(7,4),(8,0),(8,4)]
  | 11 => [(0,0),(1,3),(4,5),(7,3)]
  | 12 => [(4,2),(7,0),(7,2),(8,2)]
  | 13 => [(0,3),(1,1),(6,1),(7,0)]
  | 14 => [(4,1),(4,3),(8,1)]
  | 15 => [(0,2),(1,5),(6,5),(7,5)]
  | 16 => [(0,3),(0,4),(1,1),(6,1)]
  | 17 => [(5,1),(5,4),(8,1)]
  | 18 => [(0,0),(0,1),(1,5),(6,4),(6,5)]
  | 19 => [(0,4),(1,2),(6,1),(6,2),(7,2)]
  | 20 => [(1,4),(3,4),(5,1),(5,4),(7,4),(8,1)]
  | 21 => [(2,0),(2,2),(2,4),(4,0),(4,2),(7,0),(7,2),(8,0)]
  | 22 => [(1,3),(3,3),(5,3),(7,3),(7,4),(8,3)]
  | 23 => [(1,3),(5,2),(5,5)]
  | 24 => [(4,2),(7,0),(8,0)]
  | 25 => [(4,3),(5,3),(8,3)]
  | 26 => [(1,5),(3,5),(5,5)]
  | 27 => [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 28 => [(2,1),(2,3),(2,5),(4,1),(4,3),(8,3)]
  | 29 => [(0,2),(1,5),(3,5),(5,5),(6,0)]
  | 30 => [(0,4),(1,1),(3,1),(4,4),(5,1),(5,4),(6,1),(7,1),(8,4)]
  | 31 => [(0,1),(1,4),(6,5),(8,1)]
  | 32 => [(0,4),(0,5),(6,2),(6,5)]
  | 33 => [(0,4),(4,4),(5,4),(8,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,0),(2,4),(4,4)]
  | 37 => [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 38 => [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 39 => [(2,0),(2,4),(4,0),(4,4),(8,0)]
  | 40 => [(3,0),(4,3),(5,0),(5,3),(7,0),(7,1),(8,0),(8,3)]
  | 41 => [(2,5),(4,5),(7,5),(8,3),(8,5)]
  | 42 => [(1,0),(5,5),(6,0),(7,0)]
  | 43 => [(3,0),(4,3),(7,1)]
  | 44 => [(2,5),(7,5)]
  | 45 => [(6,0)]
  | 46 => [(3,1),(7,1)]
  | 47 => [(0,1),(1,5),(6,5),(7,5)]
  | 48 => [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 49 => [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 50 => stateChoices
  | 51 => [(0,0),(1,3),(1,4),(7,3)]
  | 52 => [(0,5),(7,2),(8,2)]
  | 53 => [(4,0),(4,4),(7,4),(8,0)]
  | 54 => [(0,0),(1,3),(7,3)]
  | 55 => [(7,2),(8,2)]
  | 56 => [(4,0),(5,0),(8,0)]
  | 57 => [(4,5),(7,3)]
  | 58 => [(1,0),(4,2),(7,0),(8,2)]
  | 59 => [(4,3),(5,0),(5,3),(7,1),(8,0),(8,3)]
  | 60 => stateChoices
  | 61 => [(0,4),(6,0),(6,1),(6,2)]
  | 62 => [(5,1),(5,4),(7,1),(8,1),(8,4)]
  | 63 => [(0,1),(1,5),(6,4),(6,5)]
  | 64 => [(0,4),(1,2),(6,1),(6,2)]
  | 65 => [(5,1),(5,4),(8,4)]
  | 66 => [(0,0),(0,1),(6,4)]
  | 67 => [(1,2),(6,2),(7,2)]
  | 68 => [(4,0),(7,4),(8,4)]
  | 69 => stateChoices
  | 70 => [(4,3),(5,0),(7,1),(8,3)]
  | 71 => [(4,5),(5,5),(7,5),(8,5)]
  | 72 => [(0,3),(1,0),(7,0)]
  | 73 => [(4,3),(7,1),(8,1),(8,3)]
  | 74 => [(1,5),(3,5),(7,5),(8,5)]
  | 75 => [(0,3),(1,0),(6,1)]
  | 76 => [(4,1),(5,1),(7,1),(8,1)]
  | 77 => stateChoices
  | 78 => [(0,0),(0,5),(1,3),(6,3),(7,3)]
  | 79 => [(4,2),(4,4),(7,2),(8,2)]
  | 80 => [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 81 => [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 82 => [(2,0),(2,2),(2,4),(4,2),(7,0),(7,2),(8,2)]
  | 83 => stateChoices
  | 84 => stateChoices
  | 85 => [(0,4),(1,1),(1,2),(6,1),(6,2),(7,1)]
  | 86 => [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(7,5),(8,1)]
  | 87 => [(0,0),(0,1),(0,2),(0,5),(6,0),(6,3),(6,4),(6,5)]
  | 88 => [(0,4),(1,1),(1,2),(3,1),(4,4),(6,2),(7,1),(7,2)]
  | 89 => stateChoices
  | _ => stateChoices
def root6Node0Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => none
  | 1 => some [(4,3),(5,0),(5,3),(8,0),(8,3)]
  | 2 => some [(4,5),(7,3),(7,5),(8,5)]
  | 3 => some [(1,0),(4,2),(5,2),(6,0),(7,0),(8,2)]
  | 4 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 5 => some [(1,5),(4,5),(7,5),(8,5)]
  | 6 => none
  | 7 => some [(5,4),(7,4),(8,4)]
  | 8 => some [(0,0),(1,3),(6,3),(6,4)]
  | 9 => some [(1,2),(7,2),(8,2)]
  | 10 => some [(4,0),(5,0),(7,4),(8,0),(8,4)]
  | 11 => some [(0,0),(1,3),(4,5),(7,3)]
  | 12 => some [(4,2),(7,0),(7,2),(8,2)]
  | 13 => some [(0,3),(1,1),(6,1),(7,0)]
  | 14 => some [(4,1),(4,3),(8,1)]
  | 15 => some [(0,2),(1,5),(6,5),(7,5)]
  | 16 => some [(0,3),(0,4),(1,1),(6,1)]
  | 17 => some [(5,1),(5,4),(8,1)]
  | 18 => some [(0,0),(0,1),(1,5),(6,4),(6,5)]
  | 19 => some [(0,4),(1,2),(6,1),(6,2),(7,2)]
  | 20 => some [(1,4),(3,4),(5,1),(5,4),(7,4),(8,1)]
  | 21 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(7,0),(7,2),(8,0)]
  | 22 => some [(1,3),(3,3),(5,3),(7,3),(7,4),(8,3)]
  | 23 => some [(1,3),(5,2),(5,5)]
  | 24 => some [(4,2),(7,0),(8,0)]
  | 25 => some [(4,3),(5,3),(8,3)]
  | 26 => some [(1,5),(3,5),(5,5)]
  | 27 => some [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 28 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(8,3)]
  | 29 => some [(0,2),(1,5),(3,5),(5,5),(6,0)]
  | 30 => some [(0,4),(1,1),(3,1),(4,4),(5,1),(5,4),(6,1),(7,1),(8,4)]
  | 31 => some [(0,1),(1,4),(6,5),(8,1)]
  | 32 => some [(0,4),(0,5),(6,2),(6,5)]
  | 33 => some [(0,4),(4,4),(5,4),(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0),(2,4),(4,4)]
  | 37 => some [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 38 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 39 => some [(2,0),(2,4),(4,0),(4,4),(8,0)]
  | 40 => some [(3,0),(4,3),(5,0),(5,3),(7,0),(7,1),(8,0),(8,3)]
  | 41 => some [(2,5),(4,5),(7,5),(8,3),(8,5)]
  | 42 => some [(1,0),(5,5),(6,0),(7,0)]
  | 43 => some [(3,0),(4,3),(7,1)]
  | 44 => some [(2,5),(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1),(7,1)]
  | 47 => some [(0,1),(1,5),(6,5),(7,5)]
  | 48 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 49 => some [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 50 => none
  | 51 => some [(0,0),(1,3),(1,4),(7,3)]
  | 52 => some [(0,5),(7,2),(8,2)]
  | 53 => some [(4,0),(4,4),(7,4),(8,0)]
  | 54 => some [(0,0),(1,3),(7,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(4,0),(5,0),(8,0)]
  | 57 => some [(4,5),(7,3)]
  | 58 => some [(1,0),(4,2),(7,0),(8,2)]
  | 59 => some [(4,3),(5,0),(5,3),(7,1),(8,0),(8,3)]
  | 60 => none
  | 61 => some [(0,4),(6,0),(6,1),(6,2)]
  | 62 => some [(5,1),(5,4),(7,1),(8,1),(8,4)]
  | 63 => some [(0,1),(1,5),(6,4),(6,5)]
  | 64 => some [(0,4),(1,2),(6,1),(6,2)]
  | 65 => some [(5,1),(5,4),(8,4)]
  | 66 => some [(0,0),(0,1),(6,4)]
  | 67 => some [(1,2),(6,2),(7,2)]
  | 68 => some [(4,0),(7,4),(8,4)]
  | 69 => none
  | 70 => some [(4,3),(5,0),(7,1),(8,3)]
  | 71 => some [(4,5),(5,5),(7,5),(8,5)]
  | 72 => some [(0,3),(1,0),(7,0)]
  | 73 => some [(4,3),(7,1),(8,1),(8,3)]
  | 74 => some [(1,5),(3,5),(7,5),(8,5)]
  | 75 => some [(0,3),(1,0),(6,1)]
  | 76 => some [(4,1),(5,1),(7,1),(8,1)]
  | 77 => none
  | 78 => some [(0,0),(0,5),(1,3),(6,3),(7,3)]
  | 79 => some [(4,2),(4,4),(7,2),(8,2)]
  | 80 => some [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 81 => some [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 82 => some [(2,0),(2,2),(2,4),(4,2),(7,0),(7,2),(8,2)]
  | 83 => none
  | 84 => none
  | 85 => some [(0,4),(1,1),(1,2),(6,1),(6,2),(7,1)]
  | 86 => some [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(7,5),(8,1)]
  | 87 => some [(0,0),(0,1),(0,2),(0,5),(6,0),(6,3),(6,4),(6,5)]
  | 88 => some [(0,4),(1,1),(1,2),(3,1),(4,4),(6,2),(7,1),(7,2)]
  | 89 => none
  | _ => none
theorem root6Node0Domains2_fast_eq : root6Node0Domains2 = expandDomains root6Node0Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node0Domains2 v = expandDomains root6Node0Domains2Fast v from by decide) v
theorem root6Node0Step2Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root6Node0Domains1 root6Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains1 root6Node0Domains2
    root6Node0Domains1Fast root6Node0Domains2Fast
    root6Node0Domains1_fast_eq root6Node0Domains2_fast_eq (by decide)
theorem root6Node0Step2Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root6Node0Domains1 root6Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains1 root6Node0Domains2
    root6Node0Domains1Fast root6Node0Domains2Fast
    root6Node0Domains1_fast_eq root6Node0Domains2_fast_eq (by decide)
theorem root6Node0Step2Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root6Node0Domains1 root6Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains1 root6Node0Domains2
    root6Node0Domains1Fast root6Node0Domains2Fast
    root6Node0Domains1_fast_eq root6Node0Domains2_fast_eq (by decide)
theorem root6Node0Step2Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root6Node0Domains1 root6Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains1 root6Node0Domains2
    root6Node0Domains1Fast root6Node0Domains2Fast
    root6Node0Domains1_fast_eq root6Node0Domains2_fast_eq (by decide)
theorem root6Node0Step2Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root6Node0Domains1 root6Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains1 root6Node0Domains2
    root6Node0Domains1Fast root6Node0Domains2Fast
    root6Node0Domains1_fast_eq root6Node0Domains2_fast_eq (by decide)
theorem root6Node0Step2Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root6Node0Domains1 root6Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains1 root6Node0Domains2
    root6Node0Domains1Fast root6Node0Domains2Fast
    root6Node0Domains1_fast_eq root6Node0Domains2_fast_eq (by decide)
theorem root6Node0Step2Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root6Node0Domains1 root6Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains1 root6Node0Domains2
    root6Node0Domains1Fast root6Node0Domains2Fast
    root6Node0Domains1_fast_eq root6Node0Domains2_fast_eq (by decide)
theorem root6Node0Step2Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root6Node0Domains1 root6Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains1 root6Node0Domains2
    root6Node0Domains1Fast root6Node0Domains2Fast
    root6Node0Domains1_fast_eq root6Node0Domains2_fast_eq (by decide)
theorem root6Node0Step2Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root6Node0Domains1 root6Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains1 root6Node0Domains2
    root6Node0Domains1Fast root6Node0Domains2Fast
    root6Node0Domains1_fast_eq root6Node0Domains2_fast_eq (by decide)
theorem root6Node0Step2Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root6Node0Domains1 root6Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains1 root6Node0Domains2
    root6Node0Domains1Fast root6Node0Domains2Fast
    root6Node0Domains1_fast_eq root6Node0Domains2_fast_eq (by decide)
theorem root6Node0Step2Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root6Node0Domains1 root6Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains1 root6Node0Domains2
    root6Node0Domains1Fast root6Node0Domains2Fast
    root6Node0Domains1_fast_eq root6Node0Domains2_fast_eq (by decide)
theorem root6Node0Step2Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root6Node0Domains1 root6Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains1 root6Node0Domains2
    root6Node0Domains1Fast root6Node0Domains2Fast
    root6Node0Domains1_fast_eq root6Node0Domains2_fast_eq (by decide)
theorem root6Node0Step2Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root6Node0Domains1 root6Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains1 root6Node0Domains2
    root6Node0Domains1Fast root6Node0Domains2Fast
    root6Node0Domains1_fast_eq root6Node0Domains2_fast_eq (by decide)
theorem root6Node0Step2Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root6Node0Domains1 root6Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains1 root6Node0Domains2
    root6Node0Domains1Fast root6Node0Domains2Fast
    root6Node0Domains1_fast_eq root6Node0Domains2_fast_eq (by decide)
theorem root6Node0Step2Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root6Node0Domains1 root6Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains1 root6Node0Domains2
    root6Node0Domains1Fast root6Node0Domains2Fast
    root6Node0Domains1_fast_eq root6Node0Domains2_fast_eq (by decide)
theorem root6Node0Step2Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root6Node0Domains1 root6Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains1 root6Node0Domains2
    root6Node0Domains1Fast root6Node0Domains2Fast
    root6Node0Domains1_fast_eq root6Node0Domains2_fast_eq (by decide)
theorem root6Node0Step2Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root6Node0Domains1 root6Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains1 root6Node0Domains2
    root6Node0Domains1Fast root6Node0Domains2Fast
    root6Node0Domains1_fast_eq root6Node0Domains2_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFive
