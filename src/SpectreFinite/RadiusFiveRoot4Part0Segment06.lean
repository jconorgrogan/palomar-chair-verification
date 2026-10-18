module

public import SpectreFinite.RadiusFiveRoot4Part0Segment05
public import SpectreFinite.RadiusFiveRoot4Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable12
public import SpectreFinite.RadiusFiveTable33
public import SpectreFinite.RadiusFiveTable51
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
theorem root4Node0Step2Chunk7_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_0⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk7_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_1⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk7_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_2⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk7_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_3⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk7_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_4⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk7_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_5⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk8_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_0⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk8_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_1⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk8_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_2⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk8_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_3⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk8_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_4⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk8_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_5⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Narrowing_checked :
    checkNarrowing table33 root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_flatten table33Scope [table33Rows0_0,table33Rows0_1,table33Rows0_2,table33Rows0_3,table33Rows0_4,table33Rows0_5,table33Rows1_0,table33Rows1_1,table33Rows1_2,table33Rows1_3,table33Rows1_4,table33Rows1_5,table33Rows2_0,table33Rows2_1,table33Rows2_2,table33Rows2_3,table33Rows2_4,table33Rows2_5,table33Rows3_0,table33Rows3_1,table33Rows3_2,table33Rows3_3,table33Rows3_4,table33Rows3_5,table33Rows4_0,table33Rows4_1,table33Rows4_2,table33Rows4_3,table33Rows4_4,table33Rows4_5,table33Rows5_0,table33Rows5_1,table33Rows5_2,table33Rows5_3,table33Rows5_4,table33Rows5_5,table33Rows6_0,table33Rows6_1,table33Rows6_2,table33Rows6_3,table33Rows6_4,table33Rows6_5,table33Rows7_0,table33Rows7_1,table33Rows7_2,table33Rows7_3,table33Rows7_4,table33Rows7_5,table33Rows8_0,table33Rows8_1,table33Rows8_2,table33Rows8_3,table33Rows8_4,table33Rows8_5]
    root4Node0Domains1 root4Node0Domains2 (by
      simp only [List.all_cons, List.all_nil, root4Node0Step2Chunk0_0_checked, root4Node0Step2Chunk0_1_checked, root4Node0Step2Chunk0_2_checked, root4Node0Step2Chunk0_3_checked, root4Node0Step2Chunk0_4_checked, root4Node0Step2Chunk0_5_checked, root4Node0Step2Chunk1_0_checked, root4Node0Step2Chunk1_1_checked, root4Node0Step2Chunk1_2_checked, root4Node0Step2Chunk1_3_checked, root4Node0Step2Chunk1_4_checked, root4Node0Step2Chunk1_5_checked, root4Node0Step2Chunk2_0_checked, root4Node0Step2Chunk2_1_checked, root4Node0Step2Chunk2_2_checked, root4Node0Step2Chunk2_3_checked, root4Node0Step2Chunk2_4_checked, root4Node0Step2Chunk2_5_checked, root4Node0Step2Chunk3_0_checked, root4Node0Step2Chunk3_1_checked, root4Node0Step2Chunk3_2_checked, root4Node0Step2Chunk3_3_checked, root4Node0Step2Chunk3_4_checked, root4Node0Step2Chunk3_5_checked, root4Node0Step2Chunk4_0_checked, root4Node0Step2Chunk4_1_checked, root4Node0Step2Chunk4_2_checked, root4Node0Step2Chunk4_3_checked, root4Node0Step2Chunk4_4_checked, root4Node0Step2Chunk4_5_checked, root4Node0Step2Chunk5_0_checked, root4Node0Step2Chunk5_1_checked, root4Node0Step2Chunk5_2_checked, root4Node0Step2Chunk5_3_checked, root4Node0Step2Chunk5_4_checked, root4Node0Step2Chunk5_5_checked, root4Node0Step2Chunk6_0_checked, root4Node0Step2Chunk6_1_checked, root4Node0Step2Chunk6_2_checked, root4Node0Step2Chunk6_3_checked, root4Node0Step2Chunk6_4_checked, root4Node0Step2Chunk6_5_checked, root4Node0Step2Chunk7_0_checked, root4Node0Step2Chunk7_1_checked, root4Node0Step2Chunk7_2_checked, root4Node0Step2Chunk7_3_checked, root4Node0Step2Chunk7_4_checked, root4Node0Step2Chunk7_5_checked, root4Node0Step2Chunk8_0_checked, root4Node0Step2Chunk8_1_checked, root4Node0Step2Chunk8_2_checked, root4Node0Step2Chunk8_3_checked, root4Node0Step2Chunk8_4_checked, root4Node0Step2Chunk8_5_checked, Bool.true_and])
theorem root4Node0Step2_checked :
    checkReplacement table33 root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq
    root4Node0Step2Narrowing_checked (by decide)
def root4Node0Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 1 => [(0,0),(0,5),(6,2),(6,3),(6,4)]
  | 2 => [(1,2),(4,4),(7,2),(8,4)]
  | 3 => [(1,4),(7,4),(8,4)]
  | 4 => [(0,0),(0,5),(1,3),(6,3)]
  | 5 => [(4,4),(7,2),(8,2)]
  | 6 => [(2,1),(2,3),(2,5),(4,3),(4,5),(7,1)]
  | 7 => [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 8 => [(0,3),(1,1),(6,1),(7,1)]
  | 9 => [(4,1),(7,5),(8,1)]
  | 10 => [(0,2),(1,5),(6,0),(6,5)]
  | 11 => [(0,4),(1,1),(6,1),(7,1)]
  | 12 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 13 => [(0,0),(1,4),(4,0),(6,4),(7,4)]
  | 14 => [(0,5),(1,2),(1,3),(3,2),(6,3),(7,2),(7,3)]
  | 15 => [(2,0),(2,2),(4,0),(4,2)]
  | 16 => [(3,3),(5,3),(7,3)]
  | 17 => [(5,2),(5,5),(8,2),(8,5)]
  | 18 => [(7,0),(8,0)]
  | 19 => [(4,3),(7,3),(8,3)]
  | 20 => [(1,5),(3,5),(4,2),(5,2),(5,5),(7,5),(8,2),(8,5)]
  | 21 => [(1,5),(4,1),(5,1),(7,5),(8,1)]
  | 22 => [(0,1),(0,2),(0,3),(6,0),(6,1),(6,5)]
  | 23 => [(0,4),(1,1),(3,1),(5,1),(6,2)]
  | 24 => [(0,1),(1,4),(3,4),(7,4)]
  | 25 => [(0,5),(6,2),(6,3)]
  | 26 => [(4,4),(7,2),(8,4)]
  | 27 => [(1,4),(6,4),(7,4)]
  | 28 => [(0,5),(1,2),(6,3)]
  | 29 => [(2,0),(2,2),(2,4),(4,4),(7,2),(7,4),(8,4)]
  | 30 => [(4,5),(7,3),(8,3),(8,5)]
  | 31 => [(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 32 => [(1,0),(3,0),(5,0),(5,3),(7,0),(8,3)]
  | 33 => [(2,1),(2,3),(2,5),(4,5),(8,5)]
  | 34 => [(0,2),(1,0),(6,0)]
  | 35 => [(1,1),(7,1)]
  | 36 => [(4,1),(7,5)]
  | 37 => [(0,2),(0,3),(6,0)]
  | 38 => [(1,1),(3,1),(7,1),(8,1)]
  | 39 => [(0,1),(1,5),(4,1),(5,1),(6,5),(7,5),(8,1)]
  | 40 => [(0,0),(0,1),(1,4),(6,3),(6,4)]
  | 41 => [(0,5),(1,2),(6,2),(7,2)]
  | 42 => [(4,4),(7,4),(8,4)]
  | 43 => [(0,0),(6,3),(6,4)]
  | 44 => [(1,2),(3,2),(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2),(5,2),(8,2)]
  | 48 => [(5,0),(5,3),(8,0)]
  | 49 => [(4,5),(7,3),(8,3),(8,5)]
  | 50 => [(1,0),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 51 => [(0,3),(1,0),(1,1),(6,0),(6,1)]
  | 52 => [(4,1),(7,1),(8,1)]
  | 53 => [(0,2),(1,5),(7,5)]
  | 54 => [(0,3),(1,1),(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(7,4),(8,4)]
  | 59 => [(0,0),(1,4),(6,3),(6,4)]
  | 60 => [(0,5),(1,2),(7,2)]
  | 61 => [(1,3),(3,3),(5,0),(5,3),(7,3),(8,0)]
  | 62 => [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 63 => [(4,2),(7,0),(8,0)]
  | 64 => [(5,3),(8,3)]
  | 65 => [(5,5),(8,5)]
  | 66 => [(1,0)]
  | 67 => [(2,1),(7,1)]
  | 68 => [(0,2),(1,5),(7,5)]
  | 69 => [(0,3),(1,1),(6,0),(6,1)]
  | 70 => [(0,0),(0,4),(0,5),(6,2),(6,3),(6,4)]
  | 71 => [(1,2),(4,4),(5,4),(7,2),(8,4)]
  | 72 => [(1,4),(7,4)]
  | 73 => [(0,5),(1,3),(6,3)]
  | 74 => [(4,4),(7,2),(8,2)]
  | 75 => [(0,0),(4,0),(5,0),(8,0)]
  | 76 => [(3,2),(4,5),(7,3)]
  | 77 => [(4,0),(4,2),(7,0),(8,2)]
  | 78 => stateChoices
  | 79 => [(4,1),(7,5),(8,1)]
  | 80 => [(0,2),(6,0),(6,5)]
  | 81 => [(0,4),(1,1),(7,1)]
  | 82 => [(1,5),(5,1),(5,4)]
  | 83 => [(0,0),(0,1),(6,1),(6,4)]
  | 84 => [(1,2),(5,1),(6,2),(7,2)]
  | 85 => stateChoices
  | 86 => [(5,2),(5,5),(8,2),(8,5)]
  | 87 => [(5,0),(7,0),(8,0)]
  | 88 => [(4,3),(4,5),(8,3)]
  | 89 => [(1,5),(3,5),(5,5),(7,0),(7,5)]
  | _ => [(0,3),(1,0),(6,1),(8,3)]
def root4Node0Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 1 => some [(0,0),(0,5),(6,2),(6,3),(6,4)]
  | 2 => some [(1,2),(4,4),(7,2),(8,4)]
  | 3 => some [(1,4),(7,4),(8,4)]
  | 4 => some [(0,0),(0,5),(1,3),(6,3)]
  | 5 => some [(4,4),(7,2),(8,2)]
  | 6 => some [(2,1),(2,3),(2,5),(4,3),(4,5),(7,1)]
  | 7 => some [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 8 => some [(0,3),(1,1),(6,1),(7,1)]
  | 9 => some [(4,1),(7,5),(8,1)]
  | 10 => some [(0,2),(1,5),(6,0),(6,5)]
  | 11 => some [(0,4),(1,1),(6,1),(7,1)]
  | 12 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 13 => some [(0,0),(1,4),(4,0),(6,4),(7,4)]
  | 14 => some [(0,5),(1,2),(1,3),(3,2),(6,3),(7,2),(7,3)]
  | 15 => some [(2,0),(2,2),(4,0),(4,2)]
  | 16 => some [(3,3),(5,3),(7,3)]
  | 17 => some [(5,2),(5,5),(8,2),(8,5)]
  | 18 => some [(7,0),(8,0)]
  | 19 => some [(4,3),(7,3),(8,3)]
  | 20 => some [(1,5),(3,5),(4,2),(5,2),(5,5),(7,5),(8,2),(8,5)]
  | 21 => some [(1,5),(4,1),(5,1),(7,5),(8,1)]
  | 22 => some [(0,1),(0,2),(0,3),(6,0),(6,1),(6,5)]
  | 23 => some [(0,4),(1,1),(3,1),(5,1),(6,2)]
  | 24 => some [(0,1),(1,4),(3,4),(7,4)]
  | 25 => some [(0,5),(6,2),(6,3)]
  | 26 => some [(4,4),(7,2),(8,4)]
  | 27 => some [(1,4),(6,4),(7,4)]
  | 28 => some [(0,5),(1,2),(6,3)]
  | 29 => some [(2,0),(2,2),(2,4),(4,4),(7,2),(7,4),(8,4)]
  | 30 => some [(4,5),(7,3),(8,3),(8,5)]
  | 31 => some [(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 32 => some [(1,0),(3,0),(5,0),(5,3),(7,0),(8,3)]
  | 33 => some [(2,1),(2,3),(2,5),(4,5),(8,5)]
  | 34 => some [(0,2),(1,0),(6,0)]
  | 35 => some [(1,1),(7,1)]
  | 36 => some [(4,1),(7,5)]
  | 37 => some [(0,2),(0,3),(6,0)]
  | 38 => some [(1,1),(3,1),(7,1),(8,1)]
  | 39 => some [(0,1),(1,5),(4,1),(5,1),(6,5),(7,5),(8,1)]
  | 40 => some [(0,0),(0,1),(1,4),(6,3),(6,4)]
  | 41 => some [(0,5),(1,2),(6,2),(7,2)]
  | 42 => some [(4,4),(7,4),(8,4)]
  | 43 => some [(0,0),(6,3),(6,4)]
  | 44 => some [(1,2),(3,2),(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(5,2),(8,2)]
  | 48 => some [(5,0),(5,3),(8,0)]
  | 49 => some [(4,5),(7,3),(8,3),(8,5)]
  | 50 => some [(1,0),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 51 => some [(0,3),(1,0),(1,1),(6,0),(6,1)]
  | 52 => some [(4,1),(7,1),(8,1)]
  | 53 => some [(0,2),(1,5),(7,5)]
  | 54 => some [(0,3),(1,1),(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(1,4),(6,3),(6,4)]
  | 60 => some [(0,5),(1,2),(7,2)]
  | 61 => some [(1,3),(3,3),(5,0),(5,3),(7,3),(8,0)]
  | 62 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 63 => some [(4,2),(7,0),(8,0)]
  | 64 => some [(5,3),(8,3)]
  | 65 => some [(5,5),(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1),(7,1)]
  | 68 => some [(0,2),(1,5),(7,5)]
  | 69 => some [(0,3),(1,1),(6,0),(6,1)]
  | 70 => some [(0,0),(0,4),(0,5),(6,2),(6,3),(6,4)]
  | 71 => some [(1,2),(4,4),(5,4),(7,2),(8,4)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(1,3),(6,3)]
  | 74 => some [(4,4),(7,2),(8,2)]
  | 75 => some [(0,0),(4,0),(5,0),(8,0)]
  | 76 => some [(3,2),(4,5),(7,3)]
  | 77 => some [(4,0),(4,2),(7,0),(8,2)]
  | 78 => none
  | 79 => some [(4,1),(7,5),(8,1)]
  | 80 => some [(0,2),(6,0),(6,5)]
  | 81 => some [(0,4),(1,1),(7,1)]
  | 82 => some [(1,5),(5,1),(5,4)]
  | 83 => some [(0,0),(0,1),(6,1),(6,4)]
  | 84 => some [(1,2),(5,1),(6,2),(7,2)]
  | 85 => none
  | 86 => some [(5,2),(5,5),(8,2),(8,5)]
  | 87 => some [(5,0),(7,0),(8,0)]
  | 88 => some [(4,3),(4,5),(8,3)]
  | 89 => some [(1,5),(3,5),(5,5),(7,0),(7,5)]
  | _ => some [(0,3),(1,0),(6,1),(8,3)]
theorem root4Node0Domains3_fast_eq : root4Node0Domains3 = expandDomains root4Node0Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node0Domains3 v = expandDomains root4Node0Domains3Fast v from by decide) v
theorem root4Node0Step3Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFive
