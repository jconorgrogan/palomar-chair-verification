module

public import SpectreFinite.RadiusFiveRoot0Part2Segment01
public import SpectreFinite.RadiusFiveRoot0Part1
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable2
public import SpectreFinite.RadiusFiveTable46
public import SpectreFinite.RadiusFiveTable65
public import SpectreFinite.RadiusFiveTable8

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
theorem root0Node1Step4Chunk7_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_5⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk8_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_0⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk8_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_1⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk8_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_2⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk8_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_3⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk8_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_4⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk8_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_5⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Narrowing_checked :
    checkNarrowing table2 root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_flatten table2Scope [table2Rows0_0,table2Rows0_1,table2Rows0_2,table2Rows0_3,table2Rows0_4,table2Rows0_5,table2Rows1_0,table2Rows1_1,table2Rows1_2,table2Rows1_3,table2Rows1_4,table2Rows1_5,table2Rows2_0,table2Rows2_1,table2Rows2_2,table2Rows2_3,table2Rows2_4,table2Rows2_5,table2Rows3_0,table2Rows3_1,table2Rows3_2,table2Rows3_3,table2Rows3_4,table2Rows3_5,table2Rows4_0,table2Rows4_1,table2Rows4_2,table2Rows4_3,table2Rows4_4,table2Rows4_5,table2Rows5_0,table2Rows5_1,table2Rows5_2,table2Rows5_3,table2Rows5_4,table2Rows5_5,table2Rows6_0,table2Rows6_1,table2Rows6_2,table2Rows6_3,table2Rows6_4,table2Rows6_5,table2Rows7_0,table2Rows7_1,table2Rows7_2,table2Rows7_3,table2Rows7_4,table2Rows7_5,table2Rows8_0,table2Rows8_1,table2Rows8_2,table2Rows8_3,table2Rows8_4,table2Rows8_5]
    root0Node1Domains3 root0Node1Domains4 (by
      simp only [List.all_cons, List.all_nil, root0Node1Step4Chunk0_0_checked, root0Node1Step4Chunk0_1_checked, root0Node1Step4Chunk0_2_checked, root0Node1Step4Chunk0_3_checked, root0Node1Step4Chunk0_4_checked, root0Node1Step4Chunk0_5_checked, root0Node1Step4Chunk1_0_checked, root0Node1Step4Chunk1_1_checked, root0Node1Step4Chunk1_2_checked, root0Node1Step4Chunk1_3_checked, root0Node1Step4Chunk1_4_checked, root0Node1Step4Chunk1_5_checked, root0Node1Step4Chunk2_0_checked, root0Node1Step4Chunk2_1_checked, root0Node1Step4Chunk2_2_checked, root0Node1Step4Chunk2_3_checked, root0Node1Step4Chunk2_4_checked, root0Node1Step4Chunk2_5_checked, root0Node1Step4Chunk3_0_checked, root0Node1Step4Chunk3_1_checked, root0Node1Step4Chunk3_2_checked, root0Node1Step4Chunk3_3_checked, root0Node1Step4Chunk3_4_checked, root0Node1Step4Chunk3_5_checked, root0Node1Step4Chunk4_0_checked, root0Node1Step4Chunk4_1_checked, root0Node1Step4Chunk4_2_checked, root0Node1Step4Chunk4_3_checked, root0Node1Step4Chunk4_4_checked, root0Node1Step4Chunk4_5_checked, root0Node1Step4Chunk5_0_checked, root0Node1Step4Chunk5_1_checked, root0Node1Step4Chunk5_2_checked, root0Node1Step4Chunk5_3_checked, root0Node1Step4Chunk5_4_checked, root0Node1Step4Chunk5_5_checked, root0Node1Step4Chunk6_0_checked, root0Node1Step4Chunk6_1_checked, root0Node1Step4Chunk6_2_checked, root0Node1Step4Chunk6_3_checked, root0Node1Step4Chunk6_4_checked, root0Node1Step4Chunk6_5_checked, root0Node1Step4Chunk7_0_checked, root0Node1Step4Chunk7_1_checked, root0Node1Step4Chunk7_2_checked, root0Node1Step4Chunk7_3_checked, root0Node1Step4Chunk7_4_checked, root0Node1Step4Chunk7_5_checked, root0Node1Step4Chunk8_0_checked, root0Node1Step4Chunk8_1_checked, root0Node1Step4Chunk8_2_checked, root0Node1Step4Chunk8_3_checked, root0Node1Step4Chunk8_4_checked, root0Node1Step4Chunk8_5_checked, Bool.true_and])
theorem root0Node1Step4_checked :
    checkReplacement table2 root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq
    root0Node1Step4Narrowing_checked (by decide)
def root0Node2Domains0 : Domains 91 State := restrict root0Node1Domains4 5 (7,4)
def root0Node2Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(4,5),(8,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(8,1)]
  | 12 => some [(1,5),(6,5)]
  | 13 => some [(0,0),(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(4,2)]
  | 18 => some [(5,3)]
  | 19 => some [(8,5)]
  | 20 => some [(7,0)]
  | 21 => some [(0,2),(1,5)]
  | 22 => some [(1,1),(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(7,4)]
  | 27 => some [(6,3)]
  | 28 => some [(7,2)]
  | 29 => some [(7,4)]
  | 30 => some [(5,2),(5,5)]
  | 31 => some [(7,0),(8,0)]
  | 32 => some [(8,3)]
  | 33 => some [(5,5)]
  | 34 => some [(1,0)]
  | 35 => some [(2,1)]
  | 36 => some [(0,2)]
  | 37 => some [(1,1)]
  | 38 => some [(4,1)]
  | 39 => some [(0,2)]
  | 40 => some [(0,4),(0,5),(6,2)]
  | 41 => some [(4,4),(5,4),(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(0,5)]
  | 44 => some [(4,4)]
  | 45 => some [(0,0)]
  | 46 => some [(3,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(5,2)]
  | 50 => some [(5,0),(8,0)]
  | 51 => some [(4,3),(7,1)]
  | 52 => some [(7,5)]
  | 53 => some [(6,0)]
  | 54 => some [(7,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(8,4)]
  | 61 => some [(1,3),(7,3)]
  | 62 => some [(8,2)]
  | 63 => some [(5,0)]
  | 64 => some [(4,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(0,4),(1,2),(6,2)]
  | 71 => some [(5,4),(8,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3),(6,3)]
  | 76 => some [(7,2),(8,2)]
  | 77 => some [(4,0),(5,0),(8,0)]
  | 78 => some [(4,3),(7,1),(8,1)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(4,1),(8,1)]
  | 82 => some [(0,2),(6,5)]
  | 83 => some [(0,4),(1,1)]
  | 84 => some [(5,1),(5,4)]
  | 85 => some [(0,5),(4,5),(5,5),(8,5)]
  | 86 => some [(2,0),(7,0)]
  | 87 => some [(7,3),(8,3)]
  | 88 => some [(5,2),(5,5),(8,5)]
  | 89 => some [(7,0),(8,0)]
  | _ => some [(4,3),(8,3)]
theorem root0Node2Domains0_fast_eq : root0Node2Domains0 = expandDomains root0Node2Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node2Domains0 v = expandDomains root0Node2Domains0Fast v from by decide) v
def root0Node2Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(8,5)]
  | 7 => [(1,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(0,3)]
  | 11 => [(8,1)]
  | 12 => [(6,5)]
  | 13 => [(6,3)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(4,2)]
  | 18 => [(5,3)]
  | 19 => [(8,5)]
  | 20 => [(7,0)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(7,4)]
  | 27 => [(6,3)]
  | 28 => [(7,2)]
  | 29 => [(7,4)]
  | 30 => [(5,2),(5,5)]
  | 31 => [(8,0)]
  | 32 => [(8,3)]
  | 33 => [(5,5)]
  | 34 => [(1,0)]
  | 35 => [(2,1)]
  | 36 => [(0,2)]
  | 37 => [(1,1)]
  | 38 => [(4,1)]
  | 39 => [(0,2)]
  | 40 => [(0,4),(0,5),(6,2)]
  | 41 => [(4,4),(5,4),(8,4)]
  | 42 => [(1,4)]
  | 43 => [(0,5)]
  | 44 => [(4,4)]
  | 45 => [(0,0)]
  | 46 => [(3,2)]
  | 47 => [(4,0)]
  | 48 => [(7,3)]
  | 49 => [(5,2)]
  | 50 => [(5,0),(8,0)]
  | 51 => [(4,3),(7,1)]
  | 52 => [(7,5)]
  | 53 => [(6,0)]
  | 54 => [(7,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(5,1)]
  | 58 => [(0,1)]
  | 59 => [(6,2)]
  | 60 => [(8,4)]
  | 61 => [(1,3),(7,3)]
  | 62 => [(8,2)]
  | 63 => [(5,0)]
  | 64 => [(4,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(8,5)]
  | 68 => [(1,0)]
  | 69 => [(7,1)]
  | 70 => [(0,4),(1,2),(6,2)]
  | 71 => [(5,4),(8,4)]
  | 72 => [(0,0)]
  | 73 => [(7,2)]
  | 74 => [(7,4)]
  | 75 => [(1,3),(6,3)]
  | 76 => [(7,2),(8,2)]
  | 77 => [(4,0),(5,0),(8,0)]
  | 78 => [(4,3),(7,1),(8,1)]
  | 79 => [(1,5)]
  | 80 => [(6,1)]
  | 81 => [(4,1),(8,1)]
  | 82 => [(0,2),(6,5)]
  | 83 => [(0,4),(1,1)]
  | 84 => [(5,1),(5,4)]
  | 85 => [(0,5),(4,5),(5,5),(8,5)]
  | 86 => [(2,0),(7,0)]
  | 87 => [(7,3),(8,3)]
  | 88 => [(5,2),(5,5),(8,5)]
  | 89 => [(7,0),(8,0)]
  | _ => [(4,3),(8,3)]
def root0Node2Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(8,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(8,1)]
  | 12 => some [(6,5)]
  | 13 => some [(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(4,2)]
  | 18 => some [(5,3)]
  | 19 => some [(8,5)]
  | 20 => some [(7,0)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(7,4)]
  | 27 => some [(6,3)]
  | 28 => some [(7,2)]
  | 29 => some [(7,4)]
  | 30 => some [(5,2),(5,5)]
  | 31 => some [(8,0)]
  | 32 => some [(8,3)]
  | 33 => some [(5,5)]
  | 34 => some [(1,0)]
  | 35 => some [(2,1)]
  | 36 => some [(0,2)]
  | 37 => some [(1,1)]
  | 38 => some [(4,1)]
  | 39 => some [(0,2)]
  | 40 => some [(0,4),(0,5),(6,2)]
  | 41 => some [(4,4),(5,4),(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(0,5)]
  | 44 => some [(4,4)]
  | 45 => some [(0,0)]
  | 46 => some [(3,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(5,2)]
  | 50 => some [(5,0),(8,0)]
  | 51 => some [(4,3),(7,1)]
  | 52 => some [(7,5)]
  | 53 => some [(6,0)]
  | 54 => some [(7,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(8,4)]
  | 61 => some [(1,3),(7,3)]
  | 62 => some [(8,2)]
  | 63 => some [(5,0)]
  | 64 => some [(4,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(0,4),(1,2),(6,2)]
  | 71 => some [(5,4),(8,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3),(6,3)]
  | 76 => some [(7,2),(8,2)]
  | 77 => some [(4,0),(5,0),(8,0)]
  | 78 => some [(4,3),(7,1),(8,1)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(4,1),(8,1)]
  | 82 => some [(0,2),(6,5)]
  | 83 => some [(0,4),(1,1)]
  | 84 => some [(5,1),(5,4)]
  | 85 => some [(0,5),(4,5),(5,5),(8,5)]
  | 86 => some [(2,0),(7,0)]
  | 87 => some [(7,3),(8,3)]
  | 88 => some [(5,2),(5,5),(8,5)]
  | 89 => some [(7,0),(8,0)]
  | _ => some [(4,3),(8,3)]
theorem root0Node2Domains1_fast_eq : root0Node2Domains1 = expandDomains root0Node2Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node2Domains1 v = expandDomains root0Node2Domains1Fast v from by decide) v
theorem root0Node2Step1Chunk0_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_0⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk0_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_1⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk0_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_2⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk0_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_3⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk0_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_4⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk0_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_5⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk1_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_0⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk1_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_1⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk1_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_2⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk1_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_3⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFive
