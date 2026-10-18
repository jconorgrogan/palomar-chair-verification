module

public import SpectreFinite.RadiusFiveRoot0Part2Segment06
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
theorem root0Node2Step2Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root0Node2Domains1 root0Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains1 root0Node2Domains2
    root0Node2Domains1Fast root0Node2Domains2Fast
    root0Node2Domains1_fast_eq root0Node2Domains2_fast_eq (by decide)
theorem root0Node2Step2Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root0Node2Domains1 root0Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains1 root0Node2Domains2
    root0Node2Domains1Fast root0Node2Domains2Fast
    root0Node2Domains1_fast_eq root0Node2Domains2_fast_eq (by decide)
theorem root0Node2Step2Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root0Node2Domains1 root0Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains1 root0Node2Domains2
    root0Node2Domains1Fast root0Node2Domains2Fast
    root0Node2Domains1_fast_eq root0Node2Domains2_fast_eq (by decide)
theorem root0Node2Step2Narrowing_checked :
    checkNarrowing table46 root0Node2Domains1 root0Node2Domains2 = true := by
  exact checkNarrowing_flatten table46Scope [table46Rows0_0,table46Rows0_1,table46Rows0_2,table46Rows0_3,table46Rows0_4,table46Rows0_5,table46Rows1_0,table46Rows1_1,table46Rows1_2,table46Rows1_3,table46Rows1_4,table46Rows1_5,table46Rows2_0,table46Rows2_1,table46Rows2_2,table46Rows2_3,table46Rows2_4,table46Rows2_5,table46Rows3_0,table46Rows3_1,table46Rows3_2,table46Rows3_3,table46Rows3_4,table46Rows3_5,table46Rows4_0,table46Rows4_1,table46Rows4_2,table46Rows4_3,table46Rows4_4,table46Rows4_5,table46Rows5_0,table46Rows5_1,table46Rows5_2,table46Rows5_3,table46Rows5_4,table46Rows5_5,table46Rows6_0,table46Rows6_1,table46Rows6_2,table46Rows6_3,table46Rows6_4,table46Rows6_5,table46Rows7_0,table46Rows7_1,table46Rows7_2,table46Rows7_3,table46Rows7_4,table46Rows7_5,table46Rows8_0,table46Rows8_1,table46Rows8_2,table46Rows8_3,table46Rows8_4,table46Rows8_5]
    root0Node2Domains1 root0Node2Domains2 (by
      simp only [List.all_cons, List.all_nil, root0Node2Step2Chunk0_0_checked, root0Node2Step2Chunk0_1_checked, root0Node2Step2Chunk0_2_checked, root0Node2Step2Chunk0_3_checked, root0Node2Step2Chunk0_4_checked, root0Node2Step2Chunk0_5_checked, root0Node2Step2Chunk1_0_checked, root0Node2Step2Chunk1_1_checked, root0Node2Step2Chunk1_2_checked, root0Node2Step2Chunk1_3_checked, root0Node2Step2Chunk1_4_checked, root0Node2Step2Chunk1_5_checked, root0Node2Step2Chunk2_0_checked, root0Node2Step2Chunk2_1_checked, root0Node2Step2Chunk2_2_checked, root0Node2Step2Chunk2_3_checked, root0Node2Step2Chunk2_4_checked, root0Node2Step2Chunk2_5_checked, root0Node2Step2Chunk3_0_checked, root0Node2Step2Chunk3_1_checked, root0Node2Step2Chunk3_2_checked, root0Node2Step2Chunk3_3_checked, root0Node2Step2Chunk3_4_checked, root0Node2Step2Chunk3_5_checked, root0Node2Step2Chunk4_0_checked, root0Node2Step2Chunk4_1_checked, root0Node2Step2Chunk4_2_checked, root0Node2Step2Chunk4_3_checked, root0Node2Step2Chunk4_4_checked, root0Node2Step2Chunk4_5_checked, root0Node2Step2Chunk5_0_checked, root0Node2Step2Chunk5_1_checked, root0Node2Step2Chunk5_2_checked, root0Node2Step2Chunk5_3_checked, root0Node2Step2Chunk5_4_checked, root0Node2Step2Chunk5_5_checked, root0Node2Step2Chunk6_0_checked, root0Node2Step2Chunk6_1_checked, root0Node2Step2Chunk6_2_checked, root0Node2Step2Chunk6_3_checked, root0Node2Step2Chunk6_4_checked, root0Node2Step2Chunk6_5_checked, root0Node2Step2Chunk7_0_checked, root0Node2Step2Chunk7_1_checked, root0Node2Step2Chunk7_2_checked, root0Node2Step2Chunk7_3_checked, root0Node2Step2Chunk7_4_checked, root0Node2Step2Chunk7_5_checked, root0Node2Step2Chunk8_0_checked, root0Node2Step2Chunk8_1_checked, root0Node2Step2Chunk8_2_checked, root0Node2Step2Chunk8_3_checked, root0Node2Step2Chunk8_4_checked, root0Node2Step2Chunk8_5_checked, Bool.true_and])
theorem root0Node2Step2_checked :
    checkReplacement table46 root0Node2Domains1 root0Node2Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root0Node2Domains1 root0Node2Domains2
    root0Node2Domains1Fast root0Node2Domains2Fast
    root0Node2Domains1_fast_eq root0Node2Domains2_fast_eq
    root0Node2Step2Narrowing_checked (by decide)
def root0Node2Domains3 (v : Fin 91) : List State :=
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
  | 50 => [(5,0)]
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
  | 61 => [(7,3)]
  | 62 => [(8,2)]
  | 63 => [(5,0)]
  | 64 => [(4,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(8,5)]
  | 68 => [(1,0)]
  | 69 => [(7,1)]
  | 70 => [(1,2)]
  | 71 => [(8,4)]
  | 72 => [(0,0)]
  | 73 => [(7,2)]
  | 74 => [(7,4)]
  | 75 => [(1,3)]
  | 76 => [(8,2)]
  | 77 => [(5,0)]
  | 78 => [(8,1)]
  | 79 => [(1,5)]
  | 80 => [(6,1)]
  | 81 => [(8,1)]
  | 82 => [(6,5)]
  | 83 => [(0,4)]
  | 84 => [(5,4)]
  | 85 => [(5,5)]
  | 86 => [(7,0)]
  | 87 => [(8,3)]
  | 88 => [(5,5)]
  | 89 => [(7,0)]
  | _ => [(4,3)]
def root0Node2Domains3Fast (v : Fin 91) : Option (List State) :=
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
  | 50 => some [(5,0)]
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
  | 61 => some [(7,3)]
  | 62 => some [(8,2)]
  | 63 => some [(5,0)]
  | 64 => some [(4,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(1,2)]
  | 71 => some [(8,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3)]
  | 76 => some [(8,2)]
  | 77 => some [(5,0)]
  | 78 => some [(8,1)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(8,1)]
  | 82 => some [(6,5)]
  | 83 => some [(0,4)]
  | 84 => some [(5,4)]
  | 85 => some [(5,5)]
  | 86 => some [(7,0)]
  | 87 => some [(8,3)]
  | 88 => some [(5,5)]
  | 89 => some [(7,0)]
  | _ => some [(4,3)]
theorem root0Node2Domains3_fast_eq : root0Node2Domains3 = expandDomains root0Node2Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node2Domains3 v = expandDomains root0Node2Domains3Fast v from by decide) v
theorem root0Node2Step3Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root0Node2Domains2 root0Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains2 root0Node2Domains3
    root0Node2Domains2Fast root0Node2Domains3Fast
    root0Node2Domains2_fast_eq root0Node2Domains3_fast_eq (by decide)
theorem root0Node2Step3Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root0Node2Domains2 root0Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains2 root0Node2Domains3
    root0Node2Domains2Fast root0Node2Domains3Fast
    root0Node2Domains2_fast_eq root0Node2Domains3_fast_eq (by decide)
theorem root0Node2Step3Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root0Node2Domains2 root0Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains2 root0Node2Domains3
    root0Node2Domains2Fast root0Node2Domains3Fast
    root0Node2Domains2_fast_eq root0Node2Domains3_fast_eq (by decide)
theorem root0Node2Step3Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root0Node2Domains2 root0Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains2 root0Node2Domains3
    root0Node2Domains2Fast root0Node2Domains3Fast
    root0Node2Domains2_fast_eq root0Node2Domains3_fast_eq (by decide)
theorem root0Node2Step3Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root0Node2Domains2 root0Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains2 root0Node2Domains3
    root0Node2Domains2Fast root0Node2Domains3Fast
    root0Node2Domains2_fast_eq root0Node2Domains3_fast_eq (by decide)
theorem root0Node2Step3Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root0Node2Domains2 root0Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains2 root0Node2Domains3
    root0Node2Domains2Fast root0Node2Domains3Fast
    root0Node2Domains2_fast_eq root0Node2Domains3_fast_eq (by decide)
theorem root0Node2Step3Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root0Node2Domains2 root0Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains2 root0Node2Domains3
    root0Node2Domains2Fast root0Node2Domains3Fast
    root0Node2Domains2_fast_eq root0Node2Domains3_fast_eq (by decide)
theorem root0Node2Step3Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root0Node2Domains2 root0Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains2 root0Node2Domains3
    root0Node2Domains2Fast root0Node2Domains3Fast
    root0Node2Domains2_fast_eq root0Node2Domains3_fast_eq (by decide)
theorem root0Node2Step3Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root0Node2Domains2 root0Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains2 root0Node2Domains3
    root0Node2Domains2Fast root0Node2Domains3Fast
    root0Node2Domains2_fast_eq root0Node2Domains3_fast_eq (by decide)
theorem root0Node2Step3Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root0Node2Domains2 root0Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains2 root0Node2Domains3
    root0Node2Domains2Fast root0Node2Domains3Fast
    root0Node2Domains2_fast_eq root0Node2Domains3_fast_eq (by decide)
theorem root0Node2Step3Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root0Node2Domains2 root0Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains2 root0Node2Domains3
    root0Node2Domains2Fast root0Node2Domains3Fast
    root0Node2Domains2_fast_eq root0Node2Domains3_fast_eq (by decide)
theorem root0Node2Step3Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root0Node2Domains2 root0Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains2 root0Node2Domains3
    root0Node2Domains2Fast root0Node2Domains3Fast
    root0Node2Domains2_fast_eq root0Node2Domains3_fast_eq (by decide)
theorem root0Node2Step3Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root0Node2Domains2 root0Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains2 root0Node2Domains3
    root0Node2Domains2Fast root0Node2Domains3Fast
    root0Node2Domains2_fast_eq root0Node2Domains3_fast_eq (by decide)
theorem root0Node2Step3Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root0Node2Domains2 root0Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains2 root0Node2Domains3
    root0Node2Domains2Fast root0Node2Domains3Fast
    root0Node2Domains2_fast_eq root0Node2Domains3_fast_eq (by decide)
theorem root0Node2Step3Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root0Node2Domains2 root0Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains2 root0Node2Domains3
    root0Node2Domains2Fast root0Node2Domains3Fast
    root0Node2Domains2_fast_eq root0Node2Domains3_fast_eq (by decide)
theorem root0Node2Step3Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root0Node2Domains2 root0Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains2 root0Node2Domains3
    root0Node2Domains2Fast root0Node2Domains3Fast
    root0Node2Domains2_fast_eq root0Node2Domains3_fast_eq (by decide)
theorem root0Node2Step3Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root0Node2Domains2 root0Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains2 root0Node2Domains3
    root0Node2Domains2Fast root0Node2Domains3Fast
    root0Node2Domains2_fast_eq root0Node2Domains3_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFive
