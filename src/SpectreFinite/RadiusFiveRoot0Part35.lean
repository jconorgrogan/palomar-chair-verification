module

public import SpectreFinite.RadiusFiveRoot0Part34
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable36
public import SpectreFinite.RadiusFiveTable51
public import SpectreFinite.RadiusFiveTable53
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node80Domains0 : Domains 91 State := restrict root0Node78Domains1 40 (6,2)
def root0Node80Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(1,5)]
  | 10 => some [(6,1)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5)]
  | 14 => some [(4,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(2,0)]
  | 18 => some [(7,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(3,1)]
  | 26 => some [(0,1)]
  | 27 => some [(6,2)]
  | 28 => some [(8,4)]
  | 29 => some [(1,4)]
  | 30 => some [(8,2)]
  | 31 => some [(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(1,0)]
  | 37 => some [(7,1)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(6,2)]
  | 41 => some [(5,4),(8,4)]
  | 42 => some [(6,4)]
  | 43 => some [(1,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(8,2)]
  | 50 => some [(5,0),(8,0)]
  | 51 => some [(4,3),(7,1)]
  | 52 => some [(7,5)]
  | 53 => some [(0,3)]
  | 54 => some [(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(8,4)]
  | 61 => some [(1,3),(7,3)]
  | 62 => some [(4,2)]
  | 63 => some [(5,3)]
  | 64 => some [(8,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(0,4),(1,2),(6,2)]
  | 71 => some [(3,4),(7,4)]
  | 72 => some [(6,3)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3),(6,3)]
  | 76 => some [(7,2),(8,2)]
  | 77 => some [(4,0),(5,0),(8,0)]
  | 78 => some [(2,1),(2,3),(4,1)]
  | 79 => some [(0,2)]
  | 80 => some [(1,1)]
  | 81 => some [(4,1),(8,1)]
  | 82 => some [(0,2),(6,5)]
  | 83 => some [(0,4),(1,1)]
  | 84 => some [(5,1),(5,4)]
  | 85 => some [(1,2),(3,2),(5,2)]
  | 86 => some [(4,0),(8,0)]
  | 87 => some [(7,3),(8,3)]
  | 88 => some [(5,2),(5,5)]
  | 89 => some [(7,0),(8,0)]
  | _ => some [(4,3),(8,3)]
theorem root0Node80Domains0_fast_eq : root0Node80Domains0 = expandDomains root0Node80Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node80Domains0 v = expandDomains root0Node80Domains0Fast v from by decide) v
def root0Node80Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(0,0)]
  | 4 => [(7,2)]
  | 5 => [(7,4)]
  | 6 => [(5,5)]
  | 7 => [(7,0)]
  | 8 => [(4,3)]
  | 9 => [(1,5)]
  | 10 => [(6,1)]
  | 11 => [(4,1)]
  | 12 => [(0,2)]
  | 13 => [(0,5)]
  | 14 => [(4,4)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(2,0)]
  | 18 => [(7,3)]
  | 19 => [(5,2)]
  | 20 => [(8,0)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(3,1)]
  | 26 => [(0,1)]
  | 27 => [(6,2)]
  | 28 => [(8,4)]
  | 29 => [(1,4)]
  | 30 => [(8,2)]
  | 31 => [(8,0)]
  | 32 => [(7,3)]
  | 33 => [(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(1,0)]
  | 37 => [(7,1)]
  | 38 => [(7,5)]
  | 39 => [(6,0)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(6,4)]
  | 43 => [(1,2)]
  | 44 => [(8,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(4,0)]
  | 48 => [(7,3)]
  | 49 => [(8,2)]
  | 50 => [(5,0),(8,0)]
  | 51 => [(7,1)]
  | 52 => [(7,5)]
  | 53 => [(0,3)]
  | 54 => [(8,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(5,1)]
  | 58 => [(0,1)]
  | 59 => [(6,2)]
  | 60 => [(8,4)]
  | 61 => [(7,3)]
  | 62 => [(4,2)]
  | 63 => [(5,3)]
  | 64 => [(8,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(8,5)]
  | 68 => [(1,0)]
  | 69 => [(7,1)]
  | 70 => [(1,2),(6,2)]
  | 71 => [(7,4)]
  | 72 => [(6,3)]
  | 73 => [(7,2)]
  | 74 => [(7,4)]
  | 75 => [(1,3),(6,3)]
  | 76 => [(7,2),(8,2)]
  | 77 => [(4,0),(5,0),(8,0)]
  | 78 => [(2,1),(4,1)]
  | 79 => [(0,2)]
  | 80 => [(1,1)]
  | 81 => [(4,1),(8,1)]
  | 82 => [(0,2),(6,5)]
  | 83 => [(0,4),(1,1)]
  | 84 => [(5,1),(5,4)]
  | 85 => [(3,2),(5,2)]
  | 86 => [(4,0),(8,0)]
  | 87 => [(7,3),(8,3)]
  | 88 => [(5,2),(5,5)]
  | 89 => [(7,0),(8,0)]
  | _ => [(4,3),(8,3)]
def root0Node80Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(1,5)]
  | 10 => some [(6,1)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5)]
  | 14 => some [(4,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(2,0)]
  | 18 => some [(7,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(3,1)]
  | 26 => some [(0,1)]
  | 27 => some [(6,2)]
  | 28 => some [(8,4)]
  | 29 => some [(1,4)]
  | 30 => some [(8,2)]
  | 31 => some [(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(1,0)]
  | 37 => some [(7,1)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(6,4)]
  | 43 => some [(1,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(8,2)]
  | 50 => some [(5,0),(8,0)]
  | 51 => some [(7,1)]
  | 52 => some [(7,5)]
  | 53 => some [(0,3)]
  | 54 => some [(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(8,4)]
  | 61 => some [(7,3)]
  | 62 => some [(4,2)]
  | 63 => some [(5,3)]
  | 64 => some [(8,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(1,2),(6,2)]
  | 71 => some [(7,4)]
  | 72 => some [(6,3)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3),(6,3)]
  | 76 => some [(7,2),(8,2)]
  | 77 => some [(4,0),(5,0),(8,0)]
  | 78 => some [(2,1),(4,1)]
  | 79 => some [(0,2)]
  | 80 => some [(1,1)]
  | 81 => some [(4,1),(8,1)]
  | 82 => some [(0,2),(6,5)]
  | 83 => some [(0,4),(1,1)]
  | 84 => some [(5,1),(5,4)]
  | 85 => some [(3,2),(5,2)]
  | 86 => some [(4,0),(8,0)]
  | 87 => some [(7,3),(8,3)]
  | 88 => some [(5,2),(5,5)]
  | 89 => some [(7,0),(8,0)]
  | _ => some [(4,3),(8,3)]
theorem root0Node80Domains1_fast_eq : root0Node80Domains1 = expandDomains root0Node80Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node80Domains1 v = expandDomains root0Node80Domains1Fast v from by decide) v
theorem root0Node80Step1Chunk0_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_0⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk0_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_1⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk0_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_2⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk0_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_3⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk0_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_4⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk0_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_5⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk1_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_0⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk1_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_1⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk1_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_2⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk1_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_3⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk1_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_4⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk1_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_5⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk2_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_0⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk2_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_1⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk2_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_2⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk2_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_3⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk2_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_4⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk2_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_5⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk3_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_0⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk3_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_1⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk3_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_2⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk3_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_3⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk3_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_4⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk3_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_5⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk4_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_0⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk4_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_1⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk4_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_2⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk4_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_3⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk4_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_4⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk4_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_5⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk5_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_0⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk5_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_1⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk5_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_2⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk5_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_3⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk5_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_4⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk5_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_5⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk6_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_0⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk6_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_1⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk6_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_2⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk6_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_3⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk6_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_4⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk6_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_5⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk7_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_0⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk7_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_1⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk7_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_2⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk7_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_3⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk7_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_4⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk7_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_5⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk8_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_0⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk8_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_1⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk8_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_2⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk8_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_3⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk8_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_4⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Chunk8_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_5⟩
      root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq (by decide)
theorem root0Node80Step1Narrowing_checked :
    checkNarrowing table51 root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkNarrowing_flatten table51Scope [table51Rows0_0,table51Rows0_1,table51Rows0_2,table51Rows0_3,table51Rows0_4,table51Rows0_5,table51Rows1_0,table51Rows1_1,table51Rows1_2,table51Rows1_3,table51Rows1_4,table51Rows1_5,table51Rows2_0,table51Rows2_1,table51Rows2_2,table51Rows2_3,table51Rows2_4,table51Rows2_5,table51Rows3_0,table51Rows3_1,table51Rows3_2,table51Rows3_3,table51Rows3_4,table51Rows3_5,table51Rows4_0,table51Rows4_1,table51Rows4_2,table51Rows4_3,table51Rows4_4,table51Rows4_5,table51Rows5_0,table51Rows5_1,table51Rows5_2,table51Rows5_3,table51Rows5_4,table51Rows5_5,table51Rows6_0,table51Rows6_1,table51Rows6_2,table51Rows6_3,table51Rows6_4,table51Rows6_5,table51Rows7_0,table51Rows7_1,table51Rows7_2,table51Rows7_3,table51Rows7_4,table51Rows7_5,table51Rows8_0,table51Rows8_1,table51Rows8_2,table51Rows8_3,table51Rows8_4,table51Rows8_5]
    root0Node80Domains0 root0Node80Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node80Step1Chunk0_0_checked, root0Node80Step1Chunk0_1_checked, root0Node80Step1Chunk0_2_checked, root0Node80Step1Chunk0_3_checked, root0Node80Step1Chunk0_4_checked, root0Node80Step1Chunk0_5_checked, root0Node80Step1Chunk1_0_checked, root0Node80Step1Chunk1_1_checked, root0Node80Step1Chunk1_2_checked, root0Node80Step1Chunk1_3_checked, root0Node80Step1Chunk1_4_checked, root0Node80Step1Chunk1_5_checked, root0Node80Step1Chunk2_0_checked, root0Node80Step1Chunk2_1_checked, root0Node80Step1Chunk2_2_checked, root0Node80Step1Chunk2_3_checked, root0Node80Step1Chunk2_4_checked, root0Node80Step1Chunk2_5_checked, root0Node80Step1Chunk3_0_checked, root0Node80Step1Chunk3_1_checked, root0Node80Step1Chunk3_2_checked, root0Node80Step1Chunk3_3_checked, root0Node80Step1Chunk3_4_checked, root0Node80Step1Chunk3_5_checked, root0Node80Step1Chunk4_0_checked, root0Node80Step1Chunk4_1_checked, root0Node80Step1Chunk4_2_checked, root0Node80Step1Chunk4_3_checked, root0Node80Step1Chunk4_4_checked, root0Node80Step1Chunk4_5_checked, root0Node80Step1Chunk5_0_checked, root0Node80Step1Chunk5_1_checked, root0Node80Step1Chunk5_2_checked, root0Node80Step1Chunk5_3_checked, root0Node80Step1Chunk5_4_checked, root0Node80Step1Chunk5_5_checked, root0Node80Step1Chunk6_0_checked, root0Node80Step1Chunk6_1_checked, root0Node80Step1Chunk6_2_checked, root0Node80Step1Chunk6_3_checked, root0Node80Step1Chunk6_4_checked, root0Node80Step1Chunk6_5_checked, root0Node80Step1Chunk7_0_checked, root0Node80Step1Chunk7_1_checked, root0Node80Step1Chunk7_2_checked, root0Node80Step1Chunk7_3_checked, root0Node80Step1Chunk7_4_checked, root0Node80Step1Chunk7_5_checked, root0Node80Step1Chunk8_0_checked, root0Node80Step1Chunk8_1_checked, root0Node80Step1Chunk8_2_checked, root0Node80Step1Chunk8_3_checked, root0Node80Step1Chunk8_4_checked, root0Node80Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node80Step1_checked :
    checkReplacement table51 root0Node80Domains0 root0Node80Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node80Domains0 root0Node80Domains1
    root0Node80Domains0Fast root0Node80Domains1Fast
    root0Node80Domains0_fast_eq root0Node80Domains1_fast_eq
    root0Node80Step1Narrowing_checked (by decide)
def root0Node81Domains0 : Domains 91 State := restrict root0Node80Domains1 50 (5,0)
def root0Node81Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(1,5)]
  | 10 => some [(6,1)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5)]
  | 14 => some [(4,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(2,0)]
  | 18 => some [(7,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(3,1)]
  | 26 => some [(0,1)]
  | 27 => some [(6,2)]
  | 28 => some [(8,4)]
  | 29 => some [(1,4)]
  | 30 => some [(8,2)]
  | 31 => some [(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(1,0)]
  | 37 => some [(7,1)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(6,4)]
  | 43 => some [(1,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(8,2)]
  | 50 => some [(5,0)]
  | 51 => some [(7,1)]
  | 52 => some [(7,5)]
  | 53 => some [(0,3)]
  | 54 => some [(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(8,4)]
  | 61 => some [(7,3)]
  | 62 => some [(4,2)]
  | 63 => some [(5,3)]
  | 64 => some [(8,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(1,2),(6,2)]
  | 71 => some [(7,4)]
  | 72 => some [(6,3)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3),(6,3)]
  | 76 => some [(7,2),(8,2)]
  | 77 => some [(4,0),(5,0),(8,0)]
  | 78 => some [(2,1),(4,1)]
  | 79 => some [(0,2)]
  | 80 => some [(1,1)]
  | 81 => some [(4,1),(8,1)]
  | 82 => some [(0,2),(6,5)]
  | 83 => some [(0,4),(1,1)]
  | 84 => some [(5,1),(5,4)]
  | 85 => some [(3,2),(5,2)]
  | 86 => some [(4,0),(8,0)]
  | 87 => some [(7,3),(8,3)]
  | 88 => some [(5,2),(5,5)]
  | 89 => some [(7,0),(8,0)]
  | _ => some [(4,3),(8,3)]
theorem root0Node81Domains0_fast_eq : root0Node81Domains0 = expandDomains root0Node81Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node81Domains0 v = expandDomains root0Node81Domains0Fast v from by decide) v
def root0Node81Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(0,0)]
  | 4 => [(7,2)]
  | 5 => [(7,4)]
  | 6 => [(5,5)]
  | 7 => [(7,0)]
  | 8 => [(4,3)]
  | 9 => [(1,5)]
  | 10 => [(6,1)]
  | 11 => [(4,1)]
  | 12 => [(0,2)]
  | 13 => [(0,5)]
  | 14 => [(4,4)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(2,0)]
  | 18 => [(7,3)]
  | 19 => [(5,2)]
  | 20 => [(8,0)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(3,1)]
  | 26 => [(0,1)]
  | 27 => [(6,2)]
  | 28 => [(8,4)]
  | 29 => [(1,4)]
  | 30 => [(8,2)]
  | 31 => [(8,0)]
  | 32 => [(7,3)]
  | 33 => [(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(1,0)]
  | 37 => [(7,1)]
  | 38 => [(7,5)]
  | 39 => [(6,0)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(6,4)]
  | 43 => [(1,2)]
  | 44 => [(8,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(4,0)]
  | 48 => [(7,3)]
  | 49 => [(8,2)]
  | 50 => [(5,0)]
  | 51 => [(7,1)]
  | 52 => [(7,5)]
  | 53 => [(0,3)]
  | 54 => [(8,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(5,1)]
  | 58 => [(0,1)]
  | 59 => [(6,2)]
  | 60 => [(8,4)]
  | 61 => [(7,3)]
  | 62 => [(4,2)]
  | 63 => [(5,3)]
  | 64 => [(8,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(8,5)]
  | 68 => [(1,0)]
  | 69 => [(7,1)]
  | 70 => [(1,2),(6,2)]
  | 71 => [(7,4)]
  | 72 => [(6,3)]
  | 73 => [(7,2)]
  | 74 => [(7,4)]
  | 75 => [(1,3)]
  | 76 => [(8,2)]
  | 77 => [(5,0)]
  | 78 => [(2,1),(4,1)]
  | 79 => [(0,2)]
  | 80 => [(1,1)]
  | 81 => [(8,1)]
  | 82 => [(6,5)]
  | 83 => [(0,4)]
  | 84 => [(5,4)]
  | 85 => [(3,2),(5,2)]
  | 86 => [(4,0),(8,0)]
  | 87 => [(8,3)]
  | 88 => [(5,5)]
  | 89 => [(7,0)]
  | _ => [(4,3)]
def root0Node81Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(1,5)]
  | 10 => some [(6,1)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5)]
  | 14 => some [(4,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(2,0)]
  | 18 => some [(7,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(3,1)]
  | 26 => some [(0,1)]
  | 27 => some [(6,2)]
  | 28 => some [(8,4)]
  | 29 => some [(1,4)]
  | 30 => some [(8,2)]
  | 31 => some [(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(1,0)]
  | 37 => some [(7,1)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(6,4)]
  | 43 => some [(1,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(8,2)]
  | 50 => some [(5,0)]
  | 51 => some [(7,1)]
  | 52 => some [(7,5)]
  | 53 => some [(0,3)]
  | 54 => some [(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(8,4)]
  | 61 => some [(7,3)]
  | 62 => some [(4,2)]
  | 63 => some [(5,3)]
  | 64 => some [(8,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(1,2),(6,2)]
  | 71 => some [(7,4)]
  | 72 => some [(6,3)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3)]
  | 76 => some [(8,2)]
  | 77 => some [(5,0)]
  | 78 => some [(2,1),(4,1)]
  | 79 => some [(0,2)]
  | 80 => some [(1,1)]
  | 81 => some [(8,1)]
  | 82 => some [(6,5)]
  | 83 => some [(0,4)]
  | 84 => some [(5,4)]
  | 85 => some [(3,2),(5,2)]
  | 86 => some [(4,0),(8,0)]
  | 87 => some [(8,3)]
  | 88 => some [(5,5)]
  | 89 => some [(7,0)]
  | _ => some [(4,3)]
theorem root0Node81Domains1_fast_eq : root0Node81Domains1 = expandDomains root0Node81Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node81Domains1 v = expandDomains root0Node81Domains1Fast v from by decide) v
theorem root0Node81Step1Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq (by decide)
theorem root0Node81Step1Narrowing_checked :
    checkNarrowing table57 root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root0Node81Domains0 root0Node81Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node81Step1Chunk0_0_checked, root0Node81Step1Chunk0_1_checked, root0Node81Step1Chunk0_2_checked, root0Node81Step1Chunk0_3_checked, root0Node81Step1Chunk0_4_checked, root0Node81Step1Chunk0_5_checked, root0Node81Step1Chunk1_0_checked, root0Node81Step1Chunk1_1_checked, root0Node81Step1Chunk1_2_checked, root0Node81Step1Chunk1_3_checked, root0Node81Step1Chunk1_4_checked, root0Node81Step1Chunk1_5_checked, root0Node81Step1Chunk2_0_checked, root0Node81Step1Chunk2_1_checked, root0Node81Step1Chunk2_2_checked, root0Node81Step1Chunk2_3_checked, root0Node81Step1Chunk2_4_checked, root0Node81Step1Chunk2_5_checked, root0Node81Step1Chunk3_0_checked, root0Node81Step1Chunk3_1_checked, root0Node81Step1Chunk3_2_checked, root0Node81Step1Chunk3_3_checked, root0Node81Step1Chunk3_4_checked, root0Node81Step1Chunk3_5_checked, root0Node81Step1Chunk4_0_checked, root0Node81Step1Chunk4_1_checked, root0Node81Step1Chunk4_2_checked, root0Node81Step1Chunk4_3_checked, root0Node81Step1Chunk4_4_checked, root0Node81Step1Chunk4_5_checked, root0Node81Step1Chunk5_0_checked, root0Node81Step1Chunk5_1_checked, root0Node81Step1Chunk5_2_checked, root0Node81Step1Chunk5_3_checked, root0Node81Step1Chunk5_4_checked, root0Node81Step1Chunk5_5_checked, root0Node81Step1Chunk6_0_checked, root0Node81Step1Chunk6_1_checked, root0Node81Step1Chunk6_2_checked, root0Node81Step1Chunk6_3_checked, root0Node81Step1Chunk6_4_checked, root0Node81Step1Chunk6_5_checked, root0Node81Step1Chunk7_0_checked, root0Node81Step1Chunk7_1_checked, root0Node81Step1Chunk7_2_checked, root0Node81Step1Chunk7_3_checked, root0Node81Step1Chunk7_4_checked, root0Node81Step1Chunk7_5_checked, root0Node81Step1Chunk8_0_checked, root0Node81Step1Chunk8_1_checked, root0Node81Step1Chunk8_2_checked, root0Node81Step1Chunk8_3_checked, root0Node81Step1Chunk8_4_checked, root0Node81Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node81Step1_checked :
    checkReplacement table57 root0Node81Domains0 root0Node81Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node81Domains0 root0Node81Domains1
    root0Node81Domains0Fast root0Node81Domains1Fast
    root0Node81Domains0_fast_eq root0Node81Domains1_fast_eq
    root0Node81Step1Narrowing_checked (by decide)
def root0Node81Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(0,0)]
  | 4 => [(7,2)]
  | 5 => [(7,4)]
  | 6 => [(5,5)]
  | 7 => [(7,0)]
  | 8 => [(4,3)]
  | 9 => [(1,5)]
  | 10 => [(6,1)]
  | 11 => [(4,1)]
  | 12 => [(0,2)]
  | 13 => [(0,5)]
  | 14 => [(4,4)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(2,0)]
  | 18 => [(7,3)]
  | 19 => [(5,2)]
  | 20 => [(8,0)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(3,1)]
  | 26 => [(0,1)]
  | 27 => [(6,2)]
  | 28 => [(8,4)]
  | 29 => [(1,4)]
  | 30 => [(8,2)]
  | 31 => [(8,0)]
  | 32 => [(7,3)]
  | 33 => [(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(1,0)]
  | 37 => [(7,1)]
  | 38 => [(7,5)]
  | 39 => [(6,0)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(6,4)]
  | 43 => [(1,2)]
  | 44 => [(8,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(4,0)]
  | 48 => [(7,3)]
  | 49 => [(8,2)]
  | 50 => [(5,0)]
  | 51 => [(7,1)]
  | 52 => [(7,5)]
  | 53 => [(0,3)]
  | 54 => [(8,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(5,1)]
  | 58 => [(0,1)]
  | 59 => [(6,2)]
  | 60 => [(8,4)]
  | 61 => [(7,3)]
  | 62 => [(4,2)]
  | 63 => [(5,3)]
  | 64 => [(8,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(8,5)]
  | 68 => [(1,0)]
  | 69 => [(7,1)]
  | 70 => [(1,2)]
  | 71 => [(7,4)]
  | 72 => [(6,3)]
  | 73 => [(7,2)]
  | 74 => [(7,4)]
  | 75 => [(1,3)]
  | 76 => [(8,2)]
  | 77 => [(5,0)]
  | 78 => [(4,1)]
  | 79 => [(0,2)]
  | 80 => [(1,1)]
  | 81 => [(8,1)]
  | 82 => [(6,5)]
  | 83 => [(0,4)]
  | 84 => [(5,4)]
  | 85 => [(5,2)]
  | 86 => [(8,0)]
  | 87 => [(8,3)]
  | 88 => [(5,5)]
  | 89 => [(7,0)]
  | _ => [(4,3)]
def root0Node81Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(1,5)]
  | 10 => some [(6,1)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5)]
  | 14 => some [(4,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(2,0)]
  | 18 => some [(7,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(3,1)]
  | 26 => some [(0,1)]
  | 27 => some [(6,2)]
  | 28 => some [(8,4)]
  | 29 => some [(1,4)]
  | 30 => some [(8,2)]
  | 31 => some [(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(1,0)]
  | 37 => some [(7,1)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(6,4)]
  | 43 => some [(1,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(8,2)]
  | 50 => some [(5,0)]
  | 51 => some [(7,1)]
  | 52 => some [(7,5)]
  | 53 => some [(0,3)]
  | 54 => some [(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(8,4)]
  | 61 => some [(7,3)]
  | 62 => some [(4,2)]
  | 63 => some [(5,3)]
  | 64 => some [(8,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(1,2)]
  | 71 => some [(7,4)]
  | 72 => some [(6,3)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3)]
  | 76 => some [(8,2)]
  | 77 => some [(5,0)]
  | 78 => some [(4,1)]
  | 79 => some [(0,2)]
  | 80 => some [(1,1)]
  | 81 => some [(8,1)]
  | 82 => some [(6,5)]
  | 83 => some [(0,4)]
  | 84 => some [(5,4)]
  | 85 => some [(5,2)]
  | 86 => some [(8,0)]
  | 87 => some [(8,3)]
  | 88 => some [(5,5)]
  | 89 => some [(7,0)]
  | _ => some [(4,3)]
theorem root0Node81Domains2_fast_eq : root0Node81Domains2 = expandDomains root0Node81Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node81Domains2 v = expandDomains root0Node81Domains2Fast v from by decide) v
theorem root0Node81Step2Chunk0_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_0⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk0_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_1⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk0_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_2⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk0_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_3⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk0_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_4⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk0_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_5⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk1_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_0⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk1_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_1⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk1_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_2⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk1_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_3⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk1_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_4⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk1_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_5⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk2_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_0⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk2_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_1⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk2_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_2⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk2_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_3⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk2_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_4⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk2_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_5⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk3_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_0⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk3_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_1⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk3_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_2⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk3_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_3⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk3_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_4⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk3_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_5⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk4_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_0⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk4_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_1⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk4_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_2⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk4_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_3⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk4_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_4⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk4_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_5⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk5_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_0⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk5_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_1⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk5_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_2⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk5_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_3⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk5_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_4⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk5_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_5⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk6_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_0⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk6_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_1⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk6_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_2⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk6_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_3⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk6_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_4⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk6_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_5⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk7_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_0⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk7_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_1⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk7_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_2⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk7_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_3⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk7_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_4⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk7_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_5⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk8_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_0⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk8_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_1⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk8_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_2⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk8_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_3⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk8_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_4⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Chunk8_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_5⟩
      root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq (by decide)
theorem root0Node81Step2Narrowing_checked :
    checkNarrowing table53 root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkNarrowing_flatten table53Scope [table53Rows0_0,table53Rows0_1,table53Rows0_2,table53Rows0_3,table53Rows0_4,table53Rows0_5,table53Rows1_0,table53Rows1_1,table53Rows1_2,table53Rows1_3,table53Rows1_4,table53Rows1_5,table53Rows2_0,table53Rows2_1,table53Rows2_2,table53Rows2_3,table53Rows2_4,table53Rows2_5,table53Rows3_0,table53Rows3_1,table53Rows3_2,table53Rows3_3,table53Rows3_4,table53Rows3_5,table53Rows4_0,table53Rows4_1,table53Rows4_2,table53Rows4_3,table53Rows4_4,table53Rows4_5,table53Rows5_0,table53Rows5_1,table53Rows5_2,table53Rows5_3,table53Rows5_4,table53Rows5_5,table53Rows6_0,table53Rows6_1,table53Rows6_2,table53Rows6_3,table53Rows6_4,table53Rows6_5,table53Rows7_0,table53Rows7_1,table53Rows7_2,table53Rows7_3,table53Rows7_4,table53Rows7_5,table53Rows8_0,table53Rows8_1,table53Rows8_2,table53Rows8_3,table53Rows8_4,table53Rows8_5]
    root0Node81Domains1 root0Node81Domains2 (by
      simp only [List.all_cons, List.all_nil, root0Node81Step2Chunk0_0_checked, root0Node81Step2Chunk0_1_checked, root0Node81Step2Chunk0_2_checked, root0Node81Step2Chunk0_3_checked, root0Node81Step2Chunk0_4_checked, root0Node81Step2Chunk0_5_checked, root0Node81Step2Chunk1_0_checked, root0Node81Step2Chunk1_1_checked, root0Node81Step2Chunk1_2_checked, root0Node81Step2Chunk1_3_checked, root0Node81Step2Chunk1_4_checked, root0Node81Step2Chunk1_5_checked, root0Node81Step2Chunk2_0_checked, root0Node81Step2Chunk2_1_checked, root0Node81Step2Chunk2_2_checked, root0Node81Step2Chunk2_3_checked, root0Node81Step2Chunk2_4_checked, root0Node81Step2Chunk2_5_checked, root0Node81Step2Chunk3_0_checked, root0Node81Step2Chunk3_1_checked, root0Node81Step2Chunk3_2_checked, root0Node81Step2Chunk3_3_checked, root0Node81Step2Chunk3_4_checked, root0Node81Step2Chunk3_5_checked, root0Node81Step2Chunk4_0_checked, root0Node81Step2Chunk4_1_checked, root0Node81Step2Chunk4_2_checked, root0Node81Step2Chunk4_3_checked, root0Node81Step2Chunk4_4_checked, root0Node81Step2Chunk4_5_checked, root0Node81Step2Chunk5_0_checked, root0Node81Step2Chunk5_1_checked, root0Node81Step2Chunk5_2_checked, root0Node81Step2Chunk5_3_checked, root0Node81Step2Chunk5_4_checked, root0Node81Step2Chunk5_5_checked, root0Node81Step2Chunk6_0_checked, root0Node81Step2Chunk6_1_checked, root0Node81Step2Chunk6_2_checked, root0Node81Step2Chunk6_3_checked, root0Node81Step2Chunk6_4_checked, root0Node81Step2Chunk6_5_checked, root0Node81Step2Chunk7_0_checked, root0Node81Step2Chunk7_1_checked, root0Node81Step2Chunk7_2_checked, root0Node81Step2Chunk7_3_checked, root0Node81Step2Chunk7_4_checked, root0Node81Step2Chunk7_5_checked, root0Node81Step2Chunk8_0_checked, root0Node81Step2Chunk8_1_checked, root0Node81Step2Chunk8_2_checked, root0Node81Step2Chunk8_3_checked, root0Node81Step2Chunk8_4_checked, root0Node81Step2Chunk8_5_checked, Bool.true_and])
theorem root0Node81Step2_checked :
    checkReplacement table53 root0Node81Domains1 root0Node81Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root0Node81Domains1 root0Node81Domains2
    root0Node81Domains1Fast root0Node81Domains2Fast
    root0Node81Domains1_fast_eq root0Node81Domains2_fast_eq
    root0Node81Step2Narrowing_checked (by decide)
theorem root0Node81Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node81Domains2 (.output 39) = true := by decide
def root0Node82Domains0 : Domains 91 State := restrict root0Node80Domains1 50 (8,0)
def root0Node82Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(1,5)]
  | 10 => some [(6,1)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5)]
  | 14 => some [(4,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(2,0)]
  | 18 => some [(7,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(3,1)]
  | 26 => some [(0,1)]
  | 27 => some [(6,2)]
  | 28 => some [(8,4)]
  | 29 => some [(1,4)]
  | 30 => some [(8,2)]
  | 31 => some [(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(1,0)]
  | 37 => some [(7,1)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(6,4)]
  | 43 => some [(1,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(8,2)]
  | 50 => some [(8,0)]
  | 51 => some [(7,1)]
  | 52 => some [(7,5)]
  | 53 => some [(0,3)]
  | 54 => some [(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(8,4)]
  | 61 => some [(7,3)]
  | 62 => some [(4,2)]
  | 63 => some [(5,3)]
  | 64 => some [(8,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(1,2),(6,2)]
  | 71 => some [(7,4)]
  | 72 => some [(6,3)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3),(6,3)]
  | 76 => some [(7,2),(8,2)]
  | 77 => some [(4,0),(5,0),(8,0)]
  | 78 => some [(2,1),(4,1)]
  | 79 => some [(0,2)]
  | 80 => some [(1,1)]
  | 81 => some [(4,1),(8,1)]
  | 82 => some [(0,2),(6,5)]
  | 83 => some [(0,4),(1,1)]
  | 84 => some [(5,1),(5,4)]
  | 85 => some [(3,2),(5,2)]
  | 86 => some [(4,0),(8,0)]
  | 87 => some [(7,3),(8,3)]
  | 88 => some [(5,2),(5,5)]
  | 89 => some [(7,0),(8,0)]
  | _ => some [(4,3),(8,3)]
theorem root0Node82Domains0_fast_eq : root0Node82Domains0 = expandDomains root0Node82Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node82Domains0 v = expandDomains root0Node82Domains0Fast v from by decide) v
def root0Node82Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(0,0)]
  | 4 => [(7,2)]
  | 5 => [(7,4)]
  | 6 => [(5,5)]
  | 7 => [(7,0)]
  | 8 => [(4,3)]
  | 9 => [(1,5)]
  | 10 => [(6,1)]
  | 11 => [(4,1)]
  | 12 => [(0,2)]
  | 13 => [(0,5)]
  | 14 => [(4,4)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(2,0)]
  | 18 => [(7,3)]
  | 19 => [(5,2)]
  | 20 => [(8,0)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(3,1)]
  | 26 => [(0,1)]
  | 27 => [(6,2)]
  | 28 => [(8,4)]
  | 29 => [(1,4)]
  | 30 => [(8,2)]
  | 31 => [(8,0)]
  | 32 => [(7,3)]
  | 33 => [(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(1,0)]
  | 37 => [(7,1)]
  | 38 => [(7,5)]
  | 39 => [(6,0)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(6,4)]
  | 43 => [(1,2)]
  | 44 => [(8,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(4,0)]
  | 48 => [(7,3)]
  | 49 => [(8,2)]
  | 50 => [(8,0)]
  | 51 => [(7,1)]
  | 52 => [(7,5)]
  | 53 => [(0,3)]
  | 54 => [(8,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(5,1)]
  | 58 => [(0,1)]
  | 59 => [(6,2)]
  | 60 => [(8,4)]
  | 61 => [(7,3)]
  | 62 => [(4,2)]
  | 63 => [(5,3)]
  | 64 => [(8,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(8,5)]
  | 68 => [(1,0)]
  | 69 => [(7,1)]
  | 70 => [(1,2),(6,2)]
  | 71 => [(7,4)]
  | 72 => [(6,3)]
  | 73 => [(7,2)]
  | 74 => [(7,4)]
  | 75 => [(1,3),(6,3)]
  | 76 => [(7,2),(8,2)]
  | 77 => [(4,0),(8,0)]
  | 78 => [(2,1),(4,1)]
  | 79 => [(0,2)]
  | 80 => [(1,1)]
  | 81 => [(4,1),(8,1)]
  | 82 => [(0,2),(6,5)]
  | 83 => [(0,4),(1,1)]
  | 84 => [(5,1),(5,4)]
  | 85 => [(3,2),(5,2)]
  | 86 => [(4,0),(8,0)]
  | 87 => [(7,3),(8,3)]
  | 88 => [(5,2),(5,5)]
  | 89 => [(7,0),(8,0)]
  | _ => [(4,3),(8,3)]
def root0Node82Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(1,5)]
  | 10 => some [(6,1)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5)]
  | 14 => some [(4,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(2,0)]
  | 18 => some [(7,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(3,1)]
  | 26 => some [(0,1)]
  | 27 => some [(6,2)]
  | 28 => some [(8,4)]
  | 29 => some [(1,4)]
  | 30 => some [(8,2)]
  | 31 => some [(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(1,0)]
  | 37 => some [(7,1)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(6,4)]
  | 43 => some [(1,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(8,2)]
  | 50 => some [(8,0)]
  | 51 => some [(7,1)]
  | 52 => some [(7,5)]
  | 53 => some [(0,3)]
  | 54 => some [(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(8,4)]
  | 61 => some [(7,3)]
  | 62 => some [(4,2)]
  | 63 => some [(5,3)]
  | 64 => some [(8,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(1,2),(6,2)]
  | 71 => some [(7,4)]
  | 72 => some [(6,3)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3),(6,3)]
  | 76 => some [(7,2),(8,2)]
  | 77 => some [(4,0),(8,0)]
  | 78 => some [(2,1),(4,1)]
  | 79 => some [(0,2)]
  | 80 => some [(1,1)]
  | 81 => some [(4,1),(8,1)]
  | 82 => some [(0,2),(6,5)]
  | 83 => some [(0,4),(1,1)]
  | 84 => some [(5,1),(5,4)]
  | 85 => some [(3,2),(5,2)]
  | 86 => some [(4,0),(8,0)]
  | 87 => some [(7,3),(8,3)]
  | 88 => some [(5,2),(5,5)]
  | 89 => some [(7,0),(8,0)]
  | _ => some [(4,3),(8,3)]
theorem root0Node82Domains1_fast_eq : root0Node82Domains1 = expandDomains root0Node82Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node82Domains1 v = expandDomains root0Node82Domains1Fast v from by decide) v
theorem root0Node82Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq (by decide)
theorem root0Node82Step1Narrowing_checked :
    checkNarrowing table36 root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root0Node82Domains0 root0Node82Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node82Step1Chunk0_0_checked, root0Node82Step1Chunk0_1_checked, root0Node82Step1Chunk0_2_checked, root0Node82Step1Chunk0_3_checked, root0Node82Step1Chunk0_4_checked, root0Node82Step1Chunk0_5_checked, root0Node82Step1Chunk1_0_checked, root0Node82Step1Chunk1_1_checked, root0Node82Step1Chunk1_2_checked, root0Node82Step1Chunk1_3_checked, root0Node82Step1Chunk1_4_checked, root0Node82Step1Chunk1_5_checked, root0Node82Step1Chunk2_0_checked, root0Node82Step1Chunk2_1_checked, root0Node82Step1Chunk2_2_checked, root0Node82Step1Chunk2_3_checked, root0Node82Step1Chunk2_4_checked, root0Node82Step1Chunk2_5_checked, root0Node82Step1Chunk3_0_checked, root0Node82Step1Chunk3_1_checked, root0Node82Step1Chunk3_2_checked, root0Node82Step1Chunk3_3_checked, root0Node82Step1Chunk3_4_checked, root0Node82Step1Chunk3_5_checked, root0Node82Step1Chunk4_0_checked, root0Node82Step1Chunk4_1_checked, root0Node82Step1Chunk4_2_checked, root0Node82Step1Chunk4_3_checked, root0Node82Step1Chunk4_4_checked, root0Node82Step1Chunk4_5_checked, root0Node82Step1Chunk5_0_checked, root0Node82Step1Chunk5_1_checked, root0Node82Step1Chunk5_2_checked, root0Node82Step1Chunk5_3_checked, root0Node82Step1Chunk5_4_checked, root0Node82Step1Chunk5_5_checked, root0Node82Step1Chunk6_0_checked, root0Node82Step1Chunk6_1_checked, root0Node82Step1Chunk6_2_checked, root0Node82Step1Chunk6_3_checked, root0Node82Step1Chunk6_4_checked, root0Node82Step1Chunk6_5_checked, root0Node82Step1Chunk7_0_checked, root0Node82Step1Chunk7_1_checked, root0Node82Step1Chunk7_2_checked, root0Node82Step1Chunk7_3_checked, root0Node82Step1Chunk7_4_checked, root0Node82Step1Chunk7_5_checked, root0Node82Step1Chunk8_0_checked, root0Node82Step1Chunk8_1_checked, root0Node82Step1Chunk8_2_checked, root0Node82Step1Chunk8_3_checked, root0Node82Step1Chunk8_4_checked, root0Node82Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node82Step1_checked :
    checkReplacement table36 root0Node82Domains0 root0Node82Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node82Domains0 root0Node82Domains1
    root0Node82Domains0Fast root0Node82Domains1Fast
    root0Node82Domains0_fast_eq root0Node82Domains1_fast_eq
    root0Node82Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
