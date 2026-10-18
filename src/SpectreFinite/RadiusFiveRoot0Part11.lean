module

public import SpectreFinite.RadiusFiveRoot0Part10
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable36
public import SpectreFinite.RadiusFiveTable51
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node20Domains0 : Domains 91 State := restrict root0Node19Domains2 50 (5,0)
def root0Node20Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(8,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(8,1)]
  | 12 => some [(1,5)]
  | 13 => some [(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(4,2)]
  | 18 => some [(5,3)]
  | 19 => some [(5,5)]
  | 20 => some [(7,0)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(1,4)]
  | 27 => some [(0,5)]
  | 28 => some [(4,4)]
  | 29 => some [(1,4)]
  | 30 => some [(5,2)]
  | 31 => some [(8,0)]
  | 32 => some [(8,3)]
  | 33 => some [(5,5)]
  | 34 => some [(3,0)]
  | 35 => some [(2,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(0,5)]
  | 44 => some [(4,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(8,2)]
  | 50 => some [(5,0)]
  | 51 => some [(7,1)]
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
  | 70 => some [(1,2),(6,2)]
  | 71 => some [(8,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3)]
  | 76 => some [(8,2)]
  | 77 => some [(5,0),(8,0)]
  | 78 => some [(7,1),(8,1)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(8,1)]
  | 82 => some [(6,5)]
  | 83 => some [(0,4)]
  | 84 => some [(5,4)]
  | 85 => some [(4,5),(5,5),(8,5)]
  | 86 => some [(7,0)]
  | 87 => some [(8,3)]
  | 88 => some [(5,5),(8,5)]
  | 89 => some [(7,0)]
  | _ => some [(4,3)]
theorem root0Node20Domains0_fast_eq : root0Node20Domains0 = expandDomains root0Node20Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node20Domains0 v = expandDomains root0Node20Domains0Fast v from by decide) v
def root0Node20Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(8,4)]
  | 6 => [(8,5)]
  | 7 => [(7,0)]
  | 8 => [(4,3)]
  | 9 => [(7,5)]
  | 10 => [(0,3)]
  | 11 => [(8,1)]
  | 12 => [(1,5)]
  | 13 => [(6,3)]
  | 14 => [(7,2)]
  | 15 => [(7,4)]
  | 16 => [(1,3)]
  | 17 => [(4,2)]
  | 18 => [(5,3)]
  | 19 => [(5,5)]
  | 20 => [(7,0)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(8,1)]
  | 24 => [(6,5)]
  | 25 => [(0,4)]
  | 26 => [(1,4)]
  | 27 => [(0,5)]
  | 28 => [(4,4)]
  | 29 => [(1,4)]
  | 30 => [(5,2)]
  | 31 => [(8,0)]
  | 32 => [(8,3)]
  | 33 => [(5,5)]
  | 34 => [(3,0)]
  | 35 => [(2,5)]
  | 36 => [(6,0)]
  | 37 => [(7,1)]
  | 38 => [(7,5)]
  | 39 => [(6,0)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(1,4)]
  | 43 => [(0,5)]
  | 44 => [(4,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(4,0)]
  | 48 => [(7,3)]
  | 49 => [(8,2)]
  | 50 => [(5,0)]
  | 51 => [(7,1)]
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
  | 70 => [(1,2),(6,2)]
  | 71 => [(8,4)]
  | 72 => [(0,0)]
  | 73 => [(7,2)]
  | 74 => [(7,4)]
  | 75 => [(1,3)]
  | 76 => [(8,2)]
  | 77 => [(5,0)]
  | 78 => [(7,1),(8,1)]
  | 79 => [(1,5)]
  | 80 => [(6,1)]
  | 81 => [(8,1)]
  | 82 => [(6,5)]
  | 83 => [(0,4)]
  | 84 => [(5,4)]
  | 85 => [(4,5),(5,5),(8,5)]
  | 86 => [(7,0)]
  | 87 => [(8,3)]
  | 88 => [(5,5)]
  | 89 => [(7,0)]
  | _ => [(4,3)]
def root0Node20Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(8,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(8,1)]
  | 12 => some [(1,5)]
  | 13 => some [(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(4,2)]
  | 18 => some [(5,3)]
  | 19 => some [(5,5)]
  | 20 => some [(7,0)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(1,4)]
  | 27 => some [(0,5)]
  | 28 => some [(4,4)]
  | 29 => some [(1,4)]
  | 30 => some [(5,2)]
  | 31 => some [(8,0)]
  | 32 => some [(8,3)]
  | 33 => some [(5,5)]
  | 34 => some [(3,0)]
  | 35 => some [(2,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(0,5)]
  | 44 => some [(4,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(8,2)]
  | 50 => some [(5,0)]
  | 51 => some [(7,1)]
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
  | 70 => some [(1,2),(6,2)]
  | 71 => some [(8,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3)]
  | 76 => some [(8,2)]
  | 77 => some [(5,0)]
  | 78 => some [(7,1),(8,1)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(8,1)]
  | 82 => some [(6,5)]
  | 83 => some [(0,4)]
  | 84 => some [(5,4)]
  | 85 => some [(4,5),(5,5),(8,5)]
  | 86 => some [(7,0)]
  | 87 => some [(8,3)]
  | 88 => some [(5,5)]
  | 89 => some [(7,0)]
  | _ => some [(4,3)]
theorem root0Node20Domains1_fast_eq : root0Node20Domains1 = expandDomains root0Node20Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node20Domains1 v = expandDomains root0Node20Domains1Fast v from by decide) v
theorem root0Node20Step1Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq (by decide)
theorem root0Node20Step1Narrowing_checked :
    checkNarrowing table57 root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root0Node20Domains0 root0Node20Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node20Step1Chunk0_0_checked, root0Node20Step1Chunk0_1_checked, root0Node20Step1Chunk0_2_checked, root0Node20Step1Chunk0_3_checked, root0Node20Step1Chunk0_4_checked, root0Node20Step1Chunk0_5_checked, root0Node20Step1Chunk1_0_checked, root0Node20Step1Chunk1_1_checked, root0Node20Step1Chunk1_2_checked, root0Node20Step1Chunk1_3_checked, root0Node20Step1Chunk1_4_checked, root0Node20Step1Chunk1_5_checked, root0Node20Step1Chunk2_0_checked, root0Node20Step1Chunk2_1_checked, root0Node20Step1Chunk2_2_checked, root0Node20Step1Chunk2_3_checked, root0Node20Step1Chunk2_4_checked, root0Node20Step1Chunk2_5_checked, root0Node20Step1Chunk3_0_checked, root0Node20Step1Chunk3_1_checked, root0Node20Step1Chunk3_2_checked, root0Node20Step1Chunk3_3_checked, root0Node20Step1Chunk3_4_checked, root0Node20Step1Chunk3_5_checked, root0Node20Step1Chunk4_0_checked, root0Node20Step1Chunk4_1_checked, root0Node20Step1Chunk4_2_checked, root0Node20Step1Chunk4_3_checked, root0Node20Step1Chunk4_4_checked, root0Node20Step1Chunk4_5_checked, root0Node20Step1Chunk5_0_checked, root0Node20Step1Chunk5_1_checked, root0Node20Step1Chunk5_2_checked, root0Node20Step1Chunk5_3_checked, root0Node20Step1Chunk5_4_checked, root0Node20Step1Chunk5_5_checked, root0Node20Step1Chunk6_0_checked, root0Node20Step1Chunk6_1_checked, root0Node20Step1Chunk6_2_checked, root0Node20Step1Chunk6_3_checked, root0Node20Step1Chunk6_4_checked, root0Node20Step1Chunk6_5_checked, root0Node20Step1Chunk7_0_checked, root0Node20Step1Chunk7_1_checked, root0Node20Step1Chunk7_2_checked, root0Node20Step1Chunk7_3_checked, root0Node20Step1Chunk7_4_checked, root0Node20Step1Chunk7_5_checked, root0Node20Step1Chunk8_0_checked, root0Node20Step1Chunk8_1_checked, root0Node20Step1Chunk8_2_checked, root0Node20Step1Chunk8_3_checked, root0Node20Step1Chunk8_4_checked, root0Node20Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node20Step1_checked :
    checkReplacement table57 root0Node20Domains0 root0Node20Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node20Domains0 root0Node20Domains1
    root0Node20Domains0Fast root0Node20Domains1Fast
    root0Node20Domains0_fast_eq root0Node20Domains1_fast_eq
    root0Node20Step1Narrowing_checked (by decide)
def root0Node20Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(8,4)]
  | 6 => [(8,5)]
  | 7 => [(7,0)]
  | 8 => [(4,3)]
  | 9 => [(7,5)]
  | 10 => [(0,3)]
  | 11 => [(8,1)]
  | 12 => [(1,5)]
  | 13 => [(6,3)]
  | 14 => [(7,2)]
  | 15 => [(7,4)]
  | 16 => [(1,3)]
  | 17 => [(4,2)]
  | 18 => [(5,3)]
  | 19 => [(5,5)]
  | 20 => [(7,0)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(8,1)]
  | 24 => [(6,5)]
  | 25 => [(0,4)]
  | 26 => [(1,4)]
  | 27 => [(0,5)]
  | 28 => [(4,4)]
  | 29 => [(1,4)]
  | 30 => [(5,2)]
  | 31 => [(8,0)]
  | 32 => [(8,3)]
  | 33 => [(5,5)]
  | 34 => [(3,0)]
  | 35 => [(2,5)]
  | 36 => [(6,0)]
  | 37 => [(7,1)]
  | 38 => [(7,5)]
  | 39 => [(6,0)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(1,4)]
  | 43 => [(0,5)]
  | 44 => [(4,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(4,0)]
  | 48 => [(7,3)]
  | 49 => [(8,2)]
  | 50 => [(5,0)]
  | 51 => [(7,1)]
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
def root0Node20Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(8,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(8,1)]
  | 12 => some [(1,5)]
  | 13 => some [(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(4,2)]
  | 18 => some [(5,3)]
  | 19 => some [(5,5)]
  | 20 => some [(7,0)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(1,4)]
  | 27 => some [(0,5)]
  | 28 => some [(4,4)]
  | 29 => some [(1,4)]
  | 30 => some [(5,2)]
  | 31 => some [(8,0)]
  | 32 => some [(8,3)]
  | 33 => some [(5,5)]
  | 34 => some [(3,0)]
  | 35 => some [(2,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(0,5)]
  | 44 => some [(4,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(8,2)]
  | 50 => some [(5,0)]
  | 51 => some [(7,1)]
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
theorem root0Node20Domains2_fast_eq : root0Node20Domains2 = expandDomains root0Node20Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node20Domains2 v = expandDomains root0Node20Domains2Fast v from by decide) v
theorem root0Node20Step2Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq (by decide)
theorem root0Node20Step2Narrowing_checked :
    checkNarrowing table54 root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root0Node20Domains1 root0Node20Domains2 (by
      simp only [List.all_cons, List.all_nil, root0Node20Step2Chunk0_0_checked, root0Node20Step2Chunk0_1_checked, root0Node20Step2Chunk0_2_checked, root0Node20Step2Chunk0_3_checked, root0Node20Step2Chunk0_4_checked, root0Node20Step2Chunk0_5_checked, root0Node20Step2Chunk1_0_checked, root0Node20Step2Chunk1_1_checked, root0Node20Step2Chunk1_2_checked, root0Node20Step2Chunk1_3_checked, root0Node20Step2Chunk1_4_checked, root0Node20Step2Chunk1_5_checked, root0Node20Step2Chunk2_0_checked, root0Node20Step2Chunk2_1_checked, root0Node20Step2Chunk2_2_checked, root0Node20Step2Chunk2_3_checked, root0Node20Step2Chunk2_4_checked, root0Node20Step2Chunk2_5_checked, root0Node20Step2Chunk3_0_checked, root0Node20Step2Chunk3_1_checked, root0Node20Step2Chunk3_2_checked, root0Node20Step2Chunk3_3_checked, root0Node20Step2Chunk3_4_checked, root0Node20Step2Chunk3_5_checked, root0Node20Step2Chunk4_0_checked, root0Node20Step2Chunk4_1_checked, root0Node20Step2Chunk4_2_checked, root0Node20Step2Chunk4_3_checked, root0Node20Step2Chunk4_4_checked, root0Node20Step2Chunk4_5_checked, root0Node20Step2Chunk5_0_checked, root0Node20Step2Chunk5_1_checked, root0Node20Step2Chunk5_2_checked, root0Node20Step2Chunk5_3_checked, root0Node20Step2Chunk5_4_checked, root0Node20Step2Chunk5_5_checked, root0Node20Step2Chunk6_0_checked, root0Node20Step2Chunk6_1_checked, root0Node20Step2Chunk6_2_checked, root0Node20Step2Chunk6_3_checked, root0Node20Step2Chunk6_4_checked, root0Node20Step2Chunk6_5_checked, root0Node20Step2Chunk7_0_checked, root0Node20Step2Chunk7_1_checked, root0Node20Step2Chunk7_2_checked, root0Node20Step2Chunk7_3_checked, root0Node20Step2Chunk7_4_checked, root0Node20Step2Chunk7_5_checked, root0Node20Step2Chunk8_0_checked, root0Node20Step2Chunk8_1_checked, root0Node20Step2Chunk8_2_checked, root0Node20Step2Chunk8_3_checked, root0Node20Step2Chunk8_4_checked, root0Node20Step2Chunk8_5_checked, Bool.true_and])
theorem root0Node20Step2_checked :
    checkReplacement table54 root0Node20Domains1 root0Node20Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root0Node20Domains1 root0Node20Domains2
    root0Node20Domains1Fast root0Node20Domains2Fast
    root0Node20Domains1_fast_eq root0Node20Domains2_fast_eq
    root0Node20Step2Narrowing_checked (by decide)
theorem root0Node20Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node20Domains2 (.output 9) = true := by decide
def root0Node21Domains0 : Domains 91 State := restrict root0Node19Domains2 50 (8,0)
def root0Node21Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(8,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(8,1)]
  | 12 => some [(1,5)]
  | 13 => some [(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(4,2)]
  | 18 => some [(5,3)]
  | 19 => some [(5,5)]
  | 20 => some [(7,0)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(1,4)]
  | 27 => some [(0,5)]
  | 28 => some [(4,4)]
  | 29 => some [(1,4)]
  | 30 => some [(5,2)]
  | 31 => some [(8,0)]
  | 32 => some [(8,3)]
  | 33 => some [(5,5)]
  | 34 => some [(3,0)]
  | 35 => some [(2,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(0,5)]
  | 44 => some [(4,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(8,2)]
  | 50 => some [(8,0)]
  | 51 => some [(7,1)]
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
  | 70 => some [(1,2),(6,2)]
  | 71 => some [(8,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3)]
  | 76 => some [(8,2)]
  | 77 => some [(5,0),(8,0)]
  | 78 => some [(7,1),(8,1)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(8,1)]
  | 82 => some [(6,5)]
  | 83 => some [(0,4)]
  | 84 => some [(5,4)]
  | 85 => some [(4,5),(5,5),(8,5)]
  | 86 => some [(7,0)]
  | 87 => some [(8,3)]
  | 88 => some [(5,5),(8,5)]
  | 89 => some [(7,0)]
  | _ => some [(4,3)]
theorem root0Node21Domains0_fast_eq : root0Node21Domains0 = expandDomains root0Node21Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node21Domains0 v = expandDomains root0Node21Domains0Fast v from by decide) v
def root0Node21Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(8,4)]
  | 6 => [(8,5)]
  | 7 => [(7,0)]
  | 8 => [(4,3)]
  | 9 => [(7,5)]
  | 10 => [(0,3)]
  | 11 => [(8,1)]
  | 12 => [(1,5)]
  | 13 => [(6,3)]
  | 14 => [(7,2)]
  | 15 => [(7,4)]
  | 16 => [(1,3)]
  | 17 => [(4,2)]
  | 18 => [(5,3)]
  | 19 => [(5,5)]
  | 20 => [(7,0)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(8,1)]
  | 24 => [(6,5)]
  | 25 => [(0,4)]
  | 26 => [(1,4)]
  | 27 => [(0,5)]
  | 28 => [(4,4)]
  | 29 => [(1,4)]
  | 30 => [(5,2)]
  | 31 => [(8,0)]
  | 32 => [(8,3)]
  | 33 => [(5,5)]
  | 34 => [(3,0)]
  | 35 => [(2,5)]
  | 36 => [(6,0)]
  | 37 => [(7,1)]
  | 38 => [(7,5)]
  | 39 => [(6,0)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(1,4)]
  | 43 => [(0,5)]
  | 44 => [(4,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(4,0)]
  | 48 => [(7,3)]
  | 49 => [(8,2)]
  | 50 => [(8,0)]
  | 51 => [(7,1)]
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
  | 70 => [(1,2),(6,2)]
  | 71 => [(8,4)]
  | 72 => [(0,0)]
  | 73 => [(7,2)]
  | 74 => [(7,4)]
  | 75 => [(1,3)]
  | 76 => [(8,2)]
  | 77 => [(8,0)]
  | 78 => [(7,1),(8,1)]
  | 79 => [(1,5)]
  | 80 => [(6,1)]
  | 81 => [(8,1)]
  | 82 => [(6,5)]
  | 83 => [(0,4)]
  | 84 => [(5,4)]
  | 85 => [(4,5),(5,5),(8,5)]
  | 86 => [(7,0)]
  | 87 => [(8,3)]
  | 88 => [(5,5),(8,5)]
  | 89 => [(7,0)]
  | _ => [(4,3)]
def root0Node21Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(8,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(8,1)]
  | 12 => some [(1,5)]
  | 13 => some [(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(4,2)]
  | 18 => some [(5,3)]
  | 19 => some [(5,5)]
  | 20 => some [(7,0)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(1,4)]
  | 27 => some [(0,5)]
  | 28 => some [(4,4)]
  | 29 => some [(1,4)]
  | 30 => some [(5,2)]
  | 31 => some [(8,0)]
  | 32 => some [(8,3)]
  | 33 => some [(5,5)]
  | 34 => some [(3,0)]
  | 35 => some [(2,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(0,5)]
  | 44 => some [(4,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(8,2)]
  | 50 => some [(8,0)]
  | 51 => some [(7,1)]
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
  | 70 => some [(1,2),(6,2)]
  | 71 => some [(8,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3)]
  | 76 => some [(8,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1),(8,1)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(8,1)]
  | 82 => some [(6,5)]
  | 83 => some [(0,4)]
  | 84 => some [(5,4)]
  | 85 => some [(4,5),(5,5),(8,5)]
  | 86 => some [(7,0)]
  | 87 => some [(8,3)]
  | 88 => some [(5,5),(8,5)]
  | 89 => some [(7,0)]
  | _ => some [(4,3)]
theorem root0Node21Domains1_fast_eq : root0Node21Domains1 = expandDomains root0Node21Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node21Domains1 v = expandDomains root0Node21Domains1Fast v from by decide) v
theorem root0Node21Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Narrowing_checked :
    checkNarrowing table36 root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root0Node21Domains0 root0Node21Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node21Step1Chunk0_0_checked, root0Node21Step1Chunk0_1_checked, root0Node21Step1Chunk0_2_checked, root0Node21Step1Chunk0_3_checked, root0Node21Step1Chunk0_4_checked, root0Node21Step1Chunk0_5_checked, root0Node21Step1Chunk1_0_checked, root0Node21Step1Chunk1_1_checked, root0Node21Step1Chunk1_2_checked, root0Node21Step1Chunk1_3_checked, root0Node21Step1Chunk1_4_checked, root0Node21Step1Chunk1_5_checked, root0Node21Step1Chunk2_0_checked, root0Node21Step1Chunk2_1_checked, root0Node21Step1Chunk2_2_checked, root0Node21Step1Chunk2_3_checked, root0Node21Step1Chunk2_4_checked, root0Node21Step1Chunk2_5_checked, root0Node21Step1Chunk3_0_checked, root0Node21Step1Chunk3_1_checked, root0Node21Step1Chunk3_2_checked, root0Node21Step1Chunk3_3_checked, root0Node21Step1Chunk3_4_checked, root0Node21Step1Chunk3_5_checked, root0Node21Step1Chunk4_0_checked, root0Node21Step1Chunk4_1_checked, root0Node21Step1Chunk4_2_checked, root0Node21Step1Chunk4_3_checked, root0Node21Step1Chunk4_4_checked, root0Node21Step1Chunk4_5_checked, root0Node21Step1Chunk5_0_checked, root0Node21Step1Chunk5_1_checked, root0Node21Step1Chunk5_2_checked, root0Node21Step1Chunk5_3_checked, root0Node21Step1Chunk5_4_checked, root0Node21Step1Chunk5_5_checked, root0Node21Step1Chunk6_0_checked, root0Node21Step1Chunk6_1_checked, root0Node21Step1Chunk6_2_checked, root0Node21Step1Chunk6_3_checked, root0Node21Step1Chunk6_4_checked, root0Node21Step1Chunk6_5_checked, root0Node21Step1Chunk7_0_checked, root0Node21Step1Chunk7_1_checked, root0Node21Step1Chunk7_2_checked, root0Node21Step1Chunk7_3_checked, root0Node21Step1Chunk7_4_checked, root0Node21Step1Chunk7_5_checked, root0Node21Step1Chunk8_0_checked, root0Node21Step1Chunk8_1_checked, root0Node21Step1Chunk8_2_checked, root0Node21Step1Chunk8_3_checked, root0Node21Step1Chunk8_4_checked, root0Node21Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node21Step1_checked :
    checkReplacement table36 root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq
    root0Node21Step1Narrowing_checked (by decide)
def root0Node22Domains0 : Domains 91 State := restrict root0Node21Domains1 70 (1,2)
def root0Node22Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(8,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(8,1)]
  | 12 => some [(1,5)]
  | 13 => some [(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(4,2)]
  | 18 => some [(5,3)]
  | 19 => some [(5,5)]
  | 20 => some [(7,0)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(1,4)]
  | 27 => some [(0,5)]
  | 28 => some [(4,4)]
  | 29 => some [(1,4)]
  | 30 => some [(5,2)]
  | 31 => some [(8,0)]
  | 32 => some [(8,3)]
  | 33 => some [(5,5)]
  | 34 => some [(3,0)]
  | 35 => some [(2,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(0,5)]
  | 44 => some [(4,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(8,2)]
  | 50 => some [(8,0)]
  | 51 => some [(7,1)]
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
  | 77 => some [(8,0)]
  | 78 => some [(7,1),(8,1)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(8,1)]
  | 82 => some [(6,5)]
  | 83 => some [(0,4)]
  | 84 => some [(5,4)]
  | 85 => some [(4,5),(5,5),(8,5)]
  | 86 => some [(7,0)]
  | 87 => some [(8,3)]
  | 88 => some [(5,5),(8,5)]
  | 89 => some [(7,0)]
  | _ => some [(4,3)]
theorem root0Node22Domains0_fast_eq : root0Node22Domains0 = expandDomains root0Node22Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node22Domains0 v = expandDomains root0Node22Domains0Fast v from by decide) v
def root0Node22Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(8,4)]
  | 6 => [(8,5)]
  | 7 => [(7,0)]
  | 8 => [(4,3)]
  | 9 => [(7,5)]
  | 10 => [(0,3)]
  | 11 => [(8,1)]
  | 12 => [(1,5)]
  | 13 => [(6,3)]
  | 14 => [(7,2)]
  | 15 => [(7,4)]
  | 16 => [(1,3)]
  | 17 => [(4,2)]
  | 18 => [(5,3)]
  | 19 => [(5,5)]
  | 20 => [(7,0)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(8,1)]
  | 24 => [(6,5)]
  | 25 => [(0,4)]
  | 26 => [(1,4)]
  | 27 => [(0,5)]
  | 28 => [(4,4)]
  | 29 => [(1,4)]
  | 30 => [(5,2)]
  | 31 => [(8,0)]
  | 32 => [(8,3)]
  | 33 => [(5,5)]
  | 34 => [(3,0)]
  | 35 => [(2,5)]
  | 36 => [(6,0)]
  | 37 => [(7,1)]
  | 38 => [(7,5)]
  | 39 => [(6,0)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(1,4)]
  | 43 => [(0,5)]
  | 44 => [(4,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(4,0)]
  | 48 => [(7,3)]
  | 49 => [(8,2)]
  | 50 => [(8,0)]
  | 51 => [(7,1)]
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
  | 77 => [(8,0)]
  | 78 => [(8,1)]
  | 79 => [(1,5)]
  | 80 => [(6,1)]
  | 81 => [(8,1)]
  | 82 => [(6,5)]
  | 83 => [(0,4)]
  | 84 => [(5,4)]
  | 85 => [(5,5),(8,5)]
  | 86 => [(7,0)]
  | 87 => [(8,3)]
  | 88 => [(5,5),(8,5)]
  | 89 => [(7,0)]
  | _ => [(4,3)]
def root0Node22Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(8,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(8,1)]
  | 12 => some [(1,5)]
  | 13 => some [(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(4,2)]
  | 18 => some [(5,3)]
  | 19 => some [(5,5)]
  | 20 => some [(7,0)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(1,4)]
  | 27 => some [(0,5)]
  | 28 => some [(4,4)]
  | 29 => some [(1,4)]
  | 30 => some [(5,2)]
  | 31 => some [(8,0)]
  | 32 => some [(8,3)]
  | 33 => some [(5,5)]
  | 34 => some [(3,0)]
  | 35 => some [(2,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(0,5)]
  | 44 => some [(4,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(8,2)]
  | 50 => some [(8,0)]
  | 51 => some [(7,1)]
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
  | 77 => some [(8,0)]
  | 78 => some [(8,1)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(8,1)]
  | 82 => some [(6,5)]
  | 83 => some [(0,4)]
  | 84 => some [(5,4)]
  | 85 => some [(5,5),(8,5)]
  | 86 => some [(7,0)]
  | 87 => some [(8,3)]
  | 88 => some [(5,5),(8,5)]
  | 89 => some [(7,0)]
  | _ => some [(4,3)]
theorem root0Node22Domains1_fast_eq : root0Node22Domains1 = expandDomains root0Node22Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node22Domains1 v = expandDomains root0Node22Domains1Fast v from by decide) v
theorem root0Node22Step1Chunk0_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_0⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk0_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_1⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk0_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_2⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk0_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_3⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk0_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_4⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk0_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_5⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk1_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_0⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk1_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_1⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk1_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_2⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk1_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_3⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk1_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_4⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk1_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_5⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk2_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_0⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk2_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_1⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk2_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_2⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk2_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_3⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk2_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_4⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk2_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_5⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk3_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_0⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk3_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_1⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk3_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_2⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk3_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_3⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk3_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_4⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk3_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_5⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk4_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_0⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk4_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_1⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk4_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_2⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk4_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_3⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk4_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_4⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk4_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_5⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk5_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_0⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk5_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_1⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk5_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_2⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk5_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_3⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk5_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_4⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk5_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_5⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk6_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_0⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk6_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_1⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk6_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_2⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk6_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_3⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk6_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_4⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk6_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_5⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk7_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_0⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk7_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_1⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk7_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_2⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk7_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_3⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk7_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_4⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk7_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_5⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk8_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_0⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk8_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_1⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk8_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_2⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk8_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_3⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk8_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_4⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk8_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_5⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Narrowing_checked :
    checkNarrowing table51 root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_flatten table51Scope [table51Rows0_0,table51Rows0_1,table51Rows0_2,table51Rows0_3,table51Rows0_4,table51Rows0_5,table51Rows1_0,table51Rows1_1,table51Rows1_2,table51Rows1_3,table51Rows1_4,table51Rows1_5,table51Rows2_0,table51Rows2_1,table51Rows2_2,table51Rows2_3,table51Rows2_4,table51Rows2_5,table51Rows3_0,table51Rows3_1,table51Rows3_2,table51Rows3_3,table51Rows3_4,table51Rows3_5,table51Rows4_0,table51Rows4_1,table51Rows4_2,table51Rows4_3,table51Rows4_4,table51Rows4_5,table51Rows5_0,table51Rows5_1,table51Rows5_2,table51Rows5_3,table51Rows5_4,table51Rows5_5,table51Rows6_0,table51Rows6_1,table51Rows6_2,table51Rows6_3,table51Rows6_4,table51Rows6_5,table51Rows7_0,table51Rows7_1,table51Rows7_2,table51Rows7_3,table51Rows7_4,table51Rows7_5,table51Rows8_0,table51Rows8_1,table51Rows8_2,table51Rows8_3,table51Rows8_4,table51Rows8_5]
    root0Node22Domains0 root0Node22Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node22Step1Chunk0_0_checked, root0Node22Step1Chunk0_1_checked, root0Node22Step1Chunk0_2_checked, root0Node22Step1Chunk0_3_checked, root0Node22Step1Chunk0_4_checked, root0Node22Step1Chunk0_5_checked, root0Node22Step1Chunk1_0_checked, root0Node22Step1Chunk1_1_checked, root0Node22Step1Chunk1_2_checked, root0Node22Step1Chunk1_3_checked, root0Node22Step1Chunk1_4_checked, root0Node22Step1Chunk1_5_checked, root0Node22Step1Chunk2_0_checked, root0Node22Step1Chunk2_1_checked, root0Node22Step1Chunk2_2_checked, root0Node22Step1Chunk2_3_checked, root0Node22Step1Chunk2_4_checked, root0Node22Step1Chunk2_5_checked, root0Node22Step1Chunk3_0_checked, root0Node22Step1Chunk3_1_checked, root0Node22Step1Chunk3_2_checked, root0Node22Step1Chunk3_3_checked, root0Node22Step1Chunk3_4_checked, root0Node22Step1Chunk3_5_checked, root0Node22Step1Chunk4_0_checked, root0Node22Step1Chunk4_1_checked, root0Node22Step1Chunk4_2_checked, root0Node22Step1Chunk4_3_checked, root0Node22Step1Chunk4_4_checked, root0Node22Step1Chunk4_5_checked, root0Node22Step1Chunk5_0_checked, root0Node22Step1Chunk5_1_checked, root0Node22Step1Chunk5_2_checked, root0Node22Step1Chunk5_3_checked, root0Node22Step1Chunk5_4_checked, root0Node22Step1Chunk5_5_checked, root0Node22Step1Chunk6_0_checked, root0Node22Step1Chunk6_1_checked, root0Node22Step1Chunk6_2_checked, root0Node22Step1Chunk6_3_checked, root0Node22Step1Chunk6_4_checked, root0Node22Step1Chunk6_5_checked, root0Node22Step1Chunk7_0_checked, root0Node22Step1Chunk7_1_checked, root0Node22Step1Chunk7_2_checked, root0Node22Step1Chunk7_3_checked, root0Node22Step1Chunk7_4_checked, root0Node22Step1Chunk7_5_checked, root0Node22Step1Chunk8_0_checked, root0Node22Step1Chunk8_1_checked, root0Node22Step1Chunk8_2_checked, root0Node22Step1Chunk8_3_checked, root0Node22Step1Chunk8_4_checked, root0Node22Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node22Step1_checked :
    checkReplacement table51 root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq
    root0Node22Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
