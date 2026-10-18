module

public import SpectreFinite.RadiusFiveRoot6Part1
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable4
public import SpectreFinite.RadiusFiveTable52
public import SpectreFinite.RadiusFiveTable57
public import SpectreFinite.RadiusFiveTable6

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node2Domains0 : Domains 91 State := restrict root6Node1Domains4 0 (5,2)
def root6Node2Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2),(5,2),(8,2)]
  | 4 => some [(5,0),(5,3)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4),(8,4)]
  | 11 => some [(0,0),(1,3)]
  | 12 => some [(7,2),(8,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(7,5)]
  | 16 => some [(0,3)]
  | 17 => some [(8,1)]
  | 18 => some [(1,5),(6,5)]
  | 19 => some [(0,4),(6,1)]
  | 20 => some [(5,1),(5,4),(8,1)]
  | 21 => some [(7,2)]
  | 22 => some [(7,4)]
  | 23 => some [(1,3)]
  | 24 => some [(4,2)]
  | 25 => some [(5,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3),(8,3)]
  | 29 => some [(1,5),(3,5),(5,5)]
  | 30 => some [(1,1),(6,1)]
  | 31 => some [(8,1)]
  | 32 => some [(6,5)]
  | 33 => some [(0,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,0),(2,4),(4,4)]
  | 40 => some [(7,0),(8,0)]
  | 41 => some [(8,3)]
  | 42 => some [(5,5)]
  | 43 => some [(3,0)]
  | 44 => some [(2,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(3,1),(7,1)]
  | 50 => some [(0,1),(1,5),(6,5),(7,5)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(4,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(4,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0),(8,0)]
  | 60 => some [(4,5),(7,3)]
  | 61 => some [(6,0)]
  | 62 => some [(7,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(5,1)]
  | 66 => some [(0,1)]
  | 67 => some [(6,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0),(6,4)]
  | 70 => some [(5,0)]
  | 71 => some [(4,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(8,5)]
  | 75 => some [(1,0)]
  | 76 => some [(7,1)]
  | 77 => some [(1,5),(7,5)]
  | 78 => some [(0,0)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3),(6,3)]
  | 82 => some [(7,2),(8,2)]
  | 83 => some [(4,0),(5,0),(8,0)]
  | 84 => some [(4,5),(7,3)]
  | 85 => some [(6,1)]
  | 86 => some [(4,1),(8,1)]
  | 87 => some [(0,2),(6,5)]
  | 88 => some [(0,4),(1,1)]
  | 89 => some [(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,4)]
theorem root6Node2Domains0_fast_eq : root6Node2Domains0 = expandDomains root6Node2Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node2Domains0 v = expandDomains root6Node2Domains0Fast v from by decide) v
def root6Node2Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,2)]
  | 1 => [(8,0)]
  | 2 => [(7,3)]
  | 3 => [(5,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(6,4)]
  | 9 => [(1,2)]
  | 10 => [(8,4)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(7,5)]
  | 16 => [(0,3)]
  | 17 => [(8,1)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(5,1)]
  | 21 => [(7,2)]
  | 22 => [(7,4)]
  | 23 => [(1,3)]
  | 24 => [(4,2)]
  | 25 => [(5,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(1,1),(6,1)]
  | 31 => [(8,1)]
  | 32 => [(6,5)]
  | 33 => [(0,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(2,0),(2,4),(4,4)]
  | 40 => [(7,0),(8,0)]
  | 41 => [(8,3)]
  | 42 => [(5,5)]
  | 43 => [(3,0)]
  | 44 => [(2,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(3,1),(7,1)]
  | 50 => [(0,1),(1,5),(6,5),(7,5)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(4,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(4,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0),(8,0)]
  | 60 => [(4,5),(7,3)]
  | 61 => [(6,0)]
  | 62 => [(7,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(5,1)]
  | 66 => [(0,1)]
  | 67 => [(6,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0),(6,4)]
  | 70 => [(5,0)]
  | 71 => [(4,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(8,5)]
  | 75 => [(1,0)]
  | 76 => [(7,1)]
  | 77 => [(1,5),(7,5)]
  | 78 => [(0,0)]
  | 79 => [(7,2)]
  | 80 => [(7,4)]
  | 81 => [(1,3),(6,3)]
  | 82 => [(7,2),(8,2)]
  | 83 => [(4,0),(5,0),(8,0)]
  | 84 => [(4,5),(7,3)]
  | 85 => [(6,1)]
  | 86 => [(4,1),(8,1)]
  | 87 => [(0,2),(6,5)]
  | 88 => [(0,4),(1,1)]
  | 89 => [(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,4)]
def root6Node2Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(5,2)]
  | 4 => some [(5,0)]
  | 5 => some [(4,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(8,4)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(7,5)]
  | 16 => some [(0,3)]
  | 17 => some [(8,1)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(7,2)]
  | 22 => some [(7,4)]
  | 23 => some [(1,3)]
  | 24 => some [(4,2)]
  | 25 => some [(5,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(1,1),(6,1)]
  | 31 => some [(8,1)]
  | 32 => some [(6,5)]
  | 33 => some [(0,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,0),(2,4),(4,4)]
  | 40 => some [(7,0),(8,0)]
  | 41 => some [(8,3)]
  | 42 => some [(5,5)]
  | 43 => some [(3,0)]
  | 44 => some [(2,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(3,1),(7,1)]
  | 50 => some [(0,1),(1,5),(6,5),(7,5)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(4,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(4,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0),(8,0)]
  | 60 => some [(4,5),(7,3)]
  | 61 => some [(6,0)]
  | 62 => some [(7,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(5,1)]
  | 66 => some [(0,1)]
  | 67 => some [(6,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0),(6,4)]
  | 70 => some [(5,0)]
  | 71 => some [(4,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(8,5)]
  | 75 => some [(1,0)]
  | 76 => some [(7,1)]
  | 77 => some [(1,5),(7,5)]
  | 78 => some [(0,0)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3),(6,3)]
  | 82 => some [(7,2),(8,2)]
  | 83 => some [(4,0),(5,0),(8,0)]
  | 84 => some [(4,5),(7,3)]
  | 85 => some [(6,1)]
  | 86 => some [(4,1),(8,1)]
  | 87 => some [(0,2),(6,5)]
  | 88 => some [(0,4),(1,1)]
  | 89 => some [(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,4)]
theorem root6Node2Domains1_fast_eq : root6Node2Domains1 = expandDomains root6Node2Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node2Domains1 v = expandDomains root6Node2Domains1Fast v from by decide) v
theorem root6Node2Step1Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Narrowing_checked :
    checkNarrowing table4 root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_flatten table4Scope [table4Rows0_0,table4Rows0_1,table4Rows0_2,table4Rows0_3,table4Rows0_4,table4Rows0_5,table4Rows1_0,table4Rows1_1,table4Rows1_2,table4Rows1_3,table4Rows1_4,table4Rows1_5,table4Rows2_0,table4Rows2_1,table4Rows2_2,table4Rows2_3,table4Rows2_4,table4Rows2_5,table4Rows3_0,table4Rows3_1,table4Rows3_2,table4Rows3_3,table4Rows3_4,table4Rows3_5,table4Rows4_0,table4Rows4_1,table4Rows4_2,table4Rows4_3,table4Rows4_4,table4Rows4_5,table4Rows5_0,table4Rows5_1,table4Rows5_2,table4Rows5_3,table4Rows5_4,table4Rows5_5,table4Rows6_0,table4Rows6_1,table4Rows6_2,table4Rows6_3,table4Rows6_4,table4Rows6_5,table4Rows7_0,table4Rows7_1,table4Rows7_2,table4Rows7_3,table4Rows7_4,table4Rows7_5,table4Rows8_0,table4Rows8_1,table4Rows8_2,table4Rows8_3,table4Rows8_4,table4Rows8_5]
    root6Node2Domains0 root6Node2Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node2Step1Chunk0_0_checked, root6Node2Step1Chunk0_1_checked, root6Node2Step1Chunk0_2_checked, root6Node2Step1Chunk0_3_checked, root6Node2Step1Chunk0_4_checked, root6Node2Step1Chunk0_5_checked, root6Node2Step1Chunk1_0_checked, root6Node2Step1Chunk1_1_checked, root6Node2Step1Chunk1_2_checked, root6Node2Step1Chunk1_3_checked, root6Node2Step1Chunk1_4_checked, root6Node2Step1Chunk1_5_checked, root6Node2Step1Chunk2_0_checked, root6Node2Step1Chunk2_1_checked, root6Node2Step1Chunk2_2_checked, root6Node2Step1Chunk2_3_checked, root6Node2Step1Chunk2_4_checked, root6Node2Step1Chunk2_5_checked, root6Node2Step1Chunk3_0_checked, root6Node2Step1Chunk3_1_checked, root6Node2Step1Chunk3_2_checked, root6Node2Step1Chunk3_3_checked, root6Node2Step1Chunk3_4_checked, root6Node2Step1Chunk3_5_checked, root6Node2Step1Chunk4_0_checked, root6Node2Step1Chunk4_1_checked, root6Node2Step1Chunk4_2_checked, root6Node2Step1Chunk4_3_checked, root6Node2Step1Chunk4_4_checked, root6Node2Step1Chunk4_5_checked, root6Node2Step1Chunk5_0_checked, root6Node2Step1Chunk5_1_checked, root6Node2Step1Chunk5_2_checked, root6Node2Step1Chunk5_3_checked, root6Node2Step1Chunk5_4_checked, root6Node2Step1Chunk5_5_checked, root6Node2Step1Chunk6_0_checked, root6Node2Step1Chunk6_1_checked, root6Node2Step1Chunk6_2_checked, root6Node2Step1Chunk6_3_checked, root6Node2Step1Chunk6_4_checked, root6Node2Step1Chunk6_5_checked, root6Node2Step1Chunk7_0_checked, root6Node2Step1Chunk7_1_checked, root6Node2Step1Chunk7_2_checked, root6Node2Step1Chunk7_3_checked, root6Node2Step1Chunk7_4_checked, root6Node2Step1Chunk7_5_checked, root6Node2Step1Chunk8_0_checked, root6Node2Step1Chunk8_1_checked, root6Node2Step1Chunk8_2_checked, root6Node2Step1Chunk8_3_checked, root6Node2Step1Chunk8_4_checked, root6Node2Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node2Step1_checked :
    checkReplacement table4 root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq
    root6Node2Step1Narrowing_checked (by decide)
def root6Node2Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,2)]
  | 1 => [(8,0)]
  | 2 => [(7,3)]
  | 3 => [(5,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(6,4)]
  | 9 => [(1,2)]
  | 10 => [(8,4)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(7,5)]
  | 16 => [(0,3)]
  | 17 => [(8,1)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(5,1)]
  | 21 => [(7,2)]
  | 22 => [(7,4)]
  | 23 => [(1,3)]
  | 24 => [(4,2)]
  | 25 => [(5,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(1,1),(6,1)]
  | 31 => [(8,1)]
  | 32 => [(6,5)]
  | 33 => [(0,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(4,4)]
  | 40 => [(7,0),(8,0)]
  | 41 => [(8,3)]
  | 42 => [(5,5)]
  | 43 => [(3,0)]
  | 44 => [(2,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(7,1)]
  | 50 => [(1,5)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(4,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(4,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(6,0)]
  | 62 => [(7,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(5,1)]
  | 66 => [(0,1)]
  | 67 => [(6,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0)]
  | 70 => [(5,0)]
  | 71 => [(4,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(8,5)]
  | 75 => [(1,0)]
  | 76 => [(7,1)]
  | 77 => [(1,5)]
  | 78 => [(0,0)]
  | 79 => [(7,2)]
  | 80 => [(7,4)]
  | 81 => [(1,3)]
  | 82 => [(8,2)]
  | 83 => [(5,0)]
  | 84 => [(4,5)]
  | 85 => [(6,1)]
  | 86 => [(4,1),(8,1)]
  | 87 => [(6,5)]
  | 88 => [(0,4)]
  | 89 => [(5,4)]
  | _ => [(0,0)]
def root6Node2Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(5,2)]
  | 4 => some [(5,0)]
  | 5 => some [(4,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(8,4)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(7,5)]
  | 16 => some [(0,3)]
  | 17 => some [(8,1)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(7,2)]
  | 22 => some [(7,4)]
  | 23 => some [(1,3)]
  | 24 => some [(4,2)]
  | 25 => some [(5,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(1,1),(6,1)]
  | 31 => some [(8,1)]
  | 32 => some [(6,5)]
  | 33 => some [(0,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(7,0),(8,0)]
  | 41 => some [(8,3)]
  | 42 => some [(5,5)]
  | 43 => some [(3,0)]
  | 44 => some [(2,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(4,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(4,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,0)]
  | 62 => some [(7,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(5,1)]
  | 66 => some [(0,1)]
  | 67 => some [(6,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(5,0)]
  | 71 => some [(4,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(8,5)]
  | 75 => some [(1,0)]
  | 76 => some [(7,1)]
  | 77 => some [(1,5)]
  | 78 => some [(0,0)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3)]
  | 82 => some [(8,2)]
  | 83 => some [(5,0)]
  | 84 => some [(4,5)]
  | 85 => some [(6,1)]
  | 86 => some [(4,1),(8,1)]
  | 87 => some [(6,5)]
  | 88 => some [(0,4)]
  | 89 => some [(5,4)]
  | _ => some [(0,0)]
theorem root6Node2Domains2_fast_eq : root6Node2Domains2 = expandDomains root6Node2Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node2Domains2 v = expandDomains root6Node2Domains2Fast v from by decide) v
theorem root6Node2Step2Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Narrowing_checked :
    checkNarrowing table57 root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root6Node2Domains1 root6Node2Domains2 (by
      simp only [List.all_cons, List.all_nil, root6Node2Step2Chunk0_0_checked, root6Node2Step2Chunk0_1_checked, root6Node2Step2Chunk0_2_checked, root6Node2Step2Chunk0_3_checked, root6Node2Step2Chunk0_4_checked, root6Node2Step2Chunk0_5_checked, root6Node2Step2Chunk1_0_checked, root6Node2Step2Chunk1_1_checked, root6Node2Step2Chunk1_2_checked, root6Node2Step2Chunk1_3_checked, root6Node2Step2Chunk1_4_checked, root6Node2Step2Chunk1_5_checked, root6Node2Step2Chunk2_0_checked, root6Node2Step2Chunk2_1_checked, root6Node2Step2Chunk2_2_checked, root6Node2Step2Chunk2_3_checked, root6Node2Step2Chunk2_4_checked, root6Node2Step2Chunk2_5_checked, root6Node2Step2Chunk3_0_checked, root6Node2Step2Chunk3_1_checked, root6Node2Step2Chunk3_2_checked, root6Node2Step2Chunk3_3_checked, root6Node2Step2Chunk3_4_checked, root6Node2Step2Chunk3_5_checked, root6Node2Step2Chunk4_0_checked, root6Node2Step2Chunk4_1_checked, root6Node2Step2Chunk4_2_checked, root6Node2Step2Chunk4_3_checked, root6Node2Step2Chunk4_4_checked, root6Node2Step2Chunk4_5_checked, root6Node2Step2Chunk5_0_checked, root6Node2Step2Chunk5_1_checked, root6Node2Step2Chunk5_2_checked, root6Node2Step2Chunk5_3_checked, root6Node2Step2Chunk5_4_checked, root6Node2Step2Chunk5_5_checked, root6Node2Step2Chunk6_0_checked, root6Node2Step2Chunk6_1_checked, root6Node2Step2Chunk6_2_checked, root6Node2Step2Chunk6_3_checked, root6Node2Step2Chunk6_4_checked, root6Node2Step2Chunk6_5_checked, root6Node2Step2Chunk7_0_checked, root6Node2Step2Chunk7_1_checked, root6Node2Step2Chunk7_2_checked, root6Node2Step2Chunk7_3_checked, root6Node2Step2Chunk7_4_checked, root6Node2Step2Chunk7_5_checked, root6Node2Step2Chunk8_0_checked, root6Node2Step2Chunk8_1_checked, root6Node2Step2Chunk8_2_checked, root6Node2Step2Chunk8_3_checked, root6Node2Step2Chunk8_4_checked, root6Node2Step2Chunk8_5_checked, Bool.true_and])
theorem root6Node2Step2_checked :
    checkReplacement table57 root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq
    root6Node2Step2Narrowing_checked (by decide)
def root6Node2Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,2)]
  | 1 => [(8,0)]
  | 2 => [(7,3)]
  | 3 => [(5,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(6,4)]
  | 9 => [(1,2)]
  | 10 => [(8,4)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(7,5)]
  | 16 => [(0,3)]
  | 17 => [(8,1)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(5,1)]
  | 21 => [(7,2)]
  | 22 => [(7,4)]
  | 23 => [(1,3)]
  | 24 => [(4,2)]
  | 25 => [(5,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(6,1)]
  | 31 => [(8,1)]
  | 32 => [(6,5)]
  | 33 => [(0,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(4,4)]
  | 40 => [(7,0)]
  | 41 => [(8,3)]
  | 42 => [(5,5)]
  | 43 => [(3,0)]
  | 44 => [(2,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(7,1)]
  | 50 => [(1,5)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(4,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(4,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(6,0)]
  | 62 => [(7,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(5,1)]
  | 66 => [(0,1)]
  | 67 => [(6,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0)]
  | 70 => [(5,0)]
  | 71 => [(4,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(8,5)]
  | 75 => [(1,0)]
  | 76 => [(7,1)]
  | 77 => [(1,5)]
  | 78 => [(0,0)]
  | 79 => [(7,2)]
  | 80 => [(7,4)]
  | 81 => [(1,3)]
  | 82 => [(8,2)]
  | 83 => [(5,0)]
  | 84 => [(4,5)]
  | 85 => [(6,1)]
  | 86 => [(4,1),(8,1)]
  | 87 => [(6,5)]
  | 88 => [(0,4)]
  | 89 => [(5,4)]
  | _ => [(0,0)]
def root6Node2Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(5,2)]
  | 4 => some [(5,0)]
  | 5 => some [(4,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(8,4)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(7,5)]
  | 16 => some [(0,3)]
  | 17 => some [(8,1)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(7,2)]
  | 22 => some [(7,4)]
  | 23 => some [(1,3)]
  | 24 => some [(4,2)]
  | 25 => some [(5,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(6,1)]
  | 31 => some [(8,1)]
  | 32 => some [(6,5)]
  | 33 => some [(0,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(7,0)]
  | 41 => some [(8,3)]
  | 42 => some [(5,5)]
  | 43 => some [(3,0)]
  | 44 => some [(2,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(4,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(4,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,0)]
  | 62 => some [(7,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(5,1)]
  | 66 => some [(0,1)]
  | 67 => some [(6,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(5,0)]
  | 71 => some [(4,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(8,5)]
  | 75 => some [(1,0)]
  | 76 => some [(7,1)]
  | 77 => some [(1,5)]
  | 78 => some [(0,0)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3)]
  | 82 => some [(8,2)]
  | 83 => some [(5,0)]
  | 84 => some [(4,5)]
  | 85 => some [(6,1)]
  | 86 => some [(4,1),(8,1)]
  | 87 => some [(6,5)]
  | 88 => some [(0,4)]
  | 89 => some [(5,4)]
  | _ => some [(0,0)]
theorem root6Node2Domains3_fast_eq : root6Node2Domains3 = expandDomains root6Node2Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node2Domains3 v = expandDomains root6Node2Domains3Fast v from by decide) v
theorem root6Node2Step3Chunk0_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_0⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk0_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_1⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk0_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_2⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk0_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_3⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk0_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_4⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk0_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_5⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk1_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_0⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk1_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_1⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk1_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_2⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk1_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_3⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk1_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_4⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk1_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_5⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk2_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_0⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk2_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_1⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk2_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_2⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk2_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_3⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk2_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_4⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk2_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_5⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk3_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_0⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk3_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_1⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk3_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_2⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk3_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_3⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk3_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_4⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk3_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_5⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk4_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_0⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk4_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_1⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk4_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_2⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk4_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_3⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk4_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_4⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk4_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_5⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk5_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_0⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk5_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_1⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk5_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_2⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk5_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_3⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk5_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_4⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk5_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_5⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk6_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_0⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk6_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_1⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk6_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_2⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk6_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_3⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk6_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_4⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk6_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_5⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk7_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_0⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk7_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_1⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk7_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_2⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk7_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_3⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk7_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_4⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk7_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_5⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk8_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_0⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk8_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_1⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk8_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_2⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk8_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_3⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk8_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_4⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Chunk8_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_5⟩
      root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq (by decide)
theorem root6Node2Step3Narrowing_checked :
    checkNarrowing table6 root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkNarrowing_flatten table6Scope [table6Rows0_0,table6Rows0_1,table6Rows0_2,table6Rows0_3,table6Rows0_4,table6Rows0_5,table6Rows1_0,table6Rows1_1,table6Rows1_2,table6Rows1_3,table6Rows1_4,table6Rows1_5,table6Rows2_0,table6Rows2_1,table6Rows2_2,table6Rows2_3,table6Rows2_4,table6Rows2_5,table6Rows3_0,table6Rows3_1,table6Rows3_2,table6Rows3_3,table6Rows3_4,table6Rows3_5,table6Rows4_0,table6Rows4_1,table6Rows4_2,table6Rows4_3,table6Rows4_4,table6Rows4_5,table6Rows5_0,table6Rows5_1,table6Rows5_2,table6Rows5_3,table6Rows5_4,table6Rows5_5,table6Rows6_0,table6Rows6_1,table6Rows6_2,table6Rows6_3,table6Rows6_4,table6Rows6_5,table6Rows7_0,table6Rows7_1,table6Rows7_2,table6Rows7_3,table6Rows7_4,table6Rows7_5,table6Rows8_0,table6Rows8_1,table6Rows8_2,table6Rows8_3,table6Rows8_4,table6Rows8_5]
    root6Node2Domains2 root6Node2Domains3 (by
      simp only [List.all_cons, List.all_nil, root6Node2Step3Chunk0_0_checked, root6Node2Step3Chunk0_1_checked, root6Node2Step3Chunk0_2_checked, root6Node2Step3Chunk0_3_checked, root6Node2Step3Chunk0_4_checked, root6Node2Step3Chunk0_5_checked, root6Node2Step3Chunk1_0_checked, root6Node2Step3Chunk1_1_checked, root6Node2Step3Chunk1_2_checked, root6Node2Step3Chunk1_3_checked, root6Node2Step3Chunk1_4_checked, root6Node2Step3Chunk1_5_checked, root6Node2Step3Chunk2_0_checked, root6Node2Step3Chunk2_1_checked, root6Node2Step3Chunk2_2_checked, root6Node2Step3Chunk2_3_checked, root6Node2Step3Chunk2_4_checked, root6Node2Step3Chunk2_5_checked, root6Node2Step3Chunk3_0_checked, root6Node2Step3Chunk3_1_checked, root6Node2Step3Chunk3_2_checked, root6Node2Step3Chunk3_3_checked, root6Node2Step3Chunk3_4_checked, root6Node2Step3Chunk3_5_checked, root6Node2Step3Chunk4_0_checked, root6Node2Step3Chunk4_1_checked, root6Node2Step3Chunk4_2_checked, root6Node2Step3Chunk4_3_checked, root6Node2Step3Chunk4_4_checked, root6Node2Step3Chunk4_5_checked, root6Node2Step3Chunk5_0_checked, root6Node2Step3Chunk5_1_checked, root6Node2Step3Chunk5_2_checked, root6Node2Step3Chunk5_3_checked, root6Node2Step3Chunk5_4_checked, root6Node2Step3Chunk5_5_checked, root6Node2Step3Chunk6_0_checked, root6Node2Step3Chunk6_1_checked, root6Node2Step3Chunk6_2_checked, root6Node2Step3Chunk6_3_checked, root6Node2Step3Chunk6_4_checked, root6Node2Step3Chunk6_5_checked, root6Node2Step3Chunk7_0_checked, root6Node2Step3Chunk7_1_checked, root6Node2Step3Chunk7_2_checked, root6Node2Step3Chunk7_3_checked, root6Node2Step3Chunk7_4_checked, root6Node2Step3Chunk7_5_checked, root6Node2Step3Chunk8_0_checked, root6Node2Step3Chunk8_1_checked, root6Node2Step3Chunk8_2_checked, root6Node2Step3Chunk8_3_checked, root6Node2Step3Chunk8_4_checked, root6Node2Step3Chunk8_5_checked, Bool.true_and])
theorem root6Node2Step3_checked :
    checkReplacement table6 root6Node2Domains2 root6Node2Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root6Node2Domains2 root6Node2Domains3
    root6Node2Domains2Fast root6Node2Domains3Fast
    root6Node2Domains2_fast_eq root6Node2Domains3_fast_eq
    root6Node2Step3Narrowing_checked (by decide)
def root6Node2Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,2)]
  | 1 => [(8,0)]
  | 2 => [(7,3)]
  | 3 => [(5,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(6,4)]
  | 9 => [(1,2)]
  | 10 => [(8,4)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(7,5)]
  | 16 => [(0,3)]
  | 17 => [(8,1)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(5,1)]
  | 21 => [(7,2)]
  | 22 => [(7,4)]
  | 23 => [(1,3)]
  | 24 => [(4,2)]
  | 25 => [(5,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(6,1)]
  | 31 => [(8,1)]
  | 32 => [(6,5)]
  | 33 => [(0,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(4,4)]
  | 40 => [(7,0)]
  | 41 => [(8,3)]
  | 42 => [(5,5)]
  | 43 => [(3,0)]
  | 44 => [(2,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(7,1)]
  | 50 => [(1,5)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(4,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(4,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(6,0)]
  | 62 => [(7,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(5,1)]
  | 66 => [(0,1)]
  | 67 => [(6,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0)]
  | 70 => [(5,0)]
  | 71 => [(4,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(8,5)]
  | 75 => [(1,0)]
  | 76 => [(7,1)]
  | 77 => [(1,5)]
  | 78 => [(0,0)]
  | 79 => [(7,2)]
  | 80 => [(7,4)]
  | 81 => [(1,3)]
  | 82 => [(8,2)]
  | 83 => [(5,0)]
  | 84 => [(4,5)]
  | 85 => [(6,1)]
  | 86 => [(8,1)]
  | 87 => [(6,5)]
  | 88 => [(0,4)]
  | 89 => [(5,4)]
  | _ => [(0,0)]
def root6Node2Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(5,2)]
  | 4 => some [(5,0)]
  | 5 => some [(4,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(8,4)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(7,5)]
  | 16 => some [(0,3)]
  | 17 => some [(8,1)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(7,2)]
  | 22 => some [(7,4)]
  | 23 => some [(1,3)]
  | 24 => some [(4,2)]
  | 25 => some [(5,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(6,1)]
  | 31 => some [(8,1)]
  | 32 => some [(6,5)]
  | 33 => some [(0,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(7,0)]
  | 41 => some [(8,3)]
  | 42 => some [(5,5)]
  | 43 => some [(3,0)]
  | 44 => some [(2,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(4,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(4,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,0)]
  | 62 => some [(7,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(5,1)]
  | 66 => some [(0,1)]
  | 67 => some [(6,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(5,0)]
  | 71 => some [(4,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(8,5)]
  | 75 => some [(1,0)]
  | 76 => some [(7,1)]
  | 77 => some [(1,5)]
  | 78 => some [(0,0)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3)]
  | 82 => some [(8,2)]
  | 83 => some [(5,0)]
  | 84 => some [(4,5)]
  | 85 => some [(6,1)]
  | 86 => some [(8,1)]
  | 87 => some [(6,5)]
  | 88 => some [(0,4)]
  | 89 => some [(5,4)]
  | _ => some [(0,0)]
theorem root6Node2Domains4_fast_eq : root6Node2Domains4 = expandDomains root6Node2Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node2Domains4 v = expandDomains root6Node2Domains4Fast v from by decide) v
theorem root6Node2Step4Chunk0_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_0⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk0_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_1⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk0_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_2⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk0_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_3⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk0_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_4⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk0_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_5⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk1_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_0⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk1_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_1⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk1_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_2⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk1_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_3⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk1_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_4⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk1_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_5⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk2_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_0⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk2_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_1⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk2_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_2⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk2_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_3⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk2_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_4⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk2_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_5⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk3_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_0⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk3_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_1⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk3_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_2⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk3_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_3⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk3_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_4⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk3_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_5⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk4_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_0⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk4_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_1⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk4_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_2⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk4_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_3⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk4_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_4⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk4_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_5⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk5_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_0⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk5_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_1⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk5_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_2⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk5_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_3⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk5_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_4⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk5_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_5⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk6_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_0⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk6_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_1⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk6_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_2⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk6_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_3⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk6_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_4⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk6_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_5⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk7_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_0⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk7_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_1⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk7_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_2⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk7_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_3⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk7_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_4⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk7_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_5⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk8_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_0⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk8_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_1⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk8_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_2⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk8_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_3⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk8_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_4⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Chunk8_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_5⟩
      root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq (by decide)
theorem root6Node2Step4Narrowing_checked :
    checkNarrowing table52 root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkNarrowing_flatten table52Scope [table52Rows0_0,table52Rows0_1,table52Rows0_2,table52Rows0_3,table52Rows0_4,table52Rows0_5,table52Rows1_0,table52Rows1_1,table52Rows1_2,table52Rows1_3,table52Rows1_4,table52Rows1_5,table52Rows2_0,table52Rows2_1,table52Rows2_2,table52Rows2_3,table52Rows2_4,table52Rows2_5,table52Rows3_0,table52Rows3_1,table52Rows3_2,table52Rows3_3,table52Rows3_4,table52Rows3_5,table52Rows4_0,table52Rows4_1,table52Rows4_2,table52Rows4_3,table52Rows4_4,table52Rows4_5,table52Rows5_0,table52Rows5_1,table52Rows5_2,table52Rows5_3,table52Rows5_4,table52Rows5_5,table52Rows6_0,table52Rows6_1,table52Rows6_2,table52Rows6_3,table52Rows6_4,table52Rows6_5,table52Rows7_0,table52Rows7_1,table52Rows7_2,table52Rows7_3,table52Rows7_4,table52Rows7_5,table52Rows8_0,table52Rows8_1,table52Rows8_2,table52Rows8_3,table52Rows8_4,table52Rows8_5]
    root6Node2Domains3 root6Node2Domains4 (by
      simp only [List.all_cons, List.all_nil, root6Node2Step4Chunk0_0_checked, root6Node2Step4Chunk0_1_checked, root6Node2Step4Chunk0_2_checked, root6Node2Step4Chunk0_3_checked, root6Node2Step4Chunk0_4_checked, root6Node2Step4Chunk0_5_checked, root6Node2Step4Chunk1_0_checked, root6Node2Step4Chunk1_1_checked, root6Node2Step4Chunk1_2_checked, root6Node2Step4Chunk1_3_checked, root6Node2Step4Chunk1_4_checked, root6Node2Step4Chunk1_5_checked, root6Node2Step4Chunk2_0_checked, root6Node2Step4Chunk2_1_checked, root6Node2Step4Chunk2_2_checked, root6Node2Step4Chunk2_3_checked, root6Node2Step4Chunk2_4_checked, root6Node2Step4Chunk2_5_checked, root6Node2Step4Chunk3_0_checked, root6Node2Step4Chunk3_1_checked, root6Node2Step4Chunk3_2_checked, root6Node2Step4Chunk3_3_checked, root6Node2Step4Chunk3_4_checked, root6Node2Step4Chunk3_5_checked, root6Node2Step4Chunk4_0_checked, root6Node2Step4Chunk4_1_checked, root6Node2Step4Chunk4_2_checked, root6Node2Step4Chunk4_3_checked, root6Node2Step4Chunk4_4_checked, root6Node2Step4Chunk4_5_checked, root6Node2Step4Chunk5_0_checked, root6Node2Step4Chunk5_1_checked, root6Node2Step4Chunk5_2_checked, root6Node2Step4Chunk5_3_checked, root6Node2Step4Chunk5_4_checked, root6Node2Step4Chunk5_5_checked, root6Node2Step4Chunk6_0_checked, root6Node2Step4Chunk6_1_checked, root6Node2Step4Chunk6_2_checked, root6Node2Step4Chunk6_3_checked, root6Node2Step4Chunk6_4_checked, root6Node2Step4Chunk6_5_checked, root6Node2Step4Chunk7_0_checked, root6Node2Step4Chunk7_1_checked, root6Node2Step4Chunk7_2_checked, root6Node2Step4Chunk7_3_checked, root6Node2Step4Chunk7_4_checked, root6Node2Step4Chunk7_5_checked, root6Node2Step4Chunk8_0_checked, root6Node2Step4Chunk8_1_checked, root6Node2Step4Chunk8_2_checked, root6Node2Step4Chunk8_3_checked, root6Node2Step4Chunk8_4_checked, root6Node2Step4Chunk8_5_checked, Bool.true_and])
theorem root6Node2Step4_checked :
    checkReplacement table52 root6Node2Domains3 root6Node2Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root6Node2Domains3 root6Node2Domains4
    root6Node2Domains3Fast root6Node2Domains4Fast
    root6Node2Domains3_fast_eq root6Node2Domains4_fast_eq
    root6Node2Step4Narrowing_checked (by decide)
theorem root6Node2Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node2Domains4 (.output 0) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
