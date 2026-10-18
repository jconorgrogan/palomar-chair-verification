module

public import SpectreFinite.RadiusFiveRoot5Part2
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable16
public import SpectreFinite.RadiusFiveTable21

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node3Domains0 : Domains 91 State := restrict root5Node2Domains3 0 (3,4)
def root5Node3Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0),(7,4)]
  | 4 => some [(1,3),(6,3),(7,3)]
  | 5 => some [(2,2),(4,2)]
  | 6 => some [(2,1),(2,3),(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(4,1),(5,1),(8,1)]
  | 10 => some [(0,1),(0,2),(6,5)]
  | 11 => some [(0,4),(1,1),(6,2)]
  | 12 => some [(0,1),(1,4),(7,4)]
  | 13 => some [(0,0),(1,3),(6,4)]
  | 14 => some [(1,2),(3,2),(5,2)]
  | 15 => some [(4,0),(8,0)]
  | 16 => some [(7,3),(8,3)]
  | 17 => some [(5,2),(5,5)]
  | 18 => some [(1,0),(3,0),(5,0)]
  | 19 => some [(2,1),(2,5),(4,5)]
  | 20 => some [(0,2),(1,0),(6,0)]
  | 21 => some [(1,5),(6,5),(7,5)]
  | 22 => some [(0,3),(0,4),(6,1)]
  | 23 => some [(5,1),(5,4)]
  | 24 => some [(0,1),(1,4)]
  | 25 => some [(0,5),(6,2)]
  | 26 => some [(4,4),(8,4)]
  | 27 => some [(0,0)]
  | 28 => some [(3,2),(7,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5),(7,3)]
  | 31 => some [(4,2),(7,0)]
  | 32 => some [(4,3),(5,3),(8,3)]
  | 33 => some [(7,5),(8,5)]
  | 34 => some [(1,0),(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0),(6,4)]
  | 41 => some [(1,2),(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(0,3),(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(5,3),(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,0)]
  | 75 => some [(7,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(3,1)]
  | 82 => some [(0,1)]
  | 83 => some [(6,2)]
  | 84 => some [(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0)]
  | _ => some [(7,1)]
theorem root5Node3Domains0_fast_eq : root5Node3Domains0 = expandDomains root5Node3Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node3Domains0 v = expandDomains root5Node3Domains0Fast v from by decide) v
def root5Node3Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(3,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(2,2)]
  | 6 => [(2,3)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(4,1)]
  | 10 => [(0,2)]
  | 11 => [(1,1)]
  | 12 => [(0,1)]
  | 13 => [(6,4)]
  | 14 => [(1,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(1,0)]
  | 21 => [(7,5)]
  | 22 => [(0,3)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(0,0)]
  | 28 => [(7,2)]
  | 29 => [(4,0)]
  | 30 => [(4,5),(7,3)]
  | 31 => [(4,2)]
  | 32 => [(5,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(0,0),(6,4)]
  | 41 => [(1,2),(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(7,0)]
  | 48 => [(8,3)]
  | 49 => [(8,5)]
  | 50 => [(1,0)]
  | 51 => [(0,3),(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(5,3),(8,3)]
  | 62 => [(5,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5)]
  | 71 => [(4,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(2,0)]
  | 75 => [(7,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(3,1)]
  | 82 => [(0,1)]
  | 83 => [(6,2)]
  | 84 => [(8,4)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(1,0)]
  | _ => [(7,1)]
def root5Node3Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,2)]
  | 6 => some [(2,3)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(0,1)]
  | 13 => some [(6,4)]
  | 14 => some [(1,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0)]
  | 21 => some [(7,5)]
  | 22 => some [(0,3)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(0,0)]
  | 28 => some [(7,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5),(7,3)]
  | 31 => some [(4,2)]
  | 32 => some [(5,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0),(6,4)]
  | 41 => some [(1,2),(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(0,3),(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(5,3),(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,0)]
  | 75 => some [(7,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(3,1)]
  | 82 => some [(0,1)]
  | 83 => some [(6,2)]
  | 84 => some [(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0)]
  | _ => some [(7,1)]
theorem root5Node3Domains1_fast_eq : root5Node3Domains1 = expandDomains root5Node3Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node3Domains1 v = expandDomains root5Node3Domains1Fast v from by decide) v
theorem root5Node3Step1Chunk0_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk0_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk0_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk0_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk0_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk0_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk1_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk1_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk1_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk1_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk1_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk1_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk2_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk2_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk2_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk2_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk2_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk2_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk3_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk3_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk3_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk3_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk3_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk3_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk4_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk4_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk4_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk4_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk4_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk4_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk5_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk5_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk5_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk5_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk5_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk5_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk6_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk6_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk6_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk6_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk6_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk6_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk7_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk7_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk7_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk7_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk7_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk7_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk8_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk8_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk8_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk8_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk8_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk8_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Narrowing_checked :
    checkNarrowing table16 root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_flatten table16Scope [table16Rows0_0,table16Rows0_1,table16Rows0_2,table16Rows0_3,table16Rows0_4,table16Rows0_5,table16Rows1_0,table16Rows1_1,table16Rows1_2,table16Rows1_3,table16Rows1_4,table16Rows1_5,table16Rows2_0,table16Rows2_1,table16Rows2_2,table16Rows2_3,table16Rows2_4,table16Rows2_5,table16Rows3_0,table16Rows3_1,table16Rows3_2,table16Rows3_3,table16Rows3_4,table16Rows3_5,table16Rows4_0,table16Rows4_1,table16Rows4_2,table16Rows4_3,table16Rows4_4,table16Rows4_5,table16Rows5_0,table16Rows5_1,table16Rows5_2,table16Rows5_3,table16Rows5_4,table16Rows5_5,table16Rows6_0,table16Rows6_1,table16Rows6_2,table16Rows6_3,table16Rows6_4,table16Rows6_5,table16Rows7_0,table16Rows7_1,table16Rows7_2,table16Rows7_3,table16Rows7_4,table16Rows7_5,table16Rows8_0,table16Rows8_1,table16Rows8_2,table16Rows8_3,table16Rows8_4,table16Rows8_5]
    root5Node3Domains0 root5Node3Domains1 (by
      simp only [List.all_cons, List.all_nil, root5Node3Step1Chunk0_0_checked, root5Node3Step1Chunk0_1_checked, root5Node3Step1Chunk0_2_checked, root5Node3Step1Chunk0_3_checked, root5Node3Step1Chunk0_4_checked, root5Node3Step1Chunk0_5_checked, root5Node3Step1Chunk1_0_checked, root5Node3Step1Chunk1_1_checked, root5Node3Step1Chunk1_2_checked, root5Node3Step1Chunk1_3_checked, root5Node3Step1Chunk1_4_checked, root5Node3Step1Chunk1_5_checked, root5Node3Step1Chunk2_0_checked, root5Node3Step1Chunk2_1_checked, root5Node3Step1Chunk2_2_checked, root5Node3Step1Chunk2_3_checked, root5Node3Step1Chunk2_4_checked, root5Node3Step1Chunk2_5_checked, root5Node3Step1Chunk3_0_checked, root5Node3Step1Chunk3_1_checked, root5Node3Step1Chunk3_2_checked, root5Node3Step1Chunk3_3_checked, root5Node3Step1Chunk3_4_checked, root5Node3Step1Chunk3_5_checked, root5Node3Step1Chunk4_0_checked, root5Node3Step1Chunk4_1_checked, root5Node3Step1Chunk4_2_checked, root5Node3Step1Chunk4_3_checked, root5Node3Step1Chunk4_4_checked, root5Node3Step1Chunk4_5_checked, root5Node3Step1Chunk5_0_checked, root5Node3Step1Chunk5_1_checked, root5Node3Step1Chunk5_2_checked, root5Node3Step1Chunk5_3_checked, root5Node3Step1Chunk5_4_checked, root5Node3Step1Chunk5_5_checked, root5Node3Step1Chunk6_0_checked, root5Node3Step1Chunk6_1_checked, root5Node3Step1Chunk6_2_checked, root5Node3Step1Chunk6_3_checked, root5Node3Step1Chunk6_4_checked, root5Node3Step1Chunk6_5_checked, root5Node3Step1Chunk7_0_checked, root5Node3Step1Chunk7_1_checked, root5Node3Step1Chunk7_2_checked, root5Node3Step1Chunk7_3_checked, root5Node3Step1Chunk7_4_checked, root5Node3Step1Chunk7_5_checked, root5Node3Step1Chunk8_0_checked, root5Node3Step1Chunk8_1_checked, root5Node3Step1Chunk8_2_checked, root5Node3Step1Chunk8_3_checked, root5Node3Step1Chunk8_4_checked, root5Node3Step1Chunk8_5_checked, Bool.true_and])
theorem root5Node3Step1_checked :
    checkReplacement table16 root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq
    root5Node3Step1Narrowing_checked (by decide)
def root5Node3Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(3,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(2,2)]
  | 6 => [(2,3)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(4,1)]
  | 10 => [(0,2)]
  | 11 => [(1,1)]
  | 12 => [(0,1)]
  | 13 => [(6,4)]
  | 14 => [(1,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(1,0)]
  | 21 => [(7,5)]
  | 22 => [(0,3)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(0,0)]
  | 28 => [(7,2)]
  | 29 => [(4,0)]
  | 30 => [(7,3)]
  | 31 => [(4,2)]
  | 32 => [(5,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,4)]
  | 41 => [(1,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(7,0)]
  | 48 => [(8,3)]
  | 49 => [(8,5)]
  | 50 => [(1,0)]
  | 51 => [(0,3)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(5,3)]
  | 62 => [(5,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5)]
  | 71 => [(4,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(2,0)]
  | 75 => [(7,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(3,1)]
  | 82 => [(0,1)]
  | 83 => [(6,2)]
  | 84 => [(8,4)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(1,0)]
  | _ => [(7,1)]
def root5Node3Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,2)]
  | 6 => some [(2,3)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(0,1)]
  | 13 => some [(6,4)]
  | 14 => some [(1,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0)]
  | 21 => some [(7,5)]
  | 22 => some [(0,3)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(0,0)]
  | 28 => some [(7,2)]
  | 29 => some [(4,0)]
  | 30 => some [(7,3)]
  | 31 => some [(4,2)]
  | 32 => some [(5,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,4)]
  | 41 => some [(1,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(0,3)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(5,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,0)]
  | 75 => some [(7,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(3,1)]
  | 82 => some [(0,1)]
  | 83 => some [(6,2)]
  | 84 => some [(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0)]
  | _ => some [(7,1)]
theorem root5Node3Domains2_fast_eq : root5Node3Domains2 = expandDomains root5Node3Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node3Domains2 v = expandDomains root5Node3Domains2Fast v from by decide) v
theorem root5Node3Step2Chunk0_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_0⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk0_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_1⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk0_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_2⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk0_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_3⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk0_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_4⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk0_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_5⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk1_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_0⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk1_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_1⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk1_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_2⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk1_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_3⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk1_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_4⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk1_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_5⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk2_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_0⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk2_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_1⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk2_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_2⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk2_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_3⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk2_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_4⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk2_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_5⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk3_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_0⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk3_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_1⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk3_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_2⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk3_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_3⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk3_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_4⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk3_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_5⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk4_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_0⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk4_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_1⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk4_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_2⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk4_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_3⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk4_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_4⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk4_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_5⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk5_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_0⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk5_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_1⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk5_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_2⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk5_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_3⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk5_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_4⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk5_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_5⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk6_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_0⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk6_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_1⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk6_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_2⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk6_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_3⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk6_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_4⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk6_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_5⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk7_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_0⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk7_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_1⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk7_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_2⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk7_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_3⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk7_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_4⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk7_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_5⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk8_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_0⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk8_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_1⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk8_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_2⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk8_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_3⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk8_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_4⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Chunk8_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_5⟩
      root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq (by decide)
theorem root5Node3Step2Narrowing_checked :
    checkNarrowing table21 root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkNarrowing_flatten table21Scope [table21Rows0_0,table21Rows0_1,table21Rows0_2,table21Rows0_3,table21Rows0_4,table21Rows0_5,table21Rows1_0,table21Rows1_1,table21Rows1_2,table21Rows1_3,table21Rows1_4,table21Rows1_5,table21Rows2_0,table21Rows2_1,table21Rows2_2,table21Rows2_3,table21Rows2_4,table21Rows2_5,table21Rows3_0,table21Rows3_1,table21Rows3_2,table21Rows3_3,table21Rows3_4,table21Rows3_5,table21Rows4_0,table21Rows4_1,table21Rows4_2,table21Rows4_3,table21Rows4_4,table21Rows4_5,table21Rows5_0,table21Rows5_1,table21Rows5_2,table21Rows5_3,table21Rows5_4,table21Rows5_5,table21Rows6_0,table21Rows6_1,table21Rows6_2,table21Rows6_3,table21Rows6_4,table21Rows6_5,table21Rows7_0,table21Rows7_1,table21Rows7_2,table21Rows7_3,table21Rows7_4,table21Rows7_5,table21Rows8_0,table21Rows8_1,table21Rows8_2,table21Rows8_3,table21Rows8_4,table21Rows8_5]
    root5Node3Domains1 root5Node3Domains2 (by
      simp only [List.all_cons, List.all_nil, root5Node3Step2Chunk0_0_checked, root5Node3Step2Chunk0_1_checked, root5Node3Step2Chunk0_2_checked, root5Node3Step2Chunk0_3_checked, root5Node3Step2Chunk0_4_checked, root5Node3Step2Chunk0_5_checked, root5Node3Step2Chunk1_0_checked, root5Node3Step2Chunk1_1_checked, root5Node3Step2Chunk1_2_checked, root5Node3Step2Chunk1_3_checked, root5Node3Step2Chunk1_4_checked, root5Node3Step2Chunk1_5_checked, root5Node3Step2Chunk2_0_checked, root5Node3Step2Chunk2_1_checked, root5Node3Step2Chunk2_2_checked, root5Node3Step2Chunk2_3_checked, root5Node3Step2Chunk2_4_checked, root5Node3Step2Chunk2_5_checked, root5Node3Step2Chunk3_0_checked, root5Node3Step2Chunk3_1_checked, root5Node3Step2Chunk3_2_checked, root5Node3Step2Chunk3_3_checked, root5Node3Step2Chunk3_4_checked, root5Node3Step2Chunk3_5_checked, root5Node3Step2Chunk4_0_checked, root5Node3Step2Chunk4_1_checked, root5Node3Step2Chunk4_2_checked, root5Node3Step2Chunk4_3_checked, root5Node3Step2Chunk4_4_checked, root5Node3Step2Chunk4_5_checked, root5Node3Step2Chunk5_0_checked, root5Node3Step2Chunk5_1_checked, root5Node3Step2Chunk5_2_checked, root5Node3Step2Chunk5_3_checked, root5Node3Step2Chunk5_4_checked, root5Node3Step2Chunk5_5_checked, root5Node3Step2Chunk6_0_checked, root5Node3Step2Chunk6_1_checked, root5Node3Step2Chunk6_2_checked, root5Node3Step2Chunk6_3_checked, root5Node3Step2Chunk6_4_checked, root5Node3Step2Chunk6_5_checked, root5Node3Step2Chunk7_0_checked, root5Node3Step2Chunk7_1_checked, root5Node3Step2Chunk7_2_checked, root5Node3Step2Chunk7_3_checked, root5Node3Step2Chunk7_4_checked, root5Node3Step2Chunk7_5_checked, root5Node3Step2Chunk8_0_checked, root5Node3Step2Chunk8_1_checked, root5Node3Step2Chunk8_2_checked, root5Node3Step2Chunk8_3_checked, root5Node3Step2Chunk8_4_checked, root5Node3Step2Chunk8_5_checked, Bool.true_and])
theorem root5Node3Step2_checked :
    checkReplacement table21 root5Node3Domains1 root5Node3Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root5Node3Domains1 root5Node3Domains2
    root5Node3Domains1Fast root5Node3Domains2Fast
    root5Node3Domains1_fast_eq root5Node3Domains2_fast_eq
    root5Node3Step2Narrowing_checked (by decide)
theorem root5Node3Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node3Domains2 (.output 0) = true := by decide
def root5Node4Domains0 : Domains 91 State := restrict root5Node2Domains3 0 (7,4)
def root5Node4Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0),(7,4)]
  | 4 => some [(1,3),(6,3),(7,3)]
  | 5 => some [(2,2),(4,2)]
  | 6 => some [(2,1),(2,3),(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(4,1),(5,1),(8,1)]
  | 10 => some [(0,1),(0,2),(6,5)]
  | 11 => some [(0,4),(1,1),(6,2)]
  | 12 => some [(0,1),(1,4),(7,4)]
  | 13 => some [(0,0),(1,3),(6,4)]
  | 14 => some [(1,2),(3,2),(5,2)]
  | 15 => some [(4,0),(8,0)]
  | 16 => some [(7,3),(8,3)]
  | 17 => some [(5,2),(5,5)]
  | 18 => some [(1,0),(3,0),(5,0)]
  | 19 => some [(2,1),(2,5),(4,5)]
  | 20 => some [(0,2),(1,0),(6,0)]
  | 21 => some [(1,5),(6,5),(7,5)]
  | 22 => some [(0,3),(0,4),(6,1)]
  | 23 => some [(5,1),(5,4)]
  | 24 => some [(0,1),(1,4)]
  | 25 => some [(0,5),(6,2)]
  | 26 => some [(4,4),(8,4)]
  | 27 => some [(0,0)]
  | 28 => some [(3,2),(7,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5),(7,3)]
  | 31 => some [(4,2),(7,0)]
  | 32 => some [(4,3),(5,3),(8,3)]
  | 33 => some [(7,5),(8,5)]
  | 34 => some [(1,0),(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0),(6,4)]
  | 41 => some [(1,2),(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(0,3),(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(5,3),(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,0)]
  | 75 => some [(7,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(3,1)]
  | 82 => some [(0,1)]
  | 83 => some [(6,2)]
  | 84 => some [(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0)]
  | _ => some [(7,1)]
theorem root5Node4Domains0_fast_eq : root5Node4Domains0 = expandDomains root5Node4Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node4Domains0 v = expandDomains root5Node4Domains0Fast v from by decide) v
def root5Node4Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,0),(7,4)]
  | 4 => [(1,3),(6,3),(7,3)]
  | 5 => [(2,2),(4,2)]
  | 6 => [(2,1),(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(4,1),(5,1),(8,1)]
  | 10 => [(0,1),(0,2),(6,5)]
  | 11 => [(0,4),(1,1),(6,2)]
  | 12 => [(0,1),(1,4),(7,4)]
  | 13 => [(0,0),(1,3)]
  | 14 => [(3,2),(5,2)]
  | 15 => [(4,0),(8,0)]
  | 16 => [(7,3),(8,3)]
  | 17 => [(5,2),(5,5)]
  | 18 => [(1,0),(3,0),(5,0)]
  | 19 => [(2,1),(2,5),(4,5)]
  | 20 => [(0,2),(1,0),(6,0)]
  | 21 => [(1,5),(6,5)]
  | 22 => [(0,4),(6,1)]
  | 23 => [(5,1),(5,4)]
  | 24 => [(0,1),(1,4)]
  | 25 => [(0,5),(6,2)]
  | 26 => [(4,4),(8,4)]
  | 27 => [(0,0)]
  | 28 => [(3,2),(7,2)]
  | 29 => [(4,0)]
  | 30 => [(4,5)]
  | 31 => [(7,0)]
  | 32 => [(4,3),(8,3)]
  | 33 => [(7,5),(8,5)]
  | 34 => [(1,0),(6,0)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(7,0)]
  | 48 => [(8,3)]
  | 49 => [(8,5)]
  | 50 => [(1,0)]
  | 51 => [(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
  | 62 => [(5,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5)]
  | 71 => [(4,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(2,0)]
  | 75 => [(7,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(3,1)]
  | 82 => [(0,1)]
  | 83 => [(6,2)]
  | 84 => [(8,4)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(1,0)]
  | _ => [(7,1)]
def root5Node4Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0),(7,4)]
  | 4 => some [(1,3),(6,3),(7,3)]
  | 5 => some [(2,2),(4,2)]
  | 6 => some [(2,1),(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(4,1),(5,1),(8,1)]
  | 10 => some [(0,1),(0,2),(6,5)]
  | 11 => some [(0,4),(1,1),(6,2)]
  | 12 => some [(0,1),(1,4),(7,4)]
  | 13 => some [(0,0),(1,3)]
  | 14 => some [(3,2),(5,2)]
  | 15 => some [(4,0),(8,0)]
  | 16 => some [(7,3),(8,3)]
  | 17 => some [(5,2),(5,5)]
  | 18 => some [(1,0),(3,0),(5,0)]
  | 19 => some [(2,1),(2,5),(4,5)]
  | 20 => some [(0,2),(1,0),(6,0)]
  | 21 => some [(1,5),(6,5)]
  | 22 => some [(0,4),(6,1)]
  | 23 => some [(5,1),(5,4)]
  | 24 => some [(0,1),(1,4)]
  | 25 => some [(0,5),(6,2)]
  | 26 => some [(4,4),(8,4)]
  | 27 => some [(0,0)]
  | 28 => some [(3,2),(7,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(4,3),(8,3)]
  | 33 => some [(7,5),(8,5)]
  | 34 => some [(1,0),(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,0)]
  | 75 => some [(7,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(3,1)]
  | 82 => some [(0,1)]
  | 83 => some [(6,2)]
  | 84 => some [(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0)]
  | _ => some [(7,1)]
theorem root5Node4Domains1_fast_eq : root5Node4Domains1 = expandDomains root5Node4Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node4Domains1 v = expandDomains root5Node4Domains1Fast v from by decide) v
theorem root5Node4Step1Chunk0_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_0⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk0_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_1⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk0_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_2⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk0_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_3⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk0_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_4⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk0_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_5⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk1_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_0⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk1_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_1⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk1_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_2⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk1_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_3⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk1_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_4⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk1_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_5⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk2_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_0⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk2_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_1⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk2_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_2⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk2_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_3⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk2_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_4⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk2_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_5⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk3_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_0⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk3_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_1⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk3_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_2⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk3_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_3⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk3_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_4⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk3_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_5⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk4_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_0⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk4_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_1⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk4_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_2⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk4_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_3⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk4_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_4⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk4_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_5⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk5_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_0⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk5_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_1⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk5_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_2⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk5_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_3⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk5_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_4⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk5_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_5⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk6_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_0⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk6_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_1⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk6_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_2⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk6_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_3⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk6_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_4⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk6_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_5⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk7_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_0⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk7_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_1⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk7_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_2⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk7_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_3⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk7_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_4⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk7_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_5⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk8_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_0⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk8_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_1⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk8_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_2⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk8_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_3⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk8_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_4⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk8_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_5⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Narrowing_checked :
    checkNarrowing table21 root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_flatten table21Scope [table21Rows0_0,table21Rows0_1,table21Rows0_2,table21Rows0_3,table21Rows0_4,table21Rows0_5,table21Rows1_0,table21Rows1_1,table21Rows1_2,table21Rows1_3,table21Rows1_4,table21Rows1_5,table21Rows2_0,table21Rows2_1,table21Rows2_2,table21Rows2_3,table21Rows2_4,table21Rows2_5,table21Rows3_0,table21Rows3_1,table21Rows3_2,table21Rows3_3,table21Rows3_4,table21Rows3_5,table21Rows4_0,table21Rows4_1,table21Rows4_2,table21Rows4_3,table21Rows4_4,table21Rows4_5,table21Rows5_0,table21Rows5_1,table21Rows5_2,table21Rows5_3,table21Rows5_4,table21Rows5_5,table21Rows6_0,table21Rows6_1,table21Rows6_2,table21Rows6_3,table21Rows6_4,table21Rows6_5,table21Rows7_0,table21Rows7_1,table21Rows7_2,table21Rows7_3,table21Rows7_4,table21Rows7_5,table21Rows8_0,table21Rows8_1,table21Rows8_2,table21Rows8_3,table21Rows8_4,table21Rows8_5]
    root5Node4Domains0 root5Node4Domains1 (by
      simp only [List.all_cons, List.all_nil, root5Node4Step1Chunk0_0_checked, root5Node4Step1Chunk0_1_checked, root5Node4Step1Chunk0_2_checked, root5Node4Step1Chunk0_3_checked, root5Node4Step1Chunk0_4_checked, root5Node4Step1Chunk0_5_checked, root5Node4Step1Chunk1_0_checked, root5Node4Step1Chunk1_1_checked, root5Node4Step1Chunk1_2_checked, root5Node4Step1Chunk1_3_checked, root5Node4Step1Chunk1_4_checked, root5Node4Step1Chunk1_5_checked, root5Node4Step1Chunk2_0_checked, root5Node4Step1Chunk2_1_checked, root5Node4Step1Chunk2_2_checked, root5Node4Step1Chunk2_3_checked, root5Node4Step1Chunk2_4_checked, root5Node4Step1Chunk2_5_checked, root5Node4Step1Chunk3_0_checked, root5Node4Step1Chunk3_1_checked, root5Node4Step1Chunk3_2_checked, root5Node4Step1Chunk3_3_checked, root5Node4Step1Chunk3_4_checked, root5Node4Step1Chunk3_5_checked, root5Node4Step1Chunk4_0_checked, root5Node4Step1Chunk4_1_checked, root5Node4Step1Chunk4_2_checked, root5Node4Step1Chunk4_3_checked, root5Node4Step1Chunk4_4_checked, root5Node4Step1Chunk4_5_checked, root5Node4Step1Chunk5_0_checked, root5Node4Step1Chunk5_1_checked, root5Node4Step1Chunk5_2_checked, root5Node4Step1Chunk5_3_checked, root5Node4Step1Chunk5_4_checked, root5Node4Step1Chunk5_5_checked, root5Node4Step1Chunk6_0_checked, root5Node4Step1Chunk6_1_checked, root5Node4Step1Chunk6_2_checked, root5Node4Step1Chunk6_3_checked, root5Node4Step1Chunk6_4_checked, root5Node4Step1Chunk6_5_checked, root5Node4Step1Chunk7_0_checked, root5Node4Step1Chunk7_1_checked, root5Node4Step1Chunk7_2_checked, root5Node4Step1Chunk7_3_checked, root5Node4Step1Chunk7_4_checked, root5Node4Step1Chunk7_5_checked, root5Node4Step1Chunk8_0_checked, root5Node4Step1Chunk8_1_checked, root5Node4Step1Chunk8_2_checked, root5Node4Step1Chunk8_3_checked, root5Node4Step1Chunk8_4_checked, root5Node4Step1Chunk8_5_checked, Bool.true_and])
theorem root5Node4Step1_checked :
    checkReplacement table21 root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq
    root5Node4Step1Narrowing_checked (by decide)
def root5Node5Domains0 : Domains 91 State := restrict root5Node4Domains1 3 (4,0)
def root5Node5Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(1,3),(6,3),(7,3)]
  | 5 => some [(2,2),(4,2)]
  | 6 => some [(2,1),(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(4,1),(5,1),(8,1)]
  | 10 => some [(0,1),(0,2),(6,5)]
  | 11 => some [(0,4),(1,1),(6,2)]
  | 12 => some [(0,1),(1,4),(7,4)]
  | 13 => some [(0,0),(1,3)]
  | 14 => some [(3,2),(5,2)]
  | 15 => some [(4,0),(8,0)]
  | 16 => some [(7,3),(8,3)]
  | 17 => some [(5,2),(5,5)]
  | 18 => some [(1,0),(3,0),(5,0)]
  | 19 => some [(2,1),(2,5),(4,5)]
  | 20 => some [(0,2),(1,0),(6,0)]
  | 21 => some [(1,5),(6,5)]
  | 22 => some [(0,4),(6,1)]
  | 23 => some [(5,1),(5,4)]
  | 24 => some [(0,1),(1,4)]
  | 25 => some [(0,5),(6,2)]
  | 26 => some [(4,4),(8,4)]
  | 27 => some [(0,0)]
  | 28 => some [(3,2),(7,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(4,3),(8,3)]
  | 33 => some [(7,5),(8,5)]
  | 34 => some [(1,0),(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,0)]
  | 75 => some [(7,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(3,1)]
  | 82 => some [(0,1)]
  | 83 => some [(6,2)]
  | 84 => some [(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0)]
  | _ => some [(7,1)]
theorem root5Node5Domains0_fast_eq : root5Node5Domains0 = expandDomains root5Node5Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node5Domains0 v = expandDomains root5Node5Domains0Fast v from by decide) v
def root5Node5Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(4,2)]
  | 6 => [(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(5,1)]
  | 10 => [(0,1)]
  | 11 => [(6,2)]
  | 12 => [(7,4)]
  | 13 => [(1,3)]
  | 14 => [(5,2)]
  | 15 => [(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(1,0)]
  | 19 => [(2,1)]
  | 20 => [(0,2)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(0,0)]
  | 28 => [(3,2)]
  | 29 => [(4,0)]
  | 30 => [(4,5)]
  | 31 => [(7,0)]
  | 32 => [(4,3)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(7,0)]
  | 48 => [(8,3)]
  | 49 => [(8,5)]
  | 50 => [(1,0)]
  | 51 => [(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
  | 62 => [(5,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5)]
  | 71 => [(4,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(2,0)]
  | 75 => [(7,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(3,1)]
  | 82 => [(0,1)]
  | 83 => [(6,2)]
  | 84 => [(8,4)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(1,0)]
  | _ => [(7,1)]
def root5Node5Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(4,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(7,4)]
  | 13 => some [(1,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(1,0)]
  | 19 => some [(2,1)]
  | 20 => some [(0,2)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(0,0)]
  | 28 => some [(3,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(4,3)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,0)]
  | 75 => some [(7,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(3,1)]
  | 82 => some [(0,1)]
  | 83 => some [(6,2)]
  | 84 => some [(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0)]
  | _ => some [(7,1)]
theorem root5Node5Domains1_fast_eq : root5Node5Domains1 = expandDomains root5Node5Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node5Domains1 v = expandDomains root5Node5Domains1Fast v from by decide) v
theorem root5Node5Step1Chunk0_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_0⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk0_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_1⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk0_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_2⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk0_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_3⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk0_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_4⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk0_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_5⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk1_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_0⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk1_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_1⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk1_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_2⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk1_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_3⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk1_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_4⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk1_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_5⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk2_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_0⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk2_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_1⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk2_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_2⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk2_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_3⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk2_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_4⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk2_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_5⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk3_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_0⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk3_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_1⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk3_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_2⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk3_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_3⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk3_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_4⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk3_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_5⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk4_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_0⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk4_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_1⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk4_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_2⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk4_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_3⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk4_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_4⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk4_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_5⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk5_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_0⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk5_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_1⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk5_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_2⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk5_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_3⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk5_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_4⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk5_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_5⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk6_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_0⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk6_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_1⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk6_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_2⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk6_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_3⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk6_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_4⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk6_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_5⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk7_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_0⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk7_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_1⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk7_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_2⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk7_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_3⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk7_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_4⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk7_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_5⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk8_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_0⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk8_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_1⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk8_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_2⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk8_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_3⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk8_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_4⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk8_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_5⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Narrowing_checked :
    checkNarrowing table16 root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_flatten table16Scope [table16Rows0_0,table16Rows0_1,table16Rows0_2,table16Rows0_3,table16Rows0_4,table16Rows0_5,table16Rows1_0,table16Rows1_1,table16Rows1_2,table16Rows1_3,table16Rows1_4,table16Rows1_5,table16Rows2_0,table16Rows2_1,table16Rows2_2,table16Rows2_3,table16Rows2_4,table16Rows2_5,table16Rows3_0,table16Rows3_1,table16Rows3_2,table16Rows3_3,table16Rows3_4,table16Rows3_5,table16Rows4_0,table16Rows4_1,table16Rows4_2,table16Rows4_3,table16Rows4_4,table16Rows4_5,table16Rows5_0,table16Rows5_1,table16Rows5_2,table16Rows5_3,table16Rows5_4,table16Rows5_5,table16Rows6_0,table16Rows6_1,table16Rows6_2,table16Rows6_3,table16Rows6_4,table16Rows6_5,table16Rows7_0,table16Rows7_1,table16Rows7_2,table16Rows7_3,table16Rows7_4,table16Rows7_5,table16Rows8_0,table16Rows8_1,table16Rows8_2,table16Rows8_3,table16Rows8_4,table16Rows8_5]
    root5Node5Domains0 root5Node5Domains1 (by
      simp only [List.all_cons, List.all_nil, root5Node5Step1Chunk0_0_checked, root5Node5Step1Chunk0_1_checked, root5Node5Step1Chunk0_2_checked, root5Node5Step1Chunk0_3_checked, root5Node5Step1Chunk0_4_checked, root5Node5Step1Chunk0_5_checked, root5Node5Step1Chunk1_0_checked, root5Node5Step1Chunk1_1_checked, root5Node5Step1Chunk1_2_checked, root5Node5Step1Chunk1_3_checked, root5Node5Step1Chunk1_4_checked, root5Node5Step1Chunk1_5_checked, root5Node5Step1Chunk2_0_checked, root5Node5Step1Chunk2_1_checked, root5Node5Step1Chunk2_2_checked, root5Node5Step1Chunk2_3_checked, root5Node5Step1Chunk2_4_checked, root5Node5Step1Chunk2_5_checked, root5Node5Step1Chunk3_0_checked, root5Node5Step1Chunk3_1_checked, root5Node5Step1Chunk3_2_checked, root5Node5Step1Chunk3_3_checked, root5Node5Step1Chunk3_4_checked, root5Node5Step1Chunk3_5_checked, root5Node5Step1Chunk4_0_checked, root5Node5Step1Chunk4_1_checked, root5Node5Step1Chunk4_2_checked, root5Node5Step1Chunk4_3_checked, root5Node5Step1Chunk4_4_checked, root5Node5Step1Chunk4_5_checked, root5Node5Step1Chunk5_0_checked, root5Node5Step1Chunk5_1_checked, root5Node5Step1Chunk5_2_checked, root5Node5Step1Chunk5_3_checked, root5Node5Step1Chunk5_4_checked, root5Node5Step1Chunk5_5_checked, root5Node5Step1Chunk6_0_checked, root5Node5Step1Chunk6_1_checked, root5Node5Step1Chunk6_2_checked, root5Node5Step1Chunk6_3_checked, root5Node5Step1Chunk6_4_checked, root5Node5Step1Chunk6_5_checked, root5Node5Step1Chunk7_0_checked, root5Node5Step1Chunk7_1_checked, root5Node5Step1Chunk7_2_checked, root5Node5Step1Chunk7_3_checked, root5Node5Step1Chunk7_4_checked, root5Node5Step1Chunk7_5_checked, root5Node5Step1Chunk8_0_checked, root5Node5Step1Chunk8_1_checked, root5Node5Step1Chunk8_2_checked, root5Node5Step1Chunk8_3_checked, root5Node5Step1Chunk8_4_checked, root5Node5Step1Chunk8_5_checked, Bool.true_and])
theorem root5Node5Step1_checked :
    checkReplacement table16 root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq
    root5Node5Step1Narrowing_checked (by decide)
theorem root5Node5Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node5Domains1 (.output 1) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
