module

public import SpectreFinite.RadiusFiveRoot2Part2
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable36
public import SpectreFinite.RadiusFiveTable41
public import SpectreFinite.RadiusFiveTable52
public import SpectreFinite.RadiusFiveTable55

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root2Node3Domains0 : Domains 91 State := restrict root2Node1Domains1 6 (8,3)
def root2Node3Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,1)]
  | 1 => some [(0,1)]
  | 2 => some [(6,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(7,2)]
  | 6 => some [(8,3)]
  | 7 => some [(8,5)]
  | 8 => some [(1,0)]
  | 9 => some [(7,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1),(8,1)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(5,3),(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(4,1),(5,1),(8,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(1,4)]
  | 44 => some [(0,5)]
  | 45 => some [(2,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3),(8,3)]
  | 50 => some [(5,2),(5,5)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(6,0)]
  | 55 => some [(3,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(1,4),(6,4)]
  | 60 => some [(0,5),(1,2)]
  | 61 => some [(4,0),(8,0)]
  | 62 => some [(7,3)]
  | 63 => some [(8,2)]
  | 64 => some [(5,0)]
  | 65 => some [(4,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3),(6,0)]
  | 70 => some [(0,1),(6,4)]
  | 71 => some [(1,2),(6,2)]
  | 72 => some [(8,4)]
  | 73 => some [(0,0)]
  | 74 => some [(7,2)]
  | 75 => some [(4,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2),(8,2)]
  | 78 => some [(0,3),(1,0)]
  | 79 => some [(7,1),(8,1)]
  | 80 => some [(1,5)]
  | 81 => some [(6,1)]
  | 82 => some [(5,1)]
  | 83 => some [(0,1)]
  | 84 => some [(6,2)]
  | 85 => some [(5,0),(5,3)]
  | 86 => some [(4,5),(5,5),(8,5)]
  | 87 => some [(7,0)]
  | 88 => some [(8,3)]
  | 89 => some [(5,5),(8,5)]
  | _ => some [(1,0)]
theorem root2Node3Domains0_fast_eq : root2Node3Domains0 = expandDomains root2Node3Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root2Node3Domains0 v = expandDomains root2Node3Domains0Fast v from by decide) v
def root2Node3Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,1)]
  | 1 => [(0,1)]
  | 2 => [(6,2)]
  | 3 => [(8,4)]
  | 4 => [(0,0)]
  | 5 => [(7,2)]
  | 6 => [(8,3)]
  | 7 => [(8,5)]
  | 8 => [(1,0)]
  | 9 => [(7,1)]
  | 10 => [(1,5)]
  | 11 => [(6,1)]
  | 12 => [(5,1),(8,1)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(8,1)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => [(7,2)]
  | 30 => [(8,3)]
  | 31 => [(5,5)]
  | 32 => [(7,0)]
  | 33 => [(4,3)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => [(4,1),(5,1),(8,1)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(1,4)]
  | 44 => [(0,5)]
  | 45 => [(2,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(8,0)]
  | 49 => [(7,3),(8,3)]
  | 50 => [(5,2),(5,5)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(7,5)]
  | 54 => [(6,0)]
  | 55 => [(3,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(1,4),(6,4)]
  | 60 => [(0,5),(1,2)]
  | 61 => [(8,0)]
  | 62 => [(7,3)]
  | 63 => [(8,2)]
  | 64 => [(5,0)]
  | 65 => [(4,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(0,3),(6,0)]
  | 70 => [(6,4)]
  | 71 => [(1,2)]
  | 72 => [(8,4)]
  | 73 => [(0,0)]
  | 74 => [(7,2)]
  | 75 => [(4,0)]
  | 76 => [(7,3)]
  | 77 => [(4,2),(8,2)]
  | 78 => [(0,3)]
  | 79 => [(8,1)]
  | 80 => [(1,5)]
  | 81 => [(6,1)]
  | 82 => [(5,1)]
  | 83 => [(0,1)]
  | 84 => [(6,2)]
  | 85 => [(5,0),(5,3)]
  | 86 => [(4,5),(5,5),(8,5)]
  | 87 => [(7,0)]
  | 88 => [(8,3)]
  | 89 => [(5,5),(8,5)]
  | _ => [(1,0)]
def root2Node3Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,1)]
  | 1 => some [(0,1)]
  | 2 => some [(6,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(7,2)]
  | 6 => some [(8,3)]
  | 7 => some [(8,5)]
  | 8 => some [(1,0)]
  | 9 => some [(7,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1),(8,1)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(4,1),(5,1),(8,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(1,4)]
  | 44 => some [(0,5)]
  | 45 => some [(2,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3),(8,3)]
  | 50 => some [(5,2),(5,5)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(6,0)]
  | 55 => some [(3,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(1,4),(6,4)]
  | 60 => some [(0,5),(1,2)]
  | 61 => some [(8,0)]
  | 62 => some [(7,3)]
  | 63 => some [(8,2)]
  | 64 => some [(5,0)]
  | 65 => some [(4,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3),(6,0)]
  | 70 => some [(6,4)]
  | 71 => some [(1,2)]
  | 72 => some [(8,4)]
  | 73 => some [(0,0)]
  | 74 => some [(7,2)]
  | 75 => some [(4,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2),(8,2)]
  | 78 => some [(0,3)]
  | 79 => some [(8,1)]
  | 80 => some [(1,5)]
  | 81 => some [(6,1)]
  | 82 => some [(5,1)]
  | 83 => some [(0,1)]
  | 84 => some [(6,2)]
  | 85 => some [(5,0),(5,3)]
  | 86 => some [(4,5),(5,5),(8,5)]
  | 87 => some [(7,0)]
  | 88 => some [(8,3)]
  | 89 => some [(5,5),(8,5)]
  | _ => some [(1,0)]
theorem root2Node3Domains1_fast_eq : root2Node3Domains1 = expandDomains root2Node3Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root2Node3Domains1 v = expandDomains root2Node3Domains1Fast v from by decide) v
theorem root2Node3Step1Chunk0_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows0_0⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk0_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows0_1⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk0_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows0_2⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk0_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows0_3⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk0_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows0_4⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk0_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows0_5⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk1_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows1_0⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk1_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows1_1⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk1_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows1_2⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk1_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows1_3⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk1_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows1_4⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk1_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows1_5⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk2_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows2_0⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk2_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows2_1⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk2_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows2_2⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk2_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows2_3⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk2_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows2_4⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk2_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows2_5⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk3_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows3_0⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk3_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows3_1⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk3_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows3_2⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk3_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows3_3⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk3_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows3_4⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk3_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows3_5⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk4_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows4_0⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk4_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows4_1⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk4_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows4_2⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk4_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows4_3⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk4_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows4_4⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk4_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows4_5⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk5_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows5_0⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk5_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows5_1⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk5_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows5_2⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk5_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows5_3⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk5_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows5_4⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk5_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows5_5⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk6_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows6_0⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk6_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows6_1⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk6_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows6_2⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk6_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows6_3⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk6_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows6_4⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk6_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows6_5⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk7_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows7_0⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk7_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows7_1⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk7_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows7_2⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk7_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows7_3⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk7_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows7_4⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk7_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows7_5⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk8_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows8_0⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk8_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows8_1⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk8_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows8_2⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk8_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows8_3⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk8_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows8_4⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Chunk8_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows8_5⟩
      root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq (by decide)
theorem root2Node3Step1Narrowing_checked :
    checkNarrowing table41 root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkNarrowing_flatten table41Scope [table41Rows0_0,table41Rows0_1,table41Rows0_2,table41Rows0_3,table41Rows0_4,table41Rows0_5,table41Rows1_0,table41Rows1_1,table41Rows1_2,table41Rows1_3,table41Rows1_4,table41Rows1_5,table41Rows2_0,table41Rows2_1,table41Rows2_2,table41Rows2_3,table41Rows2_4,table41Rows2_5,table41Rows3_0,table41Rows3_1,table41Rows3_2,table41Rows3_3,table41Rows3_4,table41Rows3_5,table41Rows4_0,table41Rows4_1,table41Rows4_2,table41Rows4_3,table41Rows4_4,table41Rows4_5,table41Rows5_0,table41Rows5_1,table41Rows5_2,table41Rows5_3,table41Rows5_4,table41Rows5_5,table41Rows6_0,table41Rows6_1,table41Rows6_2,table41Rows6_3,table41Rows6_4,table41Rows6_5,table41Rows7_0,table41Rows7_1,table41Rows7_2,table41Rows7_3,table41Rows7_4,table41Rows7_5,table41Rows8_0,table41Rows8_1,table41Rows8_2,table41Rows8_3,table41Rows8_4,table41Rows8_5]
    root2Node3Domains0 root2Node3Domains1 (by
      simp only [List.all_cons, List.all_nil, root2Node3Step1Chunk0_0_checked, root2Node3Step1Chunk0_1_checked, root2Node3Step1Chunk0_2_checked, root2Node3Step1Chunk0_3_checked, root2Node3Step1Chunk0_4_checked, root2Node3Step1Chunk0_5_checked, root2Node3Step1Chunk1_0_checked, root2Node3Step1Chunk1_1_checked, root2Node3Step1Chunk1_2_checked, root2Node3Step1Chunk1_3_checked, root2Node3Step1Chunk1_4_checked, root2Node3Step1Chunk1_5_checked, root2Node3Step1Chunk2_0_checked, root2Node3Step1Chunk2_1_checked, root2Node3Step1Chunk2_2_checked, root2Node3Step1Chunk2_3_checked, root2Node3Step1Chunk2_4_checked, root2Node3Step1Chunk2_5_checked, root2Node3Step1Chunk3_0_checked, root2Node3Step1Chunk3_1_checked, root2Node3Step1Chunk3_2_checked, root2Node3Step1Chunk3_3_checked, root2Node3Step1Chunk3_4_checked, root2Node3Step1Chunk3_5_checked, root2Node3Step1Chunk4_0_checked, root2Node3Step1Chunk4_1_checked, root2Node3Step1Chunk4_2_checked, root2Node3Step1Chunk4_3_checked, root2Node3Step1Chunk4_4_checked, root2Node3Step1Chunk4_5_checked, root2Node3Step1Chunk5_0_checked, root2Node3Step1Chunk5_1_checked, root2Node3Step1Chunk5_2_checked, root2Node3Step1Chunk5_3_checked, root2Node3Step1Chunk5_4_checked, root2Node3Step1Chunk5_5_checked, root2Node3Step1Chunk6_0_checked, root2Node3Step1Chunk6_1_checked, root2Node3Step1Chunk6_2_checked, root2Node3Step1Chunk6_3_checked, root2Node3Step1Chunk6_4_checked, root2Node3Step1Chunk6_5_checked, root2Node3Step1Chunk7_0_checked, root2Node3Step1Chunk7_1_checked, root2Node3Step1Chunk7_2_checked, root2Node3Step1Chunk7_3_checked, root2Node3Step1Chunk7_4_checked, root2Node3Step1Chunk7_5_checked, root2Node3Step1Chunk8_0_checked, root2Node3Step1Chunk8_1_checked, root2Node3Step1Chunk8_2_checked, root2Node3Step1Chunk8_3_checked, root2Node3Step1Chunk8_4_checked, root2Node3Step1Chunk8_5_checked, Bool.true_and])
theorem root2Node3Step1_checked :
    checkReplacement table41 root2Node3Domains0 root2Node3Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root2Node3Domains0 root2Node3Domains1
    root2Node3Domains0Fast root2Node3Domains1Fast
    root2Node3Domains0_fast_eq root2Node3Domains1_fast_eq
    root2Node3Step1Narrowing_checked (by decide)
def root2Node3Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,1)]
  | 1 => [(0,1)]
  | 2 => [(6,2)]
  | 3 => [(8,4)]
  | 4 => [(0,0)]
  | 5 => [(7,2)]
  | 6 => [(8,3)]
  | 7 => [(8,5)]
  | 8 => [(1,0)]
  | 9 => [(7,1)]
  | 10 => [(1,5)]
  | 11 => [(6,1)]
  | 12 => [(5,1),(8,1)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(8,1)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => [(7,2)]
  | 30 => [(8,3)]
  | 31 => [(5,5)]
  | 32 => [(7,0)]
  | 33 => [(4,3)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => [(4,1),(5,1),(8,1)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(1,4)]
  | 44 => [(0,5)]
  | 45 => [(2,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(8,0)]
  | 49 => [(7,3),(8,3)]
  | 50 => [(5,2),(5,5)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(7,5)]
  | 54 => [(6,0)]
  | 55 => [(3,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(1,4),(6,4)]
  | 60 => [(0,5),(1,2)]
  | 61 => [(8,0)]
  | 62 => [(7,3)]
  | 63 => [(8,2)]
  | 64 => [(5,0)]
  | 65 => [(4,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(0,3),(6,0)]
  | 70 => [(6,4)]
  | 71 => [(1,2)]
  | 72 => [(8,4)]
  | 73 => [(0,0)]
  | 74 => [(7,2)]
  | 75 => [(4,0)]
  | 76 => [(7,3)]
  | 77 => [(4,2),(8,2)]
  | 78 => [(0,3)]
  | 79 => [(8,1)]
  | 80 => [(1,5)]
  | 81 => [(6,1)]
  | 82 => [(5,1)]
  | 83 => [(0,1)]
  | 84 => [(6,2)]
  | 85 => [(5,3)]
  | 86 => [(5,5),(8,5)]
  | 87 => [(7,0)]
  | 88 => [(8,3)]
  | 89 => [(5,5),(8,5)]
  | _ => [(1,0)]
def root2Node3Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,1)]
  | 1 => some [(0,1)]
  | 2 => some [(6,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(7,2)]
  | 6 => some [(8,3)]
  | 7 => some [(8,5)]
  | 8 => some [(1,0)]
  | 9 => some [(7,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1),(8,1)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(4,1),(5,1),(8,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(1,4)]
  | 44 => some [(0,5)]
  | 45 => some [(2,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3),(8,3)]
  | 50 => some [(5,2),(5,5)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(6,0)]
  | 55 => some [(3,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(1,4),(6,4)]
  | 60 => some [(0,5),(1,2)]
  | 61 => some [(8,0)]
  | 62 => some [(7,3)]
  | 63 => some [(8,2)]
  | 64 => some [(5,0)]
  | 65 => some [(4,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3),(6,0)]
  | 70 => some [(6,4)]
  | 71 => some [(1,2)]
  | 72 => some [(8,4)]
  | 73 => some [(0,0)]
  | 74 => some [(7,2)]
  | 75 => some [(4,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2),(8,2)]
  | 78 => some [(0,3)]
  | 79 => some [(8,1)]
  | 80 => some [(1,5)]
  | 81 => some [(6,1)]
  | 82 => some [(5,1)]
  | 83 => some [(0,1)]
  | 84 => some [(6,2)]
  | 85 => some [(5,3)]
  | 86 => some [(5,5),(8,5)]
  | 87 => some [(7,0)]
  | 88 => some [(8,3)]
  | 89 => some [(5,5),(8,5)]
  | _ => some [(1,0)]
theorem root2Node3Domains2_fast_eq : root2Node3Domains2 = expandDomains root2Node3Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root2Node3Domains2 v = expandDomains root2Node3Domains2Fast v from by decide) v
theorem root2Node3Step2Chunk0_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_0⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk0_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_1⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk0_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_2⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk0_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_3⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk0_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_4⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk0_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_5⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk1_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_0⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk1_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_1⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk1_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_2⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk1_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_3⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk1_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_4⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk1_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_5⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk2_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_0⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk2_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_1⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk2_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_2⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk2_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_3⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk2_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_4⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk2_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_5⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk3_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_0⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk3_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_1⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk3_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_2⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk3_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_3⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk3_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_4⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk3_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_5⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk4_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_0⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk4_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_1⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk4_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_2⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk4_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_3⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk4_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_4⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk4_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_5⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk5_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_0⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk5_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_1⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk5_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_2⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk5_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_3⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk5_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_4⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk5_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_5⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk6_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_0⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk6_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_1⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk6_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_2⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk6_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_3⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk6_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_4⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk6_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_5⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk7_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_0⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk7_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_1⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk7_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_2⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk7_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_3⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk7_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_4⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk7_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_5⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk8_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_0⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk8_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_1⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk8_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_2⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk8_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_3⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk8_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_4⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Chunk8_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_5⟩
      root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq (by decide)
theorem root2Node3Step2Narrowing_checked :
    checkNarrowing table52 root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkNarrowing_flatten table52Scope [table52Rows0_0,table52Rows0_1,table52Rows0_2,table52Rows0_3,table52Rows0_4,table52Rows0_5,table52Rows1_0,table52Rows1_1,table52Rows1_2,table52Rows1_3,table52Rows1_4,table52Rows1_5,table52Rows2_0,table52Rows2_1,table52Rows2_2,table52Rows2_3,table52Rows2_4,table52Rows2_5,table52Rows3_0,table52Rows3_1,table52Rows3_2,table52Rows3_3,table52Rows3_4,table52Rows3_5,table52Rows4_0,table52Rows4_1,table52Rows4_2,table52Rows4_3,table52Rows4_4,table52Rows4_5,table52Rows5_0,table52Rows5_1,table52Rows5_2,table52Rows5_3,table52Rows5_4,table52Rows5_5,table52Rows6_0,table52Rows6_1,table52Rows6_2,table52Rows6_3,table52Rows6_4,table52Rows6_5,table52Rows7_0,table52Rows7_1,table52Rows7_2,table52Rows7_3,table52Rows7_4,table52Rows7_5,table52Rows8_0,table52Rows8_1,table52Rows8_2,table52Rows8_3,table52Rows8_4,table52Rows8_5]
    root2Node3Domains1 root2Node3Domains2 (by
      simp only [List.all_cons, List.all_nil, root2Node3Step2Chunk0_0_checked, root2Node3Step2Chunk0_1_checked, root2Node3Step2Chunk0_2_checked, root2Node3Step2Chunk0_3_checked, root2Node3Step2Chunk0_4_checked, root2Node3Step2Chunk0_5_checked, root2Node3Step2Chunk1_0_checked, root2Node3Step2Chunk1_1_checked, root2Node3Step2Chunk1_2_checked, root2Node3Step2Chunk1_3_checked, root2Node3Step2Chunk1_4_checked, root2Node3Step2Chunk1_5_checked, root2Node3Step2Chunk2_0_checked, root2Node3Step2Chunk2_1_checked, root2Node3Step2Chunk2_2_checked, root2Node3Step2Chunk2_3_checked, root2Node3Step2Chunk2_4_checked, root2Node3Step2Chunk2_5_checked, root2Node3Step2Chunk3_0_checked, root2Node3Step2Chunk3_1_checked, root2Node3Step2Chunk3_2_checked, root2Node3Step2Chunk3_3_checked, root2Node3Step2Chunk3_4_checked, root2Node3Step2Chunk3_5_checked, root2Node3Step2Chunk4_0_checked, root2Node3Step2Chunk4_1_checked, root2Node3Step2Chunk4_2_checked, root2Node3Step2Chunk4_3_checked, root2Node3Step2Chunk4_4_checked, root2Node3Step2Chunk4_5_checked, root2Node3Step2Chunk5_0_checked, root2Node3Step2Chunk5_1_checked, root2Node3Step2Chunk5_2_checked, root2Node3Step2Chunk5_3_checked, root2Node3Step2Chunk5_4_checked, root2Node3Step2Chunk5_5_checked, root2Node3Step2Chunk6_0_checked, root2Node3Step2Chunk6_1_checked, root2Node3Step2Chunk6_2_checked, root2Node3Step2Chunk6_3_checked, root2Node3Step2Chunk6_4_checked, root2Node3Step2Chunk6_5_checked, root2Node3Step2Chunk7_0_checked, root2Node3Step2Chunk7_1_checked, root2Node3Step2Chunk7_2_checked, root2Node3Step2Chunk7_3_checked, root2Node3Step2Chunk7_4_checked, root2Node3Step2Chunk7_5_checked, root2Node3Step2Chunk8_0_checked, root2Node3Step2Chunk8_1_checked, root2Node3Step2Chunk8_2_checked, root2Node3Step2Chunk8_3_checked, root2Node3Step2Chunk8_4_checked, root2Node3Step2Chunk8_5_checked, Bool.true_and])
theorem root2Node3Step2_checked :
    checkReplacement table52 root2Node3Domains1 root2Node3Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root2Node3Domains1 root2Node3Domains2
    root2Node3Domains1Fast root2Node3Domains2Fast
    root2Node3Domains1_fast_eq root2Node3Domains2_fast_eq
    root2Node3Step2Narrowing_checked (by decide)
def root2Node4Domains0 : Domains 91 State := restrict root2Node3Domains2 12 (5,1)
def root2Node4Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,1)]
  | 1 => some [(0,1)]
  | 2 => some [(6,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(7,2)]
  | 6 => some [(8,3)]
  | 7 => some [(8,5)]
  | 8 => some [(1,0)]
  | 9 => some [(7,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(4,1),(5,1),(8,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(1,4)]
  | 44 => some [(0,5)]
  | 45 => some [(2,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3),(8,3)]
  | 50 => some [(5,2),(5,5)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(6,0)]
  | 55 => some [(3,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(1,4),(6,4)]
  | 60 => some [(0,5),(1,2)]
  | 61 => some [(8,0)]
  | 62 => some [(7,3)]
  | 63 => some [(8,2)]
  | 64 => some [(5,0)]
  | 65 => some [(4,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3),(6,0)]
  | 70 => some [(6,4)]
  | 71 => some [(1,2)]
  | 72 => some [(8,4)]
  | 73 => some [(0,0)]
  | 74 => some [(7,2)]
  | 75 => some [(4,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2),(8,2)]
  | 78 => some [(0,3)]
  | 79 => some [(8,1)]
  | 80 => some [(1,5)]
  | 81 => some [(6,1)]
  | 82 => some [(5,1)]
  | 83 => some [(0,1)]
  | 84 => some [(6,2)]
  | 85 => some [(5,3)]
  | 86 => some [(5,5),(8,5)]
  | 87 => some [(7,0)]
  | 88 => some [(8,3)]
  | 89 => some [(5,5),(8,5)]
  | _ => some [(1,0)]
theorem root2Node4Domains0_fast_eq : root2Node4Domains0 = expandDomains root2Node4Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root2Node4Domains0 v = expandDomains root2Node4Domains0Fast v from by decide) v
def root2Node4Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,1)]
  | 1 => [(0,1)]
  | 2 => [(6,2)]
  | 3 => [(8,4)]
  | 4 => [(0,0)]
  | 5 => [(7,2)]
  | 6 => [(8,3)]
  | 7 => [(8,5)]
  | 8 => [(1,0)]
  | 9 => [(7,1)]
  | 10 => [(1,5)]
  | 11 => [(6,1)]
  | 12 => [(5,1)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(8,1)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => [(7,2)]
  | 30 => [(8,3)]
  | 31 => [(5,5)]
  | 32 => [(7,0)]
  | 33 => [(4,3)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => [(5,1)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(1,4)]
  | 44 => [(0,5)]
  | 45 => [(2,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(8,0)]
  | 49 => [(8,3)]
  | 50 => [(5,5)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(7,5)]
  | 54 => [(6,0)]
  | 55 => [(3,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(1,4)]
  | 60 => [(0,5)]
  | 61 => [(8,0)]
  | 62 => [(7,3)]
  | 63 => [(8,2)]
  | 64 => [(5,0)]
  | 65 => [(4,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(6,0)]
  | 70 => [(6,4)]
  | 71 => [(1,2)]
  | 72 => [(8,4)]
  | 73 => [(0,0)]
  | 74 => [(7,2)]
  | 75 => [(4,0)]
  | 76 => [(7,3)]
  | 77 => [(8,2)]
  | 78 => [(0,3)]
  | 79 => [(8,1)]
  | 80 => [(1,5)]
  | 81 => [(6,1)]
  | 82 => [(5,1)]
  | 83 => [(0,1)]
  | 84 => [(6,2)]
  | 85 => [(5,3)]
  | 86 => [(5,5),(8,5)]
  | 87 => [(7,0)]
  | 88 => [(8,3)]
  | 89 => [(5,5),(8,5)]
  | _ => [(1,0)]
def root2Node4Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,1)]
  | 1 => some [(0,1)]
  | 2 => some [(6,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(7,2)]
  | 6 => some [(8,3)]
  | 7 => some [(8,5)]
  | 8 => some [(1,0)]
  | 9 => some [(7,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(5,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(1,4)]
  | 44 => some [(0,5)]
  | 45 => some [(2,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(8,0)]
  | 49 => some [(8,3)]
  | 50 => some [(5,5)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(6,0)]
  | 55 => some [(3,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(1,4)]
  | 60 => some [(0,5)]
  | 61 => some [(8,0)]
  | 62 => some [(7,3)]
  | 63 => some [(8,2)]
  | 64 => some [(5,0)]
  | 65 => some [(4,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(6,0)]
  | 70 => some [(6,4)]
  | 71 => some [(1,2)]
  | 72 => some [(8,4)]
  | 73 => some [(0,0)]
  | 74 => some [(7,2)]
  | 75 => some [(4,0)]
  | 76 => some [(7,3)]
  | 77 => some [(8,2)]
  | 78 => some [(0,3)]
  | 79 => some [(8,1)]
  | 80 => some [(1,5)]
  | 81 => some [(6,1)]
  | 82 => some [(5,1)]
  | 83 => some [(0,1)]
  | 84 => some [(6,2)]
  | 85 => some [(5,3)]
  | 86 => some [(5,5),(8,5)]
  | 87 => some [(7,0)]
  | 88 => some [(8,3)]
  | 89 => some [(5,5),(8,5)]
  | _ => some [(1,0)]
theorem root2Node4Domains1_fast_eq : root2Node4Domains1 = expandDomains root2Node4Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root2Node4Domains1 v = expandDomains root2Node4Domains1Fast v from by decide) v
theorem root2Node4Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq (by decide)
theorem root2Node4Step1Narrowing_checked :
    checkNarrowing table36 root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root2Node4Domains0 root2Node4Domains1 (by
      simp only [List.all_cons, List.all_nil, root2Node4Step1Chunk0_0_checked, root2Node4Step1Chunk0_1_checked, root2Node4Step1Chunk0_2_checked, root2Node4Step1Chunk0_3_checked, root2Node4Step1Chunk0_4_checked, root2Node4Step1Chunk0_5_checked, root2Node4Step1Chunk1_0_checked, root2Node4Step1Chunk1_1_checked, root2Node4Step1Chunk1_2_checked, root2Node4Step1Chunk1_3_checked, root2Node4Step1Chunk1_4_checked, root2Node4Step1Chunk1_5_checked, root2Node4Step1Chunk2_0_checked, root2Node4Step1Chunk2_1_checked, root2Node4Step1Chunk2_2_checked, root2Node4Step1Chunk2_3_checked, root2Node4Step1Chunk2_4_checked, root2Node4Step1Chunk2_5_checked, root2Node4Step1Chunk3_0_checked, root2Node4Step1Chunk3_1_checked, root2Node4Step1Chunk3_2_checked, root2Node4Step1Chunk3_3_checked, root2Node4Step1Chunk3_4_checked, root2Node4Step1Chunk3_5_checked, root2Node4Step1Chunk4_0_checked, root2Node4Step1Chunk4_1_checked, root2Node4Step1Chunk4_2_checked, root2Node4Step1Chunk4_3_checked, root2Node4Step1Chunk4_4_checked, root2Node4Step1Chunk4_5_checked, root2Node4Step1Chunk5_0_checked, root2Node4Step1Chunk5_1_checked, root2Node4Step1Chunk5_2_checked, root2Node4Step1Chunk5_3_checked, root2Node4Step1Chunk5_4_checked, root2Node4Step1Chunk5_5_checked, root2Node4Step1Chunk6_0_checked, root2Node4Step1Chunk6_1_checked, root2Node4Step1Chunk6_2_checked, root2Node4Step1Chunk6_3_checked, root2Node4Step1Chunk6_4_checked, root2Node4Step1Chunk6_5_checked, root2Node4Step1Chunk7_0_checked, root2Node4Step1Chunk7_1_checked, root2Node4Step1Chunk7_2_checked, root2Node4Step1Chunk7_3_checked, root2Node4Step1Chunk7_4_checked, root2Node4Step1Chunk7_5_checked, root2Node4Step1Chunk8_0_checked, root2Node4Step1Chunk8_1_checked, root2Node4Step1Chunk8_2_checked, root2Node4Step1Chunk8_3_checked, root2Node4Step1Chunk8_4_checked, root2Node4Step1Chunk8_5_checked, Bool.true_and])
theorem root2Node4Step1_checked :
    checkReplacement table36 root2Node4Domains0 root2Node4Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root2Node4Domains0 root2Node4Domains1
    root2Node4Domains0Fast root2Node4Domains1Fast
    root2Node4Domains0_fast_eq root2Node4Domains1_fast_eq
    root2Node4Step1Narrowing_checked (by decide)
def root2Node4Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,1)]
  | 1 => [(0,1)]
  | 2 => [(6,2)]
  | 3 => [(8,4)]
  | 4 => [(0,0)]
  | 5 => [(7,2)]
  | 6 => [(8,3)]
  | 7 => [(8,5)]
  | 8 => [(1,0)]
  | 9 => [(7,1)]
  | 10 => [(1,5)]
  | 11 => [(6,1)]
  | 12 => [(5,1)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(8,1)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => [(7,2)]
  | 30 => [(8,3)]
  | 31 => [(5,5)]
  | 32 => [(7,0)]
  | 33 => [(4,3)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => [(5,1)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(1,4)]
  | 44 => [(0,5)]
  | 45 => [(2,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(8,0)]
  | 49 => [(8,3)]
  | 50 => [(5,5)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(7,5)]
  | 54 => [(6,0)]
  | 55 => [(3,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(1,4)]
  | 60 => [(0,5)]
  | 61 => [(8,0)]
  | 62 => [(7,3)]
  | 63 => [(8,2)]
  | 64 => [(5,0)]
  | 65 => [(4,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(6,0)]
  | 70 => [(6,4)]
  | 71 => [(1,2)]
  | 72 => [(8,4)]
  | 73 => [(0,0)]
  | 74 => [(7,2)]
  | 75 => [(4,0)]
  | 76 => [(7,3)]
  | 77 => [(8,2)]
  | 78 => [(0,3)]
  | 79 => [(8,1)]
  | 80 => [(1,5)]
  | 81 => [(6,1)]
  | 82 => [(5,1)]
  | 83 => [(0,1)]
  | 84 => [(6,2)]
  | 85 => [(5,3)]
  | 86 => [(8,5)]
  | 87 => [(7,0)]
  | 88 => [(8,3)]
  | 89 => [(8,5)]
  | _ => [(1,0)]
def root2Node4Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,1)]
  | 1 => some [(0,1)]
  | 2 => some [(6,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(7,2)]
  | 6 => some [(8,3)]
  | 7 => some [(8,5)]
  | 8 => some [(1,0)]
  | 9 => some [(7,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(5,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(1,4)]
  | 44 => some [(0,5)]
  | 45 => some [(2,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(8,0)]
  | 49 => some [(8,3)]
  | 50 => some [(5,5)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(6,0)]
  | 55 => some [(3,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(1,4)]
  | 60 => some [(0,5)]
  | 61 => some [(8,0)]
  | 62 => some [(7,3)]
  | 63 => some [(8,2)]
  | 64 => some [(5,0)]
  | 65 => some [(4,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(6,0)]
  | 70 => some [(6,4)]
  | 71 => some [(1,2)]
  | 72 => some [(8,4)]
  | 73 => some [(0,0)]
  | 74 => some [(7,2)]
  | 75 => some [(4,0)]
  | 76 => some [(7,3)]
  | 77 => some [(8,2)]
  | 78 => some [(0,3)]
  | 79 => some [(8,1)]
  | 80 => some [(1,5)]
  | 81 => some [(6,1)]
  | 82 => some [(5,1)]
  | 83 => some [(0,1)]
  | 84 => some [(6,2)]
  | 85 => some [(5,3)]
  | 86 => some [(8,5)]
  | 87 => some [(7,0)]
  | 88 => some [(8,3)]
  | 89 => some [(8,5)]
  | _ => some [(1,0)]
theorem root2Node4Domains2_fast_eq : root2Node4Domains2 = expandDomains root2Node4Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root2Node4Domains2 v = expandDomains root2Node4Domains2Fast v from by decide) v
theorem root2Node4Step2Chunk0_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_0⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk0_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_1⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk0_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_2⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk0_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_3⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk0_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_4⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk0_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_5⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk1_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_0⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk1_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_1⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk1_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_2⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk1_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_3⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk1_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_4⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk1_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_5⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk2_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_0⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk2_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_1⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk2_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_2⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk2_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_3⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk2_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_4⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk2_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_5⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk3_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_0⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk3_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_1⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk3_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_2⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk3_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_3⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk3_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_4⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk3_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_5⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk4_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_0⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk4_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_1⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk4_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_2⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk4_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_3⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk4_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_4⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk4_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_5⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk5_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_0⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk5_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_1⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk5_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_2⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk5_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_3⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk5_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_4⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk5_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_5⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk6_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_0⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk6_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_1⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk6_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_2⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk6_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_3⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk6_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_4⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk6_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_5⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk7_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_0⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk7_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_1⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk7_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_2⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk7_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_3⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk7_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_4⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk7_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_5⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk8_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_0⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk8_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_1⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk8_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_2⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk8_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_3⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk8_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_4⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Chunk8_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_5⟩
      root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq (by decide)
theorem root2Node4Step2Narrowing_checked :
    checkNarrowing table55 root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkNarrowing_flatten table55Scope [table55Rows0_0,table55Rows0_1,table55Rows0_2,table55Rows0_3,table55Rows0_4,table55Rows0_5,table55Rows1_0,table55Rows1_1,table55Rows1_2,table55Rows1_3,table55Rows1_4,table55Rows1_5,table55Rows2_0,table55Rows2_1,table55Rows2_2,table55Rows2_3,table55Rows2_4,table55Rows2_5,table55Rows3_0,table55Rows3_1,table55Rows3_2,table55Rows3_3,table55Rows3_4,table55Rows3_5,table55Rows4_0,table55Rows4_1,table55Rows4_2,table55Rows4_3,table55Rows4_4,table55Rows4_5,table55Rows5_0,table55Rows5_1,table55Rows5_2,table55Rows5_3,table55Rows5_4,table55Rows5_5,table55Rows6_0,table55Rows6_1,table55Rows6_2,table55Rows6_3,table55Rows6_4,table55Rows6_5,table55Rows7_0,table55Rows7_1,table55Rows7_2,table55Rows7_3,table55Rows7_4,table55Rows7_5,table55Rows8_0,table55Rows8_1,table55Rows8_2,table55Rows8_3,table55Rows8_4,table55Rows8_5]
    root2Node4Domains1 root2Node4Domains2 (by
      simp only [List.all_cons, List.all_nil, root2Node4Step2Chunk0_0_checked, root2Node4Step2Chunk0_1_checked, root2Node4Step2Chunk0_2_checked, root2Node4Step2Chunk0_3_checked, root2Node4Step2Chunk0_4_checked, root2Node4Step2Chunk0_5_checked, root2Node4Step2Chunk1_0_checked, root2Node4Step2Chunk1_1_checked, root2Node4Step2Chunk1_2_checked, root2Node4Step2Chunk1_3_checked, root2Node4Step2Chunk1_4_checked, root2Node4Step2Chunk1_5_checked, root2Node4Step2Chunk2_0_checked, root2Node4Step2Chunk2_1_checked, root2Node4Step2Chunk2_2_checked, root2Node4Step2Chunk2_3_checked, root2Node4Step2Chunk2_4_checked, root2Node4Step2Chunk2_5_checked, root2Node4Step2Chunk3_0_checked, root2Node4Step2Chunk3_1_checked, root2Node4Step2Chunk3_2_checked, root2Node4Step2Chunk3_3_checked, root2Node4Step2Chunk3_4_checked, root2Node4Step2Chunk3_5_checked, root2Node4Step2Chunk4_0_checked, root2Node4Step2Chunk4_1_checked, root2Node4Step2Chunk4_2_checked, root2Node4Step2Chunk4_3_checked, root2Node4Step2Chunk4_4_checked, root2Node4Step2Chunk4_5_checked, root2Node4Step2Chunk5_0_checked, root2Node4Step2Chunk5_1_checked, root2Node4Step2Chunk5_2_checked, root2Node4Step2Chunk5_3_checked, root2Node4Step2Chunk5_4_checked, root2Node4Step2Chunk5_5_checked, root2Node4Step2Chunk6_0_checked, root2Node4Step2Chunk6_1_checked, root2Node4Step2Chunk6_2_checked, root2Node4Step2Chunk6_3_checked, root2Node4Step2Chunk6_4_checked, root2Node4Step2Chunk6_5_checked, root2Node4Step2Chunk7_0_checked, root2Node4Step2Chunk7_1_checked, root2Node4Step2Chunk7_2_checked, root2Node4Step2Chunk7_3_checked, root2Node4Step2Chunk7_4_checked, root2Node4Step2Chunk7_5_checked, root2Node4Step2Chunk8_0_checked, root2Node4Step2Chunk8_1_checked, root2Node4Step2Chunk8_2_checked, root2Node4Step2Chunk8_3_checked, root2Node4Step2Chunk8_4_checked, root2Node4Step2Chunk8_5_checked, Bool.true_and])
theorem root2Node4Step2_checked :
    checkReplacement table55 root2Node4Domains1 root2Node4Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root2Node4Domains1 root2Node4Domains2
    root2Node4Domains1Fast root2Node4Domains2Fast
    root2Node4Domains1_fast_eq root2Node4Domains2_fast_eq
    root2Node4Step2Narrowing_checked (by decide)
theorem root2Node4Leaf_checked :
    checkCover 1 constraints root2Outputs root2Node4Domains2 (.output 1) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
