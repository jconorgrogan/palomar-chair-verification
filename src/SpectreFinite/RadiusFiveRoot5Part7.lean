module

public import SpectreFinite.RadiusFiveRoot5Part6
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable13
public import SpectreFinite.RadiusFiveTable2
public import SpectreFinite.RadiusFiveTable25
public import SpectreFinite.RadiusFiveTable65

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node15Domains0 : Domains 91 State := restrict root5Node13Domains1 5 (4,4)
def root5Node15Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(4,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(2,5)]
  | 7 => some [(6,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(1,5),(6,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(7,0)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(0,0)]
  | 28 => some [(7,2)]
  | 29 => some [(7,4)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(8,1)]
  | 39 => some [(6,5)]
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
  | 50 => some [(7,0)]
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
theorem root5Node15Domains0_fast_eq : root5Node15Domains0 = expandDomains root5Node15Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node15Domains0 v = expandDomains root5Node15Domains0Fast v from by decide) v
def root5Node15Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,4)]
  | 6 => [(2,5)]
  | 7 => [(6,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(6,0)]
  | 11 => [(7,1)]
  | 12 => [(1,5)]
  | 13 => [(0,0)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(7,0)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(0,0)]
  | 28 => [(7,2)]
  | 29 => [(7,4)]
  | 30 => [(4,5)]
  | 31 => [(7,0)]
  | 32 => [(8,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(8,1)]
  | 39 => [(6,5)]
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
  | 50 => [(7,0)]
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
def root5Node15Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(4,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(2,5)]
  | 7 => some [(6,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(1,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(7,0)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(0,0)]
  | 28 => some [(7,2)]
  | 29 => some [(7,4)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(8,1)]
  | 39 => some [(6,5)]
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
  | 50 => some [(7,0)]
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
theorem root5Node15Domains1_fast_eq : root5Node15Domains1 = expandDomains root5Node15Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node15Domains1 v = expandDomains root5Node15Domains1Fast v from by decide) v
theorem root5Node15Step1Chunk0_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk0_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk0_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk0_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk0_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk0_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk1_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk1_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk1_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk1_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk1_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk1_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk2_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk2_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk2_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk2_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk2_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk2_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk3_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk3_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk3_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk3_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk3_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk3_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk4_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk4_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk4_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk4_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk4_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk4_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk5_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk5_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk5_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk5_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk5_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk5_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk6_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk6_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk6_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk6_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk6_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk6_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk7_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk7_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk7_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk7_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk7_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk7_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk8_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk8_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk8_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk8_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk8_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk8_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Narrowing_checked :
    checkNarrowing table2 root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_flatten table2Scope [table2Rows0_0,table2Rows0_1,table2Rows0_2,table2Rows0_3,table2Rows0_4,table2Rows0_5,table2Rows1_0,table2Rows1_1,table2Rows1_2,table2Rows1_3,table2Rows1_4,table2Rows1_5,table2Rows2_0,table2Rows2_1,table2Rows2_2,table2Rows2_3,table2Rows2_4,table2Rows2_5,table2Rows3_0,table2Rows3_1,table2Rows3_2,table2Rows3_3,table2Rows3_4,table2Rows3_5,table2Rows4_0,table2Rows4_1,table2Rows4_2,table2Rows4_3,table2Rows4_4,table2Rows4_5,table2Rows5_0,table2Rows5_1,table2Rows5_2,table2Rows5_3,table2Rows5_4,table2Rows5_5,table2Rows6_0,table2Rows6_1,table2Rows6_2,table2Rows6_3,table2Rows6_4,table2Rows6_5,table2Rows7_0,table2Rows7_1,table2Rows7_2,table2Rows7_3,table2Rows7_4,table2Rows7_5,table2Rows8_0,table2Rows8_1,table2Rows8_2,table2Rows8_3,table2Rows8_4,table2Rows8_5]
    root5Node15Domains0 root5Node15Domains1 (by
      simp only [List.all_cons, List.all_nil, root5Node15Step1Chunk0_0_checked, root5Node15Step1Chunk0_1_checked, root5Node15Step1Chunk0_2_checked, root5Node15Step1Chunk0_3_checked, root5Node15Step1Chunk0_4_checked, root5Node15Step1Chunk0_5_checked, root5Node15Step1Chunk1_0_checked, root5Node15Step1Chunk1_1_checked, root5Node15Step1Chunk1_2_checked, root5Node15Step1Chunk1_3_checked, root5Node15Step1Chunk1_4_checked, root5Node15Step1Chunk1_5_checked, root5Node15Step1Chunk2_0_checked, root5Node15Step1Chunk2_1_checked, root5Node15Step1Chunk2_2_checked, root5Node15Step1Chunk2_3_checked, root5Node15Step1Chunk2_4_checked, root5Node15Step1Chunk2_5_checked, root5Node15Step1Chunk3_0_checked, root5Node15Step1Chunk3_1_checked, root5Node15Step1Chunk3_2_checked, root5Node15Step1Chunk3_3_checked, root5Node15Step1Chunk3_4_checked, root5Node15Step1Chunk3_5_checked, root5Node15Step1Chunk4_0_checked, root5Node15Step1Chunk4_1_checked, root5Node15Step1Chunk4_2_checked, root5Node15Step1Chunk4_3_checked, root5Node15Step1Chunk4_4_checked, root5Node15Step1Chunk4_5_checked, root5Node15Step1Chunk5_0_checked, root5Node15Step1Chunk5_1_checked, root5Node15Step1Chunk5_2_checked, root5Node15Step1Chunk5_3_checked, root5Node15Step1Chunk5_4_checked, root5Node15Step1Chunk5_5_checked, root5Node15Step1Chunk6_0_checked, root5Node15Step1Chunk6_1_checked, root5Node15Step1Chunk6_2_checked, root5Node15Step1Chunk6_3_checked, root5Node15Step1Chunk6_4_checked, root5Node15Step1Chunk6_5_checked, root5Node15Step1Chunk7_0_checked, root5Node15Step1Chunk7_1_checked, root5Node15Step1Chunk7_2_checked, root5Node15Step1Chunk7_3_checked, root5Node15Step1Chunk7_4_checked, root5Node15Step1Chunk7_5_checked, root5Node15Step1Chunk8_0_checked, root5Node15Step1Chunk8_1_checked, root5Node15Step1Chunk8_2_checked, root5Node15Step1Chunk8_3_checked, root5Node15Step1Chunk8_4_checked, root5Node15Step1Chunk8_5_checked, Bool.true_and])
theorem root5Node15Step1_checked :
    checkReplacement table2 root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq
    root5Node15Step1Narrowing_checked (by decide)
theorem root5Node15Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node15Domains1 (.output 7) = true := by decide
def root5Node16Domains0 : Domains 91 State := restrict root5Node0Domains4 43 (7,3)
def root5Node16Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(3,4),(7,4),(8,4)]
  | 1 => some [(0,0),(0,5),(1,3),(6,2),(6,3)]
  | 2 => some [(4,4),(7,2),(8,2),(8,4)]
  | 3 => some [(1,4),(4,0),(5,0),(7,4),(8,0)]
  | 4 => some [(0,5),(1,3),(4,5),(6,3),(7,3)]
  | 5 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(7,0)]
  | 6 => some [(2,1),(2,3),(2,5),(4,1),(4,5),(8,1)]
  | 7 => some [(0,2),(1,0),(1,5),(6,0),(6,5)]
  | 8 => some [(0,4),(1,1),(6,1),(7,1)]
  | 9 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 10 => some [(0,0),(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 11 => some [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 12 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 13 => some [(0,0),(1,3),(3,3),(5,3),(6,4),(7,3),(8,3)]
  | 14 => some [(1,2),(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 15 => some [(4,0),(7,0),(8,0)]
  | 16 => some [(4,3),(7,3),(8,3)]
  | 17 => some [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 18 => some [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 19 => some [(2,1),(2,5),(4,1),(4,5)]
  | 20 => some [(0,2),(1,0),(6,0),(7,0)]
  | 21 => some [(0,1),(1,4),(1,5),(3,4),(6,5),(7,4),(7,5)]
  | 22 => some [(0,3),(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 23 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 24 => some [(0,1),(1,4),(7,4)]
  | 25 => some [(0,5),(6,2),(6,3)]
  | 26 => some [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 27 => some [(0,0),(1,3),(3,3),(7,3)]
  | 28 => some [(3,2),(5,2),(7,2)]
  | 29 => some [(4,0),(7,4),(8,0)]
  | 30 => some [(2,1),(2,3),(2,5),(4,1),(4,5),(7,3),(7,5),(8,5)]
  | 31 => some [(0,2),(1,0),(4,2),(6,0),(7,0)]
  | 32 => some [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 33 => some [(4,1),(7,5),(8,5)]
  | 34 => some [(0,2),(1,0),(6,0)]
  | 35 => some [(1,1),(3,1),(7,1)]
  | 36 => some [(0,1),(1,5),(6,5)]
  | 37 => some [(0,4),(6,1),(6,2)]
  | 38 => some [(5,1),(5,4),(8,1),(8,4)]
  | 39 => some [(0,1),(1,4),(6,4),(6,5)]
  | 40 => some [(0,0),(1,3),(3,3),(6,3),(6,4),(7,3)]
  | 41 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 42 => some [(4,0),(7,4),(8,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2),(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0),(7,0)]
  | 48 => some [(4,3),(7,1),(8,3)]
  | 49 => some [(7,5),(8,5)]
  | 50 => some [(0,3),(1,0),(6,0),(7,0)]
  | 51 => some [(0,3),(0,4),(1,1),(6,1),(6,2)]
  | 52 => some [(5,1),(5,4),(8,1),(8,4)]
  | 53 => some [(0,1),(6,4),(6,5)]
  | 54 => some [(0,4),(1,2),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0),(7,4)]
  | 59 => some [(1,3),(6,3),(7,3)]
  | 60 => some [(4,2),(7,2),(8,2)]
  | 61 => some [(4,3),(5,3),(7,1),(8,3)]
  | 62 => some [(5,5),(7,5),(8,5)]
  | 63 => some [(0,3),(1,0),(7,0)]
  | 64 => some [(4,3),(7,1),(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1),(5,1),(8,1)]
  | 68 => some [(0,1),(0,2),(6,5)]
  | 69 => some [(0,4),(1,1),(6,2)]
  | 70 => some [(0,5),(1,3),(7,3)]
  | 71 => some [(4,2),(4,4),(8,2)]
  | 72 => some [(1,4),(5,0),(5,3)]
  | 73 => some [(0,5),(4,5),(5,5),(8,5)]
  | 74 => some [(2,0),(7,0)]
  | 75 => some [(7,3),(8,3)]
  | 76 => some [(5,2),(5,5),(8,5)]
  | 77 => some [(1,0),(3,0),(7,0),(8,0)]
  | 78 => some [(0,4),(1,2),(6,2),(7,1)]
  | 79 => some [(1,4),(3,4),(5,4),(7,4),(7,5)]
  | 80 => some [(0,0),(0,5),(6,0),(6,3)]
  | 81 => some [(3,1),(4,4),(7,2)]
  | 82 => some [(0,1),(1,4),(7,4)]
  | 83 => some [(0,5),(1,3),(6,2),(6,3)]
  | 84 => some [(4,4),(7,2),(8,2),(8,4)]
  | 85 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,3)]
  | 86 => some [(0,2),(1,5),(6,0),(8,2)]
  | 87 => some [(1,1),(5,0),(6,1),(7,1)]
  | 88 => some [(4,1),(4,5),(7,5),(8,1)]
  | 89 => some [(0,2),(1,0),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root5Node16Domains0_fast_eq : root5Node16Domains0 = expandDomains root5Node16Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node16Domains0 v = expandDomains root5Node16Domains0Fast v from by decide) v
def root5Node16Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4),(8,4)]
  | 1 => [(0,0),(1,3),(6,3)]
  | 2 => [(7,2),(8,2)]
  | 3 => [(4,0),(5,0),(7,4),(8,0)]
  | 4 => [(1,3),(4,5),(7,3)]
  | 5 => [(4,2),(7,0)]
  | 6 => [(4,1),(8,1)]
  | 7 => [(0,2),(1,5),(6,5)]
  | 8 => [(0,4),(1,1),(6,1)]
  | 9 => [(5,1),(5,4),(8,1)]
  | 10 => [(0,0),(0,1),(6,4),(6,5)]
  | 11 => [(0,4),(1,2),(6,2),(7,2)]
  | 12 => [(1,4),(7,4)]
  | 13 => [(3,3),(5,3),(7,3),(8,3)]
  | 14 => [(5,2),(5,5),(8,5)]
  | 15 => [(7,0),(8,0)]
  | 16 => [(4,3),(8,3)]
  | 17 => [(1,5),(3,5),(5,5),(7,5)]
  | 18 => [(0,3),(1,0),(3,0),(6,1)]
  | 19 => [(2,1),(2,5),(4,1)]
  | 20 => [(0,2),(6,0)]
  | 21 => [(0,1),(1,4),(3,4),(7,4)]
  | 22 => [(0,5),(6,2),(6,3)]
  | 23 => [(4,4),(7,2),(8,4)]
  | 24 => [(1,4),(7,4)]
  | 25 => [(0,5),(6,3)]
  | 26 => [(2,0),(2,2),(2,4),(4,4)]
  | 27 => [(0,0),(1,3),(3,3),(7,3)]
  | 28 => [(3,2),(5,2),(7,2)]
  | 29 => [(4,0),(8,0)]
  | 30 => [(2,1),(2,3),(2,5),(4,1),(4,5),(7,3),(7,5),(8,5)]
  | 31 => [(0,2),(1,0),(6,0)]
  | 32 => [(1,1),(7,1)]
  | 33 => [(4,1),(7,5)]
  | 34 => [(0,2),(6,0)]
  | 35 => [(1,1),(3,1),(7,1)]
  | 36 => [(0,1),(1,5),(6,5)]
  | 37 => [(0,4),(6,1),(6,2)]
  | 38 => [(5,1),(5,4),(8,4)]
  | 39 => [(0,1),(1,4),(6,4),(6,5)]
  | 40 => [(0,0),(1,3),(3,3),(6,3),(6,4),(7,3)]
  | 41 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 42 => [(4,0),(8,0)]
  | 43 => [(7,3)]
  | 44 => [(5,2),(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(1,0),(7,0)]
  | 48 => [(4,3),(7,1),(8,3)]
  | 49 => [(7,5),(8,5)]
  | 50 => [(0,3),(1,0),(6,0),(7,0)]
  | 51 => [(0,3),(0,4),(1,1),(6,1),(6,2)]
  | 52 => [(5,1),(5,4),(8,1),(8,4)]
  | 53 => [(0,1),(6,4)]
  | 54 => [(1,2),(6,2)]
  | 55 => [(8,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(4,0),(7,4)]
  | 59 => [(1,3),(6,3),(7,3)]
  | 60 => [(4,2),(7,2),(8,2)]
  | 61 => [(4,3),(5,3),(7,1),(8,3)]
  | 62 => [(5,5),(7,5),(8,5)]
  | 63 => [(0,3),(1,0)]
  | 64 => [(7,1),(8,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(5,1),(8,1)]
  | 68 => [(0,1),(0,2),(6,5)]
  | 69 => [(0,4),(1,1),(6,2)]
  | 70 => [(0,5),(1,3),(7,3)]
  | 71 => [(4,2),(4,4),(8,2)]
  | 72 => [(1,4),(5,0),(5,3)]
  | 73 => [(0,5),(4,5),(5,5),(8,5)]
  | 74 => [(2,0),(7,0)]
  | 75 => [(7,3),(8,3)]
  | 76 => [(5,2),(5,5),(8,5)]
  | 77 => [(1,0),(3,0),(7,0),(8,0)]
  | 78 => [(0,4),(1,2),(6,2),(7,1)]
  | 79 => [(1,4),(3,4),(5,4),(7,4),(7,5)]
  | 80 => [(0,0),(0,5),(6,0),(6,3)]
  | 81 => [(3,1),(4,4),(7,2)]
  | 82 => [(0,1),(1,4),(7,4)]
  | 83 => [(0,5),(1,3),(6,2),(6,3)]
  | 84 => [(4,4),(7,2),(8,2),(8,4)]
  | 85 => [(2,1),(2,3),(2,5),(4,1),(4,3),(7,3)]
  | 86 => [(0,2),(1,5),(6,0),(8,2)]
  | 87 => [(1,1),(5,0),(6,1),(7,1)]
  | 88 => [(4,1),(4,5),(7,5),(8,1)]
  | 89 => [(0,2),(1,0),(6,0),(6,5)]
  | _ => [(0,4),(1,1),(7,1)]
def root5Node16Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4),(8,4)]
  | 1 => some [(0,0),(1,3),(6,3)]
  | 2 => some [(7,2),(8,2)]
  | 3 => some [(4,0),(5,0),(7,4),(8,0)]
  | 4 => some [(1,3),(4,5),(7,3)]
  | 5 => some [(4,2),(7,0)]
  | 6 => some [(4,1),(8,1)]
  | 7 => some [(0,2),(1,5),(6,5)]
  | 8 => some [(0,4),(1,1),(6,1)]
  | 9 => some [(5,1),(5,4),(8,1)]
  | 10 => some [(0,0),(0,1),(6,4),(6,5)]
  | 11 => some [(0,4),(1,2),(6,2),(7,2)]
  | 12 => some [(1,4),(7,4)]
  | 13 => some [(3,3),(5,3),(7,3),(8,3)]
  | 14 => some [(5,2),(5,5),(8,5)]
  | 15 => some [(7,0),(8,0)]
  | 16 => some [(4,3),(8,3)]
  | 17 => some [(1,5),(3,5),(5,5),(7,5)]
  | 18 => some [(0,3),(1,0),(3,0),(6,1)]
  | 19 => some [(2,1),(2,5),(4,1)]
  | 20 => some [(0,2),(6,0)]
  | 21 => some [(0,1),(1,4),(3,4),(7,4)]
  | 22 => some [(0,5),(6,2),(6,3)]
  | 23 => some [(4,4),(7,2),(8,4)]
  | 24 => some [(1,4),(7,4)]
  | 25 => some [(0,5),(6,3)]
  | 26 => some [(2,0),(2,2),(2,4),(4,4)]
  | 27 => some [(0,0),(1,3),(3,3),(7,3)]
  | 28 => some [(3,2),(5,2),(7,2)]
  | 29 => some [(4,0),(8,0)]
  | 30 => some [(2,1),(2,3),(2,5),(4,1),(4,5),(7,3),(7,5),(8,5)]
  | 31 => some [(0,2),(1,0),(6,0)]
  | 32 => some [(1,1),(7,1)]
  | 33 => some [(4,1),(7,5)]
  | 34 => some [(0,2),(6,0)]
  | 35 => some [(1,1),(3,1),(7,1)]
  | 36 => some [(0,1),(1,5),(6,5)]
  | 37 => some [(0,4),(6,1),(6,2)]
  | 38 => some [(5,1),(5,4),(8,4)]
  | 39 => some [(0,1),(1,4),(6,4),(6,5)]
  | 40 => some [(0,0),(1,3),(3,3),(6,3),(6,4),(7,3)]
  | 41 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 42 => some [(4,0),(8,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2),(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0),(7,0)]
  | 48 => some [(4,3),(7,1),(8,3)]
  | 49 => some [(7,5),(8,5)]
  | 50 => some [(0,3),(1,0),(6,0),(7,0)]
  | 51 => some [(0,3),(0,4),(1,1),(6,1),(6,2)]
  | 52 => some [(5,1),(5,4),(8,1),(8,4)]
  | 53 => some [(0,1),(6,4)]
  | 54 => some [(1,2),(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0),(7,4)]
  | 59 => some [(1,3),(6,3),(7,3)]
  | 60 => some [(4,2),(7,2),(8,2)]
  | 61 => some [(4,3),(5,3),(7,1),(8,3)]
  | 62 => some [(5,5),(7,5),(8,5)]
  | 63 => some [(0,3),(1,0)]
  | 64 => some [(7,1),(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1),(8,1)]
  | 68 => some [(0,1),(0,2),(6,5)]
  | 69 => some [(0,4),(1,1),(6,2)]
  | 70 => some [(0,5),(1,3),(7,3)]
  | 71 => some [(4,2),(4,4),(8,2)]
  | 72 => some [(1,4),(5,0),(5,3)]
  | 73 => some [(0,5),(4,5),(5,5),(8,5)]
  | 74 => some [(2,0),(7,0)]
  | 75 => some [(7,3),(8,3)]
  | 76 => some [(5,2),(5,5),(8,5)]
  | 77 => some [(1,0),(3,0),(7,0),(8,0)]
  | 78 => some [(0,4),(1,2),(6,2),(7,1)]
  | 79 => some [(1,4),(3,4),(5,4),(7,4),(7,5)]
  | 80 => some [(0,0),(0,5),(6,0),(6,3)]
  | 81 => some [(3,1),(4,4),(7,2)]
  | 82 => some [(0,1),(1,4),(7,4)]
  | 83 => some [(0,5),(1,3),(6,2),(6,3)]
  | 84 => some [(4,4),(7,2),(8,2),(8,4)]
  | 85 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,3)]
  | 86 => some [(0,2),(1,5),(6,0),(8,2)]
  | 87 => some [(1,1),(5,0),(6,1),(7,1)]
  | 88 => some [(4,1),(4,5),(7,5),(8,1)]
  | 89 => some [(0,2),(1,0),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root5Node16Domains1_fast_eq : root5Node16Domains1 = expandDomains root5Node16Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node16Domains1 v = expandDomains root5Node16Domains1Fast v from by decide) v
theorem root5Node16Step1Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Narrowing_checked :
    checkNarrowing table25 root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_flatten table25Scope [table25Rows0_0,table25Rows0_1,table25Rows0_2,table25Rows0_3,table25Rows0_4,table25Rows0_5,table25Rows1_0,table25Rows1_1,table25Rows1_2,table25Rows1_3,table25Rows1_4,table25Rows1_5,table25Rows2_0,table25Rows2_1,table25Rows2_2,table25Rows2_3,table25Rows2_4,table25Rows2_5,table25Rows3_0,table25Rows3_1,table25Rows3_2,table25Rows3_3,table25Rows3_4,table25Rows3_5,table25Rows4_0,table25Rows4_1,table25Rows4_2,table25Rows4_3,table25Rows4_4,table25Rows4_5,table25Rows5_0,table25Rows5_1,table25Rows5_2,table25Rows5_3,table25Rows5_4,table25Rows5_5,table25Rows6_0,table25Rows6_1,table25Rows6_2,table25Rows6_3,table25Rows6_4,table25Rows6_5,table25Rows7_0,table25Rows7_1,table25Rows7_2,table25Rows7_3,table25Rows7_4,table25Rows7_5,table25Rows8_0,table25Rows8_1,table25Rows8_2,table25Rows8_3,table25Rows8_4,table25Rows8_5]
    root5Node16Domains0 root5Node16Domains1 (by
      simp only [List.all_cons, List.all_nil, root5Node16Step1Chunk0_0_checked, root5Node16Step1Chunk0_1_checked, root5Node16Step1Chunk0_2_checked, root5Node16Step1Chunk0_3_checked, root5Node16Step1Chunk0_4_checked, root5Node16Step1Chunk0_5_checked, root5Node16Step1Chunk1_0_checked, root5Node16Step1Chunk1_1_checked, root5Node16Step1Chunk1_2_checked, root5Node16Step1Chunk1_3_checked, root5Node16Step1Chunk1_4_checked, root5Node16Step1Chunk1_5_checked, root5Node16Step1Chunk2_0_checked, root5Node16Step1Chunk2_1_checked, root5Node16Step1Chunk2_2_checked, root5Node16Step1Chunk2_3_checked, root5Node16Step1Chunk2_4_checked, root5Node16Step1Chunk2_5_checked, root5Node16Step1Chunk3_0_checked, root5Node16Step1Chunk3_1_checked, root5Node16Step1Chunk3_2_checked, root5Node16Step1Chunk3_3_checked, root5Node16Step1Chunk3_4_checked, root5Node16Step1Chunk3_5_checked, root5Node16Step1Chunk4_0_checked, root5Node16Step1Chunk4_1_checked, root5Node16Step1Chunk4_2_checked, root5Node16Step1Chunk4_3_checked, root5Node16Step1Chunk4_4_checked, root5Node16Step1Chunk4_5_checked, root5Node16Step1Chunk5_0_checked, root5Node16Step1Chunk5_1_checked, root5Node16Step1Chunk5_2_checked, root5Node16Step1Chunk5_3_checked, root5Node16Step1Chunk5_4_checked, root5Node16Step1Chunk5_5_checked, root5Node16Step1Chunk6_0_checked, root5Node16Step1Chunk6_1_checked, root5Node16Step1Chunk6_2_checked, root5Node16Step1Chunk6_3_checked, root5Node16Step1Chunk6_4_checked, root5Node16Step1Chunk6_5_checked, root5Node16Step1Chunk7_0_checked, root5Node16Step1Chunk7_1_checked, root5Node16Step1Chunk7_2_checked, root5Node16Step1Chunk7_3_checked, root5Node16Step1Chunk7_4_checked, root5Node16Step1Chunk7_5_checked, root5Node16Step1Chunk8_0_checked, root5Node16Step1Chunk8_1_checked, root5Node16Step1Chunk8_2_checked, root5Node16Step1Chunk8_3_checked, root5Node16Step1Chunk8_4_checked, root5Node16Step1Chunk8_5_checked, Bool.true_and])
theorem root5Node16Step1_checked :
    checkReplacement table25 root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq
    root5Node16Step1Narrowing_checked (by decide)
def root5Node16Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4),(8,4)]
  | 1 => [(0,0),(1,3),(6,3)]
  | 2 => [(7,2),(8,2)]
  | 3 => [(4,0),(5,0),(7,4),(8,0)]
  | 4 => [(1,3),(4,5),(7,3)]
  | 5 => [(4,2),(7,0)]
  | 6 => [(4,1),(8,1)]
  | 7 => [(0,2),(1,5),(6,5)]
  | 8 => [(0,4),(1,1),(6,1)]
  | 9 => [(5,1),(5,4),(8,1)]
  | 10 => [(0,0),(0,1),(6,4),(6,5)]
  | 11 => [(0,4),(1,2),(6,2),(7,2)]
  | 12 => [(1,4),(7,4)]
  | 13 => [(3,3),(5,3),(7,3),(8,3)]
  | 14 => [(5,2),(5,5),(8,5)]
  | 15 => [(7,0),(8,0)]
  | 16 => [(4,3),(8,3)]
  | 17 => [(1,5),(3,5),(5,5),(7,5)]
  | 18 => [(0,3),(1,0),(3,0),(6,1)]
  | 19 => [(2,1),(2,5),(4,1)]
  | 20 => [(0,2),(6,0)]
  | 21 => [(0,1),(1,4),(3,4),(7,4)]
  | 22 => [(0,5),(6,2),(6,3)]
  | 23 => [(4,4),(7,2),(8,4)]
  | 24 => [(1,4),(7,4)]
  | 25 => [(0,5),(6,3)]
  | 26 => [(2,0),(2,2),(2,4),(4,4)]
  | 27 => [(0,0),(1,3),(3,3),(7,3)]
  | 28 => [(3,2),(5,2),(7,2)]
  | 29 => [(4,0),(8,0)]
  | 30 => [(2,1),(2,3),(2,5),(4,1),(4,5),(7,3),(7,5),(8,5)]
  | 31 => [(0,2),(1,0),(6,0)]
  | 32 => [(1,1),(7,1)]
  | 33 => [(4,1),(7,5)]
  | 34 => [(0,2),(6,0)]
  | 35 => [(1,1),(3,1),(7,1)]
  | 36 => [(0,1),(1,5),(6,5)]
  | 37 => [(0,4),(6,1),(6,2)]
  | 38 => [(5,1),(5,4),(8,4)]
  | 39 => [(0,1),(1,4),(6,4),(6,5)]
  | 40 => [(0,0),(1,3),(3,3),(6,3),(6,4),(7,3)]
  | 41 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 42 => [(4,0),(8,0)]
  | 43 => [(7,3)]
  | 44 => [(5,2),(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(1,0),(7,0)]
  | 48 => [(4,3),(7,1),(8,3)]
  | 49 => [(7,5),(8,5)]
  | 50 => [(0,3),(1,0),(6,0),(7,0)]
  | 51 => [(0,3),(0,4),(1,1),(6,1),(6,2)]
  | 52 => [(5,1),(5,4),(8,4)]
  | 53 => [(0,1),(6,4)]
  | 54 => [(1,2),(6,2)]
  | 55 => [(8,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(4,0),(7,4)]
  | 59 => [(1,3),(7,3)]
  | 60 => [(4,2),(7,2),(8,2)]
  | 61 => [(4,3),(5,3),(7,1),(8,3)]
  | 62 => [(7,5),(8,5)]
  | 63 => [(0,3),(1,0)]
  | 64 => [(7,1),(8,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(5,1),(8,1)]
  | 68 => [(0,1),(6,5)]
  | 69 => [(0,4),(6,2)]
  | 70 => [(1,3),(7,3)]
  | 71 => [(4,2),(8,2)]
  | 72 => [(5,0),(5,3)]
  | 73 => [(4,5),(5,5),(8,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(5,5),(8,5)]
  | 77 => [(1,0),(3,0),(7,0)]
  | 78 => [(0,4),(1,2),(6,2)]
  | 79 => [(1,4),(3,4),(5,4),(7,4)]
  | 80 => [(0,0),(0,5),(6,3)]
  | 81 => [(4,4),(7,2)]
  | 82 => [(1,4),(7,4)]
  | 83 => [(0,5),(1,3),(6,3)]
  | 84 => [(4,4),(7,2),(8,2)]
  | 85 => [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 86 => [(0,2),(1,5),(6,0)]
  | 87 => [(1,1),(6,1),(7,1)]
  | 88 => [(4,1),(7,5),(8,1)]
  | 89 => [(0,2),(6,0),(6,5)]
  | _ => [(0,4),(1,1),(7,1)]
def root5Node16Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4),(8,4)]
  | 1 => some [(0,0),(1,3),(6,3)]
  | 2 => some [(7,2),(8,2)]
  | 3 => some [(4,0),(5,0),(7,4),(8,0)]
  | 4 => some [(1,3),(4,5),(7,3)]
  | 5 => some [(4,2),(7,0)]
  | 6 => some [(4,1),(8,1)]
  | 7 => some [(0,2),(1,5),(6,5)]
  | 8 => some [(0,4),(1,1),(6,1)]
  | 9 => some [(5,1),(5,4),(8,1)]
  | 10 => some [(0,0),(0,1),(6,4),(6,5)]
  | 11 => some [(0,4),(1,2),(6,2),(7,2)]
  | 12 => some [(1,4),(7,4)]
  | 13 => some [(3,3),(5,3),(7,3),(8,3)]
  | 14 => some [(5,2),(5,5),(8,5)]
  | 15 => some [(7,0),(8,0)]
  | 16 => some [(4,3),(8,3)]
  | 17 => some [(1,5),(3,5),(5,5),(7,5)]
  | 18 => some [(0,3),(1,0),(3,0),(6,1)]
  | 19 => some [(2,1),(2,5),(4,1)]
  | 20 => some [(0,2),(6,0)]
  | 21 => some [(0,1),(1,4),(3,4),(7,4)]
  | 22 => some [(0,5),(6,2),(6,3)]
  | 23 => some [(4,4),(7,2),(8,4)]
  | 24 => some [(1,4),(7,4)]
  | 25 => some [(0,5),(6,3)]
  | 26 => some [(2,0),(2,2),(2,4),(4,4)]
  | 27 => some [(0,0),(1,3),(3,3),(7,3)]
  | 28 => some [(3,2),(5,2),(7,2)]
  | 29 => some [(4,0),(8,0)]
  | 30 => some [(2,1),(2,3),(2,5),(4,1),(4,5),(7,3),(7,5),(8,5)]
  | 31 => some [(0,2),(1,0),(6,0)]
  | 32 => some [(1,1),(7,1)]
  | 33 => some [(4,1),(7,5)]
  | 34 => some [(0,2),(6,0)]
  | 35 => some [(1,1),(3,1),(7,1)]
  | 36 => some [(0,1),(1,5),(6,5)]
  | 37 => some [(0,4),(6,1),(6,2)]
  | 38 => some [(5,1),(5,4),(8,4)]
  | 39 => some [(0,1),(1,4),(6,4),(6,5)]
  | 40 => some [(0,0),(1,3),(3,3),(6,3),(6,4),(7,3)]
  | 41 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 42 => some [(4,0),(8,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2),(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0),(7,0)]
  | 48 => some [(4,3),(7,1),(8,3)]
  | 49 => some [(7,5),(8,5)]
  | 50 => some [(0,3),(1,0),(6,0),(7,0)]
  | 51 => some [(0,3),(0,4),(1,1),(6,1),(6,2)]
  | 52 => some [(5,1),(5,4),(8,4)]
  | 53 => some [(0,1),(6,4)]
  | 54 => some [(1,2),(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0),(7,4)]
  | 59 => some [(1,3),(7,3)]
  | 60 => some [(4,2),(7,2),(8,2)]
  | 61 => some [(4,3),(5,3),(7,1),(8,3)]
  | 62 => some [(7,5),(8,5)]
  | 63 => some [(0,3),(1,0)]
  | 64 => some [(7,1),(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1),(8,1)]
  | 68 => some [(0,1),(6,5)]
  | 69 => some [(0,4),(6,2)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(4,2),(8,2)]
  | 72 => some [(5,0),(5,3)]
  | 73 => some [(4,5),(5,5),(8,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(1,0),(3,0),(7,0)]
  | 78 => some [(0,4),(1,2),(6,2)]
  | 79 => some [(1,4),(3,4),(5,4),(7,4)]
  | 80 => some [(0,0),(0,5),(6,3)]
  | 81 => some [(4,4),(7,2)]
  | 82 => some [(1,4),(7,4)]
  | 83 => some [(0,5),(1,3),(6,3)]
  | 84 => some [(4,4),(7,2),(8,2)]
  | 85 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 86 => some [(0,2),(1,5),(6,0)]
  | 87 => some [(1,1),(6,1),(7,1)]
  | 88 => some [(4,1),(7,5),(8,1)]
  | 89 => some [(0,2),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root5Node16Domains2_fast_eq : root5Node16Domains2 = expandDomains root5Node16Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node16Domains2 v = expandDomains root5Node16Domains2Fast v from by decide) v
theorem root5Node16Step2Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Narrowing_checked :
    checkNarrowing table65 root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root5Node16Domains1 root5Node16Domains2 (by
      simp only [List.all_cons, List.all_nil, root5Node16Step2Chunk0_0_checked, root5Node16Step2Chunk0_1_checked, root5Node16Step2Chunk0_2_checked, root5Node16Step2Chunk0_3_checked, root5Node16Step2Chunk0_4_checked, root5Node16Step2Chunk0_5_checked, root5Node16Step2Chunk1_0_checked, root5Node16Step2Chunk1_1_checked, root5Node16Step2Chunk1_2_checked, root5Node16Step2Chunk1_3_checked, root5Node16Step2Chunk1_4_checked, root5Node16Step2Chunk1_5_checked, root5Node16Step2Chunk2_0_checked, root5Node16Step2Chunk2_1_checked, root5Node16Step2Chunk2_2_checked, root5Node16Step2Chunk2_3_checked, root5Node16Step2Chunk2_4_checked, root5Node16Step2Chunk2_5_checked, root5Node16Step2Chunk3_0_checked, root5Node16Step2Chunk3_1_checked, root5Node16Step2Chunk3_2_checked, root5Node16Step2Chunk3_3_checked, root5Node16Step2Chunk3_4_checked, root5Node16Step2Chunk3_5_checked, root5Node16Step2Chunk4_0_checked, root5Node16Step2Chunk4_1_checked, root5Node16Step2Chunk4_2_checked, root5Node16Step2Chunk4_3_checked, root5Node16Step2Chunk4_4_checked, root5Node16Step2Chunk4_5_checked, root5Node16Step2Chunk5_0_checked, root5Node16Step2Chunk5_1_checked, root5Node16Step2Chunk5_2_checked, root5Node16Step2Chunk5_3_checked, root5Node16Step2Chunk5_4_checked, root5Node16Step2Chunk5_5_checked, root5Node16Step2Chunk6_0_checked, root5Node16Step2Chunk6_1_checked, root5Node16Step2Chunk6_2_checked, root5Node16Step2Chunk6_3_checked, root5Node16Step2Chunk6_4_checked, root5Node16Step2Chunk6_5_checked, root5Node16Step2Chunk7_0_checked, root5Node16Step2Chunk7_1_checked, root5Node16Step2Chunk7_2_checked, root5Node16Step2Chunk7_3_checked, root5Node16Step2Chunk7_4_checked, root5Node16Step2Chunk7_5_checked, root5Node16Step2Chunk8_0_checked, root5Node16Step2Chunk8_1_checked, root5Node16Step2Chunk8_2_checked, root5Node16Step2Chunk8_3_checked, root5Node16Step2Chunk8_4_checked, root5Node16Step2Chunk8_5_checked, Bool.true_and])
theorem root5Node16Step2_checked :
    checkReplacement table65 root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq
    root5Node16Step2Narrowing_checked (by decide)
def root5Node16Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4),(8,4)]
  | 1 => [(0,0),(1,3),(6,3)]
  | 2 => [(7,2),(8,2)]
  | 3 => [(4,0),(5,0),(7,4),(8,0)]
  | 4 => [(1,3),(4,5),(7,3)]
  | 5 => [(4,2),(7,0)]
  | 6 => [(4,1),(8,1)]
  | 7 => [(0,2),(1,5),(6,5)]
  | 8 => [(0,4),(1,1),(6,1)]
  | 9 => [(5,1),(5,4),(8,1)]
  | 10 => [(0,0),(0,1),(6,4),(6,5)]
  | 11 => [(0,4),(1,2),(6,2),(7,2)]
  | 12 => [(1,4),(7,4)]
  | 13 => [(3,3),(5,3),(7,3),(8,3)]
  | 14 => [(5,2),(5,5),(8,5)]
  | 15 => [(7,0),(8,0)]
  | 16 => [(4,3),(8,3)]
  | 17 => [(1,5),(3,5),(5,5),(7,5)]
  | 18 => [(0,3),(1,0),(3,0),(6,1)]
  | 19 => [(2,1),(2,5),(4,1)]
  | 20 => [(0,2),(6,0)]
  | 21 => [(0,1),(1,4),(3,4),(7,4)]
  | 22 => [(0,5),(6,2),(6,3)]
  | 23 => [(4,4),(7,2),(8,4)]
  | 24 => [(1,4),(7,4)]
  | 25 => [(0,5),(6,3)]
  | 26 => [(2,0),(2,2),(2,4),(4,4)]
  | 27 => [(0,0),(1,3),(3,3),(7,3)]
  | 28 => [(3,2),(5,2),(7,2)]
  | 29 => [(4,0),(8,0)]
  | 30 => [(2,1),(2,3),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 31 => [(0,2),(1,0),(6,0)]
  | 32 => [(1,1),(7,1)]
  | 33 => [(4,1),(7,5)]
  | 34 => [(0,2),(6,0)]
  | 35 => [(1,1),(3,1),(7,1)]
  | 36 => [(0,1),(1,5),(6,5)]
  | 37 => [(0,4),(6,1),(6,2)]
  | 38 => [(5,1),(5,4),(8,4)]
  | 39 => [(0,1),(1,4),(6,4),(6,5)]
  | 40 => [(0,0),(1,3),(3,3),(6,4),(7,3)]
  | 41 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 42 => [(4,0),(8,0)]
  | 43 => [(7,3)]
  | 44 => [(5,2),(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(1,0),(7,0)]
  | 48 => [(4,3),(7,1),(8,3)]
  | 49 => [(7,5),(8,5)]
  | 50 => [(0,3),(1,0),(6,0),(7,0)]
  | 51 => [(0,3),(0,4),(6,1),(6,2)]
  | 52 => [(5,1),(5,4),(8,4)]
  | 53 => [(0,1),(6,4)]
  | 54 => [(1,2),(6,2)]
  | 55 => [(8,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(4,0),(7,4)]
  | 59 => [(1,3),(7,3)]
  | 60 => [(4,2),(7,2),(8,2)]
  | 61 => [(4,3),(5,3),(7,1),(8,3)]
  | 62 => [(7,5),(8,5)]
  | 63 => [(0,3),(1,0)]
  | 64 => [(7,1),(8,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(5,1),(8,1)]
  | 68 => [(0,1),(6,5)]
  | 69 => [(0,4),(6,2)]
  | 70 => [(1,3),(7,3)]
  | 71 => [(4,2),(8,2)]
  | 72 => [(5,0),(5,3)]
  | 73 => [(4,5),(5,5),(8,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(5,5),(8,5)]
  | 77 => [(1,0),(3,0),(7,0)]
  | 78 => [(0,4),(1,2),(6,2)]
  | 79 => [(1,4),(3,4),(5,4),(7,4)]
  | 80 => [(0,0),(0,5),(6,3)]
  | 81 => [(4,4),(7,2)]
  | 82 => [(1,4),(7,4)]
  | 83 => [(0,5),(1,3),(6,3)]
  | 84 => [(4,4),(7,2),(8,2)]
  | 85 => [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 86 => [(0,2),(1,5),(6,0)]
  | 87 => [(1,1),(6,1),(7,1)]
  | 88 => [(4,1),(7,5),(8,1)]
  | 89 => [(0,2),(6,0),(6,5)]
  | _ => [(0,4),(1,1),(7,1)]
def root5Node16Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4),(8,4)]
  | 1 => some [(0,0),(1,3),(6,3)]
  | 2 => some [(7,2),(8,2)]
  | 3 => some [(4,0),(5,0),(7,4),(8,0)]
  | 4 => some [(1,3),(4,5),(7,3)]
  | 5 => some [(4,2),(7,0)]
  | 6 => some [(4,1),(8,1)]
  | 7 => some [(0,2),(1,5),(6,5)]
  | 8 => some [(0,4),(1,1),(6,1)]
  | 9 => some [(5,1),(5,4),(8,1)]
  | 10 => some [(0,0),(0,1),(6,4),(6,5)]
  | 11 => some [(0,4),(1,2),(6,2),(7,2)]
  | 12 => some [(1,4),(7,4)]
  | 13 => some [(3,3),(5,3),(7,3),(8,3)]
  | 14 => some [(5,2),(5,5),(8,5)]
  | 15 => some [(7,0),(8,0)]
  | 16 => some [(4,3),(8,3)]
  | 17 => some [(1,5),(3,5),(5,5),(7,5)]
  | 18 => some [(0,3),(1,0),(3,0),(6,1)]
  | 19 => some [(2,1),(2,5),(4,1)]
  | 20 => some [(0,2),(6,0)]
  | 21 => some [(0,1),(1,4),(3,4),(7,4)]
  | 22 => some [(0,5),(6,2),(6,3)]
  | 23 => some [(4,4),(7,2),(8,4)]
  | 24 => some [(1,4),(7,4)]
  | 25 => some [(0,5),(6,3)]
  | 26 => some [(2,0),(2,2),(2,4),(4,4)]
  | 27 => some [(0,0),(1,3),(3,3),(7,3)]
  | 28 => some [(3,2),(5,2),(7,2)]
  | 29 => some [(4,0),(8,0)]
  | 30 => some [(2,1),(2,3),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 31 => some [(0,2),(1,0),(6,0)]
  | 32 => some [(1,1),(7,1)]
  | 33 => some [(4,1),(7,5)]
  | 34 => some [(0,2),(6,0)]
  | 35 => some [(1,1),(3,1),(7,1)]
  | 36 => some [(0,1),(1,5),(6,5)]
  | 37 => some [(0,4),(6,1),(6,2)]
  | 38 => some [(5,1),(5,4),(8,4)]
  | 39 => some [(0,1),(1,4),(6,4),(6,5)]
  | 40 => some [(0,0),(1,3),(3,3),(6,4),(7,3)]
  | 41 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 42 => some [(4,0),(8,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2),(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0),(7,0)]
  | 48 => some [(4,3),(7,1),(8,3)]
  | 49 => some [(7,5),(8,5)]
  | 50 => some [(0,3),(1,0),(6,0),(7,0)]
  | 51 => some [(0,3),(0,4),(6,1),(6,2)]
  | 52 => some [(5,1),(5,4),(8,4)]
  | 53 => some [(0,1),(6,4)]
  | 54 => some [(1,2),(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0),(7,4)]
  | 59 => some [(1,3),(7,3)]
  | 60 => some [(4,2),(7,2),(8,2)]
  | 61 => some [(4,3),(5,3),(7,1),(8,3)]
  | 62 => some [(7,5),(8,5)]
  | 63 => some [(0,3),(1,0)]
  | 64 => some [(7,1),(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1),(8,1)]
  | 68 => some [(0,1),(6,5)]
  | 69 => some [(0,4),(6,2)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(4,2),(8,2)]
  | 72 => some [(5,0),(5,3)]
  | 73 => some [(4,5),(5,5),(8,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(1,0),(3,0),(7,0)]
  | 78 => some [(0,4),(1,2),(6,2)]
  | 79 => some [(1,4),(3,4),(5,4),(7,4)]
  | 80 => some [(0,0),(0,5),(6,3)]
  | 81 => some [(4,4),(7,2)]
  | 82 => some [(1,4),(7,4)]
  | 83 => some [(0,5),(1,3),(6,3)]
  | 84 => some [(4,4),(7,2),(8,2)]
  | 85 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 86 => some [(0,2),(1,5),(6,0)]
  | 87 => some [(1,1),(6,1),(7,1)]
  | 88 => some [(4,1),(7,5),(8,1)]
  | 89 => some [(0,2),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root5Node16Domains3_fast_eq : root5Node16Domains3 = expandDomains root5Node16Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node16Domains3 v = expandDomains root5Node16Domains3Fast v from by decide) v
theorem root5Node16Step3Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Narrowing_checked :
    checkNarrowing table13 root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_flatten table13Scope [table13Rows0_0,table13Rows0_1,table13Rows0_2,table13Rows0_3,table13Rows0_4,table13Rows0_5,table13Rows1_0,table13Rows1_1,table13Rows1_2,table13Rows1_3,table13Rows1_4,table13Rows1_5,table13Rows2_0,table13Rows2_1,table13Rows2_2,table13Rows2_3,table13Rows2_4,table13Rows2_5,table13Rows3_0,table13Rows3_1,table13Rows3_2,table13Rows3_3,table13Rows3_4,table13Rows3_5,table13Rows4_0,table13Rows4_1,table13Rows4_2,table13Rows4_3,table13Rows4_4,table13Rows4_5,table13Rows5_0,table13Rows5_1,table13Rows5_2,table13Rows5_3,table13Rows5_4,table13Rows5_5,table13Rows6_0,table13Rows6_1,table13Rows6_2,table13Rows6_3,table13Rows6_4,table13Rows6_5,table13Rows7_0,table13Rows7_1,table13Rows7_2,table13Rows7_3,table13Rows7_4,table13Rows7_5,table13Rows8_0,table13Rows8_1,table13Rows8_2,table13Rows8_3,table13Rows8_4,table13Rows8_5]
    root5Node16Domains2 root5Node16Domains3 (by
      simp only [List.all_cons, List.all_nil, root5Node16Step3Chunk0_0_checked, root5Node16Step3Chunk0_1_checked, root5Node16Step3Chunk0_2_checked, root5Node16Step3Chunk0_3_checked, root5Node16Step3Chunk0_4_checked, root5Node16Step3Chunk0_5_checked, root5Node16Step3Chunk1_0_checked, root5Node16Step3Chunk1_1_checked, root5Node16Step3Chunk1_2_checked, root5Node16Step3Chunk1_3_checked, root5Node16Step3Chunk1_4_checked, root5Node16Step3Chunk1_5_checked, root5Node16Step3Chunk2_0_checked, root5Node16Step3Chunk2_1_checked, root5Node16Step3Chunk2_2_checked, root5Node16Step3Chunk2_3_checked, root5Node16Step3Chunk2_4_checked, root5Node16Step3Chunk2_5_checked, root5Node16Step3Chunk3_0_checked, root5Node16Step3Chunk3_1_checked, root5Node16Step3Chunk3_2_checked, root5Node16Step3Chunk3_3_checked, root5Node16Step3Chunk3_4_checked, root5Node16Step3Chunk3_5_checked, root5Node16Step3Chunk4_0_checked, root5Node16Step3Chunk4_1_checked, root5Node16Step3Chunk4_2_checked, root5Node16Step3Chunk4_3_checked, root5Node16Step3Chunk4_4_checked, root5Node16Step3Chunk4_5_checked, root5Node16Step3Chunk5_0_checked, root5Node16Step3Chunk5_1_checked, root5Node16Step3Chunk5_2_checked, root5Node16Step3Chunk5_3_checked, root5Node16Step3Chunk5_4_checked, root5Node16Step3Chunk5_5_checked, root5Node16Step3Chunk6_0_checked, root5Node16Step3Chunk6_1_checked, root5Node16Step3Chunk6_2_checked, root5Node16Step3Chunk6_3_checked, root5Node16Step3Chunk6_4_checked, root5Node16Step3Chunk6_5_checked, root5Node16Step3Chunk7_0_checked, root5Node16Step3Chunk7_1_checked, root5Node16Step3Chunk7_2_checked, root5Node16Step3Chunk7_3_checked, root5Node16Step3Chunk7_4_checked, root5Node16Step3Chunk7_5_checked, root5Node16Step3Chunk8_0_checked, root5Node16Step3Chunk8_1_checked, root5Node16Step3Chunk8_2_checked, root5Node16Step3Chunk8_3_checked, root5Node16Step3Chunk8_4_checked, root5Node16Step3Chunk8_5_checked, Bool.true_and])
theorem root5Node16Step3_checked :
    checkReplacement table13 root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq
    root5Node16Step3Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
