module

public import SpectreFinite.RadiusFiveRoot0Part16
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable2
public import SpectreFinite.RadiusFiveTable4
public import SpectreFinite.RadiusFiveTable51
public import SpectreFinite.RadiusFiveTable8

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node34Domains0 : Domains 91 State := restrict root0Node32Domains2 2 (8,1)
def root0Node34Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(0,1),(6,5)]
  | 4 => some [(0,4),(6,2)]
  | 5 => some [(1,4),(7,4)]
  | 6 => some [(5,2)]
  | 7 => some [(8,0)]
  | 8 => some [(8,3)]
  | 9 => some [(5,5)]
  | 10 => some [(1,0),(3,0)]
  | 11 => some [(2,1),(2,5)]
  | 12 => some [(0,2),(6,0)]
  | 13 => some [(0,4)]
  | 14 => some [(5,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(0,0)]
  | 19 => some [(3,2),(7,2)]
  | 20 => some [(4,0)]
  | 21 => some [(7,0)]
  | 22 => some [(4,3)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(5,1)]
  | 29 => some [(0,1)]
  | 30 => some [(7,2)]
  | 31 => some [(7,4)]
  | 32 => some [(1,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(8,3)]
  | 38 => some [(8,5)]
  | 39 => some [(1,0)]
  | 40 => some [(6,1)]
  | 41 => some [(8,1)]
  | 42 => some [(6,5)]
  | 43 => some [(0,4)]
  | 44 => some [(5,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(6,3)]
  | 49 => some [(7,2)]
  | 50 => some [(4,0)]
  | 51 => some [(8,3)]
  | 52 => some [(5,5)]
  | 53 => some [(7,0)]
  | 54 => some [(4,3)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(4,1)]
  | 58 => some [(0,2)]
  | 59 => some [(1,1)]
  | 60 => some [(5,1)]
  | 61 => some [(0,5)]
  | 62 => some [(4,4)]
  | 63 => some [(1,4)]
  | 64 => some [(0,5)]
  | 65 => some [(2,0)]
  | 66 => some [(7,3)]
  | 67 => some [(5,2)]
  | 68 => some [(8,0)]
  | 69 => some [(8,3)]
  | 70 => some [(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(6,0)]
  | 73 => some [(3,1)]
  | 74 => some [(0,1)]
  | 75 => some [(6,2)]
  | 76 => some [(8,4)]
  | 77 => some [(1,4)]
  | 78 => some [(7,3)]
  | 79 => some [(8,2)]
  | 80 => some [(5,0)]
  | 81 => some [(4,5)]
  | 82 => some [(1,0)]
  | 83 => some [(7,1)]
  | 84 => some [(7,5)]
  | 85 => some [(1,2)]
  | 86 => some [(8,4)]
  | 87 => some [(0,0)]
  | 88 => some [(7,2)]
  | 89 => some [(4,0)]
  | _ => some [(7,3)]
theorem root0Node34Domains0_fast_eq : root0Node34Domains0 = expandDomains root0Node34Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node34Domains0 v = expandDomains root0Node34Domains0Fast v from by decide) v
def root0Node34Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(1,4)]
  | 6 => [(5,2)]
  | 7 => [(8,0)]
  | 8 => [(8,3)]
  | 9 => [(5,5)]
  | 10 => [(3,0)]
  | 11 => [(2,5)]
  | 12 => [(6,0)]
  | 13 => [(0,4)]
  | 14 => [(5,4)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(4,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(4,0)]
  | 21 => [(7,0)]
  | 22 => [(4,3)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(7,1)]
  | 26 => [(1,5)]
  | 27 => [(6,1)]
  | 28 => [(5,1)]
  | 29 => [(0,1)]
  | 30 => [(7,2)]
  | 31 => [(7,4)]
  | 32 => [(1,3)]
  | 33 => [(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(7,0)]
  | 37 => [(8,3)]
  | 38 => [(8,5)]
  | 39 => [(1,0)]
  | 40 => [(6,1)]
  | 41 => [(8,1)]
  | 42 => [(6,5)]
  | 43 => [(0,4)]
  | 44 => [(5,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(7,4)]
  | 48 => [(6,3)]
  | 49 => [(7,2)]
  | 50 => [(4,0)]
  | 51 => [(8,3)]
  | 52 => [(5,5)]
  | 53 => [(7,0)]
  | 54 => [(4,3)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(4,1)]
  | 58 => [(0,2)]
  | 59 => [(1,1)]
  | 60 => [(5,1)]
  | 61 => [(0,5)]
  | 62 => [(4,4)]
  | 63 => [(1,4)]
  | 64 => [(0,5)]
  | 65 => [(2,0)]
  | 66 => [(7,3)]
  | 67 => [(5,2)]
  | 68 => [(8,0)]
  | 69 => [(8,3)]
  | 70 => [(7,1)]
  | 71 => [(7,5)]
  | 72 => [(6,0)]
  | 73 => [(3,1)]
  | 74 => [(0,1)]
  | 75 => [(6,2)]
  | 76 => [(8,4)]
  | 77 => [(1,4)]
  | 78 => [(7,3)]
  | 79 => [(8,2)]
  | 80 => [(5,0)]
  | 81 => [(4,5)]
  | 82 => [(1,0)]
  | 83 => [(7,1)]
  | 84 => [(7,5)]
  | 85 => [(1,2)]
  | 86 => [(8,4)]
  | 87 => [(0,0)]
  | 88 => [(7,2)]
  | 89 => [(4,0)]
  | _ => [(7,3)]
def root0Node34Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(1,4)]
  | 6 => some [(5,2)]
  | 7 => some [(8,0)]
  | 8 => some [(8,3)]
  | 9 => some [(5,5)]
  | 10 => some [(3,0)]
  | 11 => some [(2,5)]
  | 12 => some [(6,0)]
  | 13 => some [(0,4)]
  | 14 => some [(5,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(4,0)]
  | 21 => some [(7,0)]
  | 22 => some [(4,3)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(5,1)]
  | 29 => some [(0,1)]
  | 30 => some [(7,2)]
  | 31 => some [(7,4)]
  | 32 => some [(1,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(8,3)]
  | 38 => some [(8,5)]
  | 39 => some [(1,0)]
  | 40 => some [(6,1)]
  | 41 => some [(8,1)]
  | 42 => some [(6,5)]
  | 43 => some [(0,4)]
  | 44 => some [(5,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(6,3)]
  | 49 => some [(7,2)]
  | 50 => some [(4,0)]
  | 51 => some [(8,3)]
  | 52 => some [(5,5)]
  | 53 => some [(7,0)]
  | 54 => some [(4,3)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(4,1)]
  | 58 => some [(0,2)]
  | 59 => some [(1,1)]
  | 60 => some [(5,1)]
  | 61 => some [(0,5)]
  | 62 => some [(4,4)]
  | 63 => some [(1,4)]
  | 64 => some [(0,5)]
  | 65 => some [(2,0)]
  | 66 => some [(7,3)]
  | 67 => some [(5,2)]
  | 68 => some [(8,0)]
  | 69 => some [(8,3)]
  | 70 => some [(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(6,0)]
  | 73 => some [(3,1)]
  | 74 => some [(0,1)]
  | 75 => some [(6,2)]
  | 76 => some [(8,4)]
  | 77 => some [(1,4)]
  | 78 => some [(7,3)]
  | 79 => some [(8,2)]
  | 80 => some [(5,0)]
  | 81 => some [(4,5)]
  | 82 => some [(1,0)]
  | 83 => some [(7,1)]
  | 84 => some [(7,5)]
  | 85 => some [(1,2)]
  | 86 => some [(8,4)]
  | 87 => some [(0,0)]
  | 88 => some [(7,2)]
  | 89 => some [(4,0)]
  | _ => some [(7,3)]
theorem root0Node34Domains1_fast_eq : root0Node34Domains1 = expandDomains root0Node34Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node34Domains1 v = expandDomains root0Node34Domains1Fast v from by decide) v
theorem root0Node34Step1Chunk0_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_0⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk0_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_1⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk0_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_2⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk0_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_3⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk0_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_4⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk0_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_5⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk1_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_0⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk1_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_1⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk1_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_2⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk1_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_3⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk1_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_4⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk1_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_5⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk2_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_0⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk2_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_1⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk2_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_2⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk2_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_3⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk2_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_4⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk2_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_5⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk3_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_0⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk3_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_1⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk3_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_2⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk3_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_3⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk3_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_4⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk3_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_5⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk4_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_0⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk4_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_1⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk4_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_2⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk4_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_3⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk4_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_4⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk4_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_5⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk5_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_0⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk5_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_1⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk5_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_2⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk5_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_3⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk5_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_4⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk5_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_5⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk6_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_0⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk6_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_1⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk6_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_2⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk6_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_3⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk6_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_4⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk6_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_5⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk7_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_0⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk7_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_1⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk7_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_2⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk7_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_3⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk7_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_4⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk7_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_5⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk8_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_0⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk8_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_1⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk8_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_2⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk8_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_3⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk8_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_4⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Chunk8_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_5⟩
      root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq (by decide)
theorem root0Node34Step1Narrowing_checked :
    checkNarrowing table2 root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkNarrowing_flatten table2Scope [table2Rows0_0,table2Rows0_1,table2Rows0_2,table2Rows0_3,table2Rows0_4,table2Rows0_5,table2Rows1_0,table2Rows1_1,table2Rows1_2,table2Rows1_3,table2Rows1_4,table2Rows1_5,table2Rows2_0,table2Rows2_1,table2Rows2_2,table2Rows2_3,table2Rows2_4,table2Rows2_5,table2Rows3_0,table2Rows3_1,table2Rows3_2,table2Rows3_3,table2Rows3_4,table2Rows3_5,table2Rows4_0,table2Rows4_1,table2Rows4_2,table2Rows4_3,table2Rows4_4,table2Rows4_5,table2Rows5_0,table2Rows5_1,table2Rows5_2,table2Rows5_3,table2Rows5_4,table2Rows5_5,table2Rows6_0,table2Rows6_1,table2Rows6_2,table2Rows6_3,table2Rows6_4,table2Rows6_5,table2Rows7_0,table2Rows7_1,table2Rows7_2,table2Rows7_3,table2Rows7_4,table2Rows7_5,table2Rows8_0,table2Rows8_1,table2Rows8_2,table2Rows8_3,table2Rows8_4,table2Rows8_5]
    root0Node34Domains0 root0Node34Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node34Step1Chunk0_0_checked, root0Node34Step1Chunk0_1_checked, root0Node34Step1Chunk0_2_checked, root0Node34Step1Chunk0_3_checked, root0Node34Step1Chunk0_4_checked, root0Node34Step1Chunk0_5_checked, root0Node34Step1Chunk1_0_checked, root0Node34Step1Chunk1_1_checked, root0Node34Step1Chunk1_2_checked, root0Node34Step1Chunk1_3_checked, root0Node34Step1Chunk1_4_checked, root0Node34Step1Chunk1_5_checked, root0Node34Step1Chunk2_0_checked, root0Node34Step1Chunk2_1_checked, root0Node34Step1Chunk2_2_checked, root0Node34Step1Chunk2_3_checked, root0Node34Step1Chunk2_4_checked, root0Node34Step1Chunk2_5_checked, root0Node34Step1Chunk3_0_checked, root0Node34Step1Chunk3_1_checked, root0Node34Step1Chunk3_2_checked, root0Node34Step1Chunk3_3_checked, root0Node34Step1Chunk3_4_checked, root0Node34Step1Chunk3_5_checked, root0Node34Step1Chunk4_0_checked, root0Node34Step1Chunk4_1_checked, root0Node34Step1Chunk4_2_checked, root0Node34Step1Chunk4_3_checked, root0Node34Step1Chunk4_4_checked, root0Node34Step1Chunk4_5_checked, root0Node34Step1Chunk5_0_checked, root0Node34Step1Chunk5_1_checked, root0Node34Step1Chunk5_2_checked, root0Node34Step1Chunk5_3_checked, root0Node34Step1Chunk5_4_checked, root0Node34Step1Chunk5_5_checked, root0Node34Step1Chunk6_0_checked, root0Node34Step1Chunk6_1_checked, root0Node34Step1Chunk6_2_checked, root0Node34Step1Chunk6_3_checked, root0Node34Step1Chunk6_4_checked, root0Node34Step1Chunk6_5_checked, root0Node34Step1Chunk7_0_checked, root0Node34Step1Chunk7_1_checked, root0Node34Step1Chunk7_2_checked, root0Node34Step1Chunk7_3_checked, root0Node34Step1Chunk7_4_checked, root0Node34Step1Chunk7_5_checked, root0Node34Step1Chunk8_0_checked, root0Node34Step1Chunk8_1_checked, root0Node34Step1Chunk8_2_checked, root0Node34Step1Chunk8_3_checked, root0Node34Step1Chunk8_4_checked, root0Node34Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node34Step1_checked :
    checkReplacement table2 root0Node34Domains0 root0Node34Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node34Domains0 root0Node34Domains1
    root0Node34Domains0Fast root0Node34Domains1Fast
    root0Node34Domains0_fast_eq root0Node34Domains1_fast_eq
    root0Node34Step1Narrowing_checked (by decide)
theorem root0Node34Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node34Domains1 (.output 16) = true := by decide
def root0Node35Domains0 : Domains 91 State := restrict root0Node27Domains4 1 (7,1)
def root0Node35Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(4,1),(5,1),(7,5),(8,1)]
  | 3 => some [(0,1),(0,2),(6,0),(6,5)]
  | 4 => some [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 5 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 6 => some [(1,2),(3,2),(5,2),(7,2)]
  | 7 => some [(4,0),(8,0)]
  | 8 => some [(7,3),(8,3)]
  | 9 => some [(5,2),(5,5),(8,2)]
  | 10 => some [(1,0),(3,0),(5,0)]
  | 11 => some [(2,1),(2,5),(4,5)]
  | 12 => some [(0,2),(1,0),(6,0),(7,0)]
  | 13 => some [(0,3),(0,4),(6,1)]
  | 14 => some [(5,1),(5,4)]
  | 15 => some [(0,1),(1,4)]
  | 16 => some [(0,5),(6,2)]
  | 17 => some [(4,4),(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(3,2),(7,2)]
  | 20 => some [(4,0),(7,4)]
  | 21 => some [(4,2),(7,0)]
  | 22 => some [(4,3),(5,3),(8,3)]
  | 23 => some [(7,5),(8,5)]
  | 24 => some [(1,0),(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(5,1),(8,1)]
  | 29 => some [(0,1),(6,5)]
  | 30 => some [(1,2),(7,2)]
  | 31 => some [(7,4)]
  | 32 => some [(1,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(8,3)]
  | 38 => some [(8,5)]
  | 39 => some [(1,0),(7,0)]
  | 40 => some [(0,3),(1,1),(6,1)]
  | 41 => some [(8,1)]
  | 42 => some [(6,5)]
  | 43 => some [(0,4)]
  | 44 => some [(5,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(6,3)]
  | 49 => some [(7,2)]
  | 50 => some [(4,0),(7,4)]
  | 51 => some [(5,3),(8,3)]
  | 52 => some [(5,5)]
  | 53 => some [(7,0)]
  | 54 => some [(4,3)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(4,1)]
  | 58 => some [(0,2)]
  | 59 => some [(1,1)]
  | 60 => some [(4,1),(5,1),(8,1)]
  | 61 => some [(0,5)]
  | 62 => some [(4,4)]
  | 63 => some [(1,4)]
  | 64 => some [(0,5)]
  | 65 => some [(2,0)]
  | 66 => some [(7,3)]
  | 67 => some [(5,2)]
  | 68 => some [(8,0)]
  | 69 => some [(7,3),(8,3)]
  | 70 => some [(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(6,0)]
  | 73 => some [(3,1)]
  | 74 => some [(0,1)]
  | 75 => some [(6,2)]
  | 76 => some [(8,4)]
  | 77 => some [(1,4),(6,4)]
  | 78 => some [(7,3)]
  | 79 => some [(8,2)]
  | 80 => some [(5,0)]
  | 81 => some [(4,5)]
  | 82 => some [(1,0)]
  | 83 => some [(7,1)]
  | 84 => some [(7,5)]
  | 85 => some [(1,2),(6,2)]
  | 86 => some [(8,4)]
  | 87 => some [(0,0)]
  | 88 => some [(7,2)]
  | 89 => some [(4,0)]
  | _ => some [(7,3)]
theorem root0Node35Domains0_fast_eq : root0Node35Domains0 = expandDomains root0Node35Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node35Domains0 v = expandDomains root0Node35Domains0Fast v from by decide) v
def root0Node35Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(1,0),(6,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(6,0)]
  | 4 => [(3,1),(7,1)]
  | 5 => [(0,1),(1,5),(6,5)]
  | 6 => [(7,2)]
  | 7 => [(4,0)]
  | 8 => [(7,3)]
  | 9 => [(8,2)]
  | 10 => [(5,0)]
  | 11 => [(4,5)]
  | 12 => [(1,0),(7,0)]
  | 13 => [(6,1)]
  | 14 => [(5,1)]
  | 15 => [(0,1)]
  | 16 => [(6,2)]
  | 17 => [(8,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(4,0),(7,4)]
  | 21 => [(7,0)]
  | 22 => [(8,3)]
  | 23 => [(8,5)]
  | 24 => [(1,0)]
  | 25 => [(7,1)]
  | 26 => [(1,5)]
  | 27 => [(6,1)]
  | 28 => [(5,1),(8,1)]
  | 29 => [(0,1),(6,5)]
  | 30 => [(1,2),(7,2)]
  | 31 => [(7,4)]
  | 32 => [(1,3)]
  | 33 => [(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(7,0)]
  | 37 => [(8,3)]
  | 38 => [(8,5)]
  | 39 => [(1,0),(7,0)]
  | 40 => [(0,3),(1,1),(6,1)]
  | 41 => [(8,1)]
  | 42 => [(6,5)]
  | 43 => [(0,4)]
  | 44 => [(5,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(7,4)]
  | 48 => [(6,3)]
  | 49 => [(7,2)]
  | 50 => [(4,0),(7,4)]
  | 51 => [(5,3),(8,3)]
  | 52 => [(5,5)]
  | 53 => [(7,0)]
  | 54 => [(4,3)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(4,1)]
  | 58 => [(0,2)]
  | 59 => [(1,1)]
  | 60 => [(4,1),(5,1),(8,1)]
  | 61 => [(0,5)]
  | 62 => [(4,4)]
  | 63 => [(1,4)]
  | 64 => [(0,5)]
  | 65 => [(2,0)]
  | 66 => [(7,3)]
  | 67 => [(5,2)]
  | 68 => [(8,0)]
  | 69 => [(7,3),(8,3)]
  | 70 => [(7,1)]
  | 71 => [(7,5)]
  | 72 => [(6,0)]
  | 73 => [(3,1)]
  | 74 => [(0,1)]
  | 75 => [(6,2)]
  | 76 => [(8,4)]
  | 77 => [(1,4),(6,4)]
  | 78 => [(7,3)]
  | 79 => [(8,2)]
  | 80 => [(5,0)]
  | 81 => [(4,5)]
  | 82 => [(1,0)]
  | 83 => [(7,1)]
  | 84 => [(7,5)]
  | 85 => [(1,2),(6,2)]
  | 86 => [(8,4)]
  | 87 => [(0,0)]
  | 88 => [(7,2)]
  | 89 => [(4,0)]
  | _ => [(7,3)]
def root0Node35Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0),(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(3,1),(7,1)]
  | 5 => some [(0,1),(1,5),(6,5)]
  | 6 => some [(7,2)]
  | 7 => some [(4,0)]
  | 8 => some [(7,3)]
  | 9 => some [(8,2)]
  | 10 => some [(5,0)]
  | 11 => some [(4,5)]
  | 12 => some [(1,0),(7,0)]
  | 13 => some [(6,1)]
  | 14 => some [(5,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(4,0),(7,4)]
  | 21 => some [(7,0)]
  | 22 => some [(8,3)]
  | 23 => some [(8,5)]
  | 24 => some [(1,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(5,1),(8,1)]
  | 29 => some [(0,1),(6,5)]
  | 30 => some [(1,2),(7,2)]
  | 31 => some [(7,4)]
  | 32 => some [(1,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(8,3)]
  | 38 => some [(8,5)]
  | 39 => some [(1,0),(7,0)]
  | 40 => some [(0,3),(1,1),(6,1)]
  | 41 => some [(8,1)]
  | 42 => some [(6,5)]
  | 43 => some [(0,4)]
  | 44 => some [(5,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(6,3)]
  | 49 => some [(7,2)]
  | 50 => some [(4,0),(7,4)]
  | 51 => some [(5,3),(8,3)]
  | 52 => some [(5,5)]
  | 53 => some [(7,0)]
  | 54 => some [(4,3)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(4,1)]
  | 58 => some [(0,2)]
  | 59 => some [(1,1)]
  | 60 => some [(4,1),(5,1),(8,1)]
  | 61 => some [(0,5)]
  | 62 => some [(4,4)]
  | 63 => some [(1,4)]
  | 64 => some [(0,5)]
  | 65 => some [(2,0)]
  | 66 => some [(7,3)]
  | 67 => some [(5,2)]
  | 68 => some [(8,0)]
  | 69 => some [(7,3),(8,3)]
  | 70 => some [(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(6,0)]
  | 73 => some [(3,1)]
  | 74 => some [(0,1)]
  | 75 => some [(6,2)]
  | 76 => some [(8,4)]
  | 77 => some [(1,4),(6,4)]
  | 78 => some [(7,3)]
  | 79 => some [(8,2)]
  | 80 => some [(5,0)]
  | 81 => some [(4,5)]
  | 82 => some [(1,0)]
  | 83 => some [(7,1)]
  | 84 => some [(7,5)]
  | 85 => some [(1,2),(6,2)]
  | 86 => some [(8,4)]
  | 87 => some [(0,0)]
  | 88 => some [(7,2)]
  | 89 => some [(4,0)]
  | _ => some [(7,3)]
theorem root0Node35Domains1_fast_eq : root0Node35Domains1 = expandDomains root0Node35Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node35Domains1 v = expandDomains root0Node35Domains1Fast v from by decide) v
theorem root0Node35Step1Chunk0_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_0⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk0_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_1⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk0_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_2⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk0_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_3⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk0_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_4⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk0_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_5⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk1_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_0⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk1_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_1⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk1_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_2⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk1_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_3⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk1_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_4⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk1_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_5⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk2_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_0⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk2_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_1⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk2_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_2⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk2_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_3⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk2_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_4⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk2_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_5⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk3_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_0⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk3_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_1⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk3_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_2⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk3_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_3⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk3_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_4⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk3_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_5⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk4_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_0⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk4_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_1⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk4_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_2⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk4_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_3⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk4_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_4⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk4_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_5⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk5_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_0⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk5_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_1⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk5_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_2⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk5_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_3⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk5_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_4⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk5_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_5⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk6_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_0⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk6_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_1⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk6_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_2⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk6_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_3⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk6_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_4⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk6_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_5⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk7_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_0⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk7_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_1⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk7_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_2⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk7_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_3⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk7_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_4⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk7_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_5⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk8_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_0⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk8_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_1⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk8_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_2⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk8_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_3⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk8_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_4⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Chunk8_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_5⟩
      root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq (by decide)
theorem root0Node35Step1Narrowing_checked :
    checkNarrowing table8 root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkNarrowing_flatten table8Scope [table8Rows0_0,table8Rows0_1,table8Rows0_2,table8Rows0_3,table8Rows0_4,table8Rows0_5,table8Rows1_0,table8Rows1_1,table8Rows1_2,table8Rows1_3,table8Rows1_4,table8Rows1_5,table8Rows2_0,table8Rows2_1,table8Rows2_2,table8Rows2_3,table8Rows2_4,table8Rows2_5,table8Rows3_0,table8Rows3_1,table8Rows3_2,table8Rows3_3,table8Rows3_4,table8Rows3_5,table8Rows4_0,table8Rows4_1,table8Rows4_2,table8Rows4_3,table8Rows4_4,table8Rows4_5,table8Rows5_0,table8Rows5_1,table8Rows5_2,table8Rows5_3,table8Rows5_4,table8Rows5_5,table8Rows6_0,table8Rows6_1,table8Rows6_2,table8Rows6_3,table8Rows6_4,table8Rows6_5,table8Rows7_0,table8Rows7_1,table8Rows7_2,table8Rows7_3,table8Rows7_4,table8Rows7_5,table8Rows8_0,table8Rows8_1,table8Rows8_2,table8Rows8_3,table8Rows8_4,table8Rows8_5]
    root0Node35Domains0 root0Node35Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node35Step1Chunk0_0_checked, root0Node35Step1Chunk0_1_checked, root0Node35Step1Chunk0_2_checked, root0Node35Step1Chunk0_3_checked, root0Node35Step1Chunk0_4_checked, root0Node35Step1Chunk0_5_checked, root0Node35Step1Chunk1_0_checked, root0Node35Step1Chunk1_1_checked, root0Node35Step1Chunk1_2_checked, root0Node35Step1Chunk1_3_checked, root0Node35Step1Chunk1_4_checked, root0Node35Step1Chunk1_5_checked, root0Node35Step1Chunk2_0_checked, root0Node35Step1Chunk2_1_checked, root0Node35Step1Chunk2_2_checked, root0Node35Step1Chunk2_3_checked, root0Node35Step1Chunk2_4_checked, root0Node35Step1Chunk2_5_checked, root0Node35Step1Chunk3_0_checked, root0Node35Step1Chunk3_1_checked, root0Node35Step1Chunk3_2_checked, root0Node35Step1Chunk3_3_checked, root0Node35Step1Chunk3_4_checked, root0Node35Step1Chunk3_5_checked, root0Node35Step1Chunk4_0_checked, root0Node35Step1Chunk4_1_checked, root0Node35Step1Chunk4_2_checked, root0Node35Step1Chunk4_3_checked, root0Node35Step1Chunk4_4_checked, root0Node35Step1Chunk4_5_checked, root0Node35Step1Chunk5_0_checked, root0Node35Step1Chunk5_1_checked, root0Node35Step1Chunk5_2_checked, root0Node35Step1Chunk5_3_checked, root0Node35Step1Chunk5_4_checked, root0Node35Step1Chunk5_5_checked, root0Node35Step1Chunk6_0_checked, root0Node35Step1Chunk6_1_checked, root0Node35Step1Chunk6_2_checked, root0Node35Step1Chunk6_3_checked, root0Node35Step1Chunk6_4_checked, root0Node35Step1Chunk6_5_checked, root0Node35Step1Chunk7_0_checked, root0Node35Step1Chunk7_1_checked, root0Node35Step1Chunk7_2_checked, root0Node35Step1Chunk7_3_checked, root0Node35Step1Chunk7_4_checked, root0Node35Step1Chunk7_5_checked, root0Node35Step1Chunk8_0_checked, root0Node35Step1Chunk8_1_checked, root0Node35Step1Chunk8_2_checked, root0Node35Step1Chunk8_3_checked, root0Node35Step1Chunk8_4_checked, root0Node35Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node35Step1_checked :
    checkReplacement table8 root0Node35Domains0 root0Node35Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node35Domains0 root0Node35Domains1
    root0Node35Domains0Fast root0Node35Domains1Fast
    root0Node35Domains0_fast_eq root0Node35Domains1_fast_eq
    root0Node35Step1Narrowing_checked (by decide)
def root0Node35Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(1,0),(6,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(6,0)]
  | 4 => [(3,1),(7,1)]
  | 5 => [(0,1),(1,5),(6,5)]
  | 6 => [(7,2)]
  | 7 => [(4,0)]
  | 8 => [(7,3)]
  | 9 => [(8,2)]
  | 10 => [(5,0)]
  | 11 => [(4,5)]
  | 12 => [(1,0),(7,0)]
  | 13 => [(6,1)]
  | 14 => [(5,1)]
  | 15 => [(0,1)]
  | 16 => [(6,2)]
  | 17 => [(8,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(4,0),(7,4)]
  | 21 => [(7,0)]
  | 22 => [(8,3)]
  | 23 => [(8,5)]
  | 24 => [(1,0)]
  | 25 => [(7,1)]
  | 26 => [(1,5)]
  | 27 => [(6,1)]
  | 28 => [(5,1),(8,1)]
  | 29 => [(0,1),(6,5)]
  | 30 => [(7,2)]
  | 31 => [(7,4)]
  | 32 => [(1,3)]
  | 33 => [(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(7,0)]
  | 37 => [(8,3)]
  | 38 => [(8,5)]
  | 39 => [(1,0),(7,0)]
  | 40 => [(1,1),(6,1)]
  | 41 => [(8,1)]
  | 42 => [(6,5)]
  | 43 => [(0,4)]
  | 44 => [(5,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(7,4)]
  | 48 => [(6,3)]
  | 49 => [(7,2)]
  | 50 => [(4,0),(7,4)]
  | 51 => [(8,3)]
  | 52 => [(5,5)]
  | 53 => [(7,0)]
  | 54 => [(4,3)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(4,1)]
  | 58 => [(0,2)]
  | 59 => [(1,1)]
  | 60 => [(4,1),(5,1),(8,1)]
  | 61 => [(0,5)]
  | 62 => [(4,4)]
  | 63 => [(1,4)]
  | 64 => [(0,5)]
  | 65 => [(2,0)]
  | 66 => [(7,3)]
  | 67 => [(5,2)]
  | 68 => [(8,0)]
  | 69 => [(7,3),(8,3)]
  | 70 => [(7,1)]
  | 71 => [(7,5)]
  | 72 => [(6,0)]
  | 73 => [(3,1)]
  | 74 => [(0,1)]
  | 75 => [(6,2)]
  | 76 => [(8,4)]
  | 77 => [(1,4),(6,4)]
  | 78 => [(7,3)]
  | 79 => [(8,2)]
  | 80 => [(5,0)]
  | 81 => [(4,5)]
  | 82 => [(1,0)]
  | 83 => [(7,1)]
  | 84 => [(7,5)]
  | 85 => [(1,2)]
  | 86 => [(8,4)]
  | 87 => [(0,0)]
  | 88 => [(7,2)]
  | 89 => [(4,0)]
  | _ => [(7,3)]
def root0Node35Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0),(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(3,1),(7,1)]
  | 5 => some [(0,1),(1,5),(6,5)]
  | 6 => some [(7,2)]
  | 7 => some [(4,0)]
  | 8 => some [(7,3)]
  | 9 => some [(8,2)]
  | 10 => some [(5,0)]
  | 11 => some [(4,5)]
  | 12 => some [(1,0),(7,0)]
  | 13 => some [(6,1)]
  | 14 => some [(5,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(4,0),(7,4)]
  | 21 => some [(7,0)]
  | 22 => some [(8,3)]
  | 23 => some [(8,5)]
  | 24 => some [(1,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(5,1),(8,1)]
  | 29 => some [(0,1),(6,5)]
  | 30 => some [(7,2)]
  | 31 => some [(7,4)]
  | 32 => some [(1,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(8,3)]
  | 38 => some [(8,5)]
  | 39 => some [(1,0),(7,0)]
  | 40 => some [(1,1),(6,1)]
  | 41 => some [(8,1)]
  | 42 => some [(6,5)]
  | 43 => some [(0,4)]
  | 44 => some [(5,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(6,3)]
  | 49 => some [(7,2)]
  | 50 => some [(4,0),(7,4)]
  | 51 => some [(8,3)]
  | 52 => some [(5,5)]
  | 53 => some [(7,0)]
  | 54 => some [(4,3)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(4,1)]
  | 58 => some [(0,2)]
  | 59 => some [(1,1)]
  | 60 => some [(4,1),(5,1),(8,1)]
  | 61 => some [(0,5)]
  | 62 => some [(4,4)]
  | 63 => some [(1,4)]
  | 64 => some [(0,5)]
  | 65 => some [(2,0)]
  | 66 => some [(7,3)]
  | 67 => some [(5,2)]
  | 68 => some [(8,0)]
  | 69 => some [(7,3),(8,3)]
  | 70 => some [(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(6,0)]
  | 73 => some [(3,1)]
  | 74 => some [(0,1)]
  | 75 => some [(6,2)]
  | 76 => some [(8,4)]
  | 77 => some [(1,4),(6,4)]
  | 78 => some [(7,3)]
  | 79 => some [(8,2)]
  | 80 => some [(5,0)]
  | 81 => some [(4,5)]
  | 82 => some [(1,0)]
  | 83 => some [(7,1)]
  | 84 => some [(7,5)]
  | 85 => some [(1,2)]
  | 86 => some [(8,4)]
  | 87 => some [(0,0)]
  | 88 => some [(7,2)]
  | 89 => some [(4,0)]
  | _ => some [(7,3)]
theorem root0Node35Domains2_fast_eq : root0Node35Domains2 = expandDomains root0Node35Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node35Domains2 v = expandDomains root0Node35Domains2Fast v from by decide) v
theorem root0Node35Step2Chunk0_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_0⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk0_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_1⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk0_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_2⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk0_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_3⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk0_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_4⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk0_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_5⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk1_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_0⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk1_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_1⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk1_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_2⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk1_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_3⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk1_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_4⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk1_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_5⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk2_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_0⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk2_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_1⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk2_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_2⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk2_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_3⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk2_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_4⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk2_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_5⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk3_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_0⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk3_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_1⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk3_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_2⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk3_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_3⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk3_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_4⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk3_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_5⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk4_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_0⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk4_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_1⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk4_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_2⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk4_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_3⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk4_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_4⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk4_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_5⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk5_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_0⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk5_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_1⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk5_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_2⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk5_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_3⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk5_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_4⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk5_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_5⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk6_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_0⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk6_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_1⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk6_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_2⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk6_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_3⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk6_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_4⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk6_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_5⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk7_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_0⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk7_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_1⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk7_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_2⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk7_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_3⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk7_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_4⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk7_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_5⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk8_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_0⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk8_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_1⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk8_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_2⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk8_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_3⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk8_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_4⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Chunk8_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_5⟩
      root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq (by decide)
theorem root0Node35Step2Narrowing_checked :
    checkNarrowing table51 root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkNarrowing_flatten table51Scope [table51Rows0_0,table51Rows0_1,table51Rows0_2,table51Rows0_3,table51Rows0_4,table51Rows0_5,table51Rows1_0,table51Rows1_1,table51Rows1_2,table51Rows1_3,table51Rows1_4,table51Rows1_5,table51Rows2_0,table51Rows2_1,table51Rows2_2,table51Rows2_3,table51Rows2_4,table51Rows2_5,table51Rows3_0,table51Rows3_1,table51Rows3_2,table51Rows3_3,table51Rows3_4,table51Rows3_5,table51Rows4_0,table51Rows4_1,table51Rows4_2,table51Rows4_3,table51Rows4_4,table51Rows4_5,table51Rows5_0,table51Rows5_1,table51Rows5_2,table51Rows5_3,table51Rows5_4,table51Rows5_5,table51Rows6_0,table51Rows6_1,table51Rows6_2,table51Rows6_3,table51Rows6_4,table51Rows6_5,table51Rows7_0,table51Rows7_1,table51Rows7_2,table51Rows7_3,table51Rows7_4,table51Rows7_5,table51Rows8_0,table51Rows8_1,table51Rows8_2,table51Rows8_3,table51Rows8_4,table51Rows8_5]
    root0Node35Domains1 root0Node35Domains2 (by
      simp only [List.all_cons, List.all_nil, root0Node35Step2Chunk0_0_checked, root0Node35Step2Chunk0_1_checked, root0Node35Step2Chunk0_2_checked, root0Node35Step2Chunk0_3_checked, root0Node35Step2Chunk0_4_checked, root0Node35Step2Chunk0_5_checked, root0Node35Step2Chunk1_0_checked, root0Node35Step2Chunk1_1_checked, root0Node35Step2Chunk1_2_checked, root0Node35Step2Chunk1_3_checked, root0Node35Step2Chunk1_4_checked, root0Node35Step2Chunk1_5_checked, root0Node35Step2Chunk2_0_checked, root0Node35Step2Chunk2_1_checked, root0Node35Step2Chunk2_2_checked, root0Node35Step2Chunk2_3_checked, root0Node35Step2Chunk2_4_checked, root0Node35Step2Chunk2_5_checked, root0Node35Step2Chunk3_0_checked, root0Node35Step2Chunk3_1_checked, root0Node35Step2Chunk3_2_checked, root0Node35Step2Chunk3_3_checked, root0Node35Step2Chunk3_4_checked, root0Node35Step2Chunk3_5_checked, root0Node35Step2Chunk4_0_checked, root0Node35Step2Chunk4_1_checked, root0Node35Step2Chunk4_2_checked, root0Node35Step2Chunk4_3_checked, root0Node35Step2Chunk4_4_checked, root0Node35Step2Chunk4_5_checked, root0Node35Step2Chunk5_0_checked, root0Node35Step2Chunk5_1_checked, root0Node35Step2Chunk5_2_checked, root0Node35Step2Chunk5_3_checked, root0Node35Step2Chunk5_4_checked, root0Node35Step2Chunk5_5_checked, root0Node35Step2Chunk6_0_checked, root0Node35Step2Chunk6_1_checked, root0Node35Step2Chunk6_2_checked, root0Node35Step2Chunk6_3_checked, root0Node35Step2Chunk6_4_checked, root0Node35Step2Chunk6_5_checked, root0Node35Step2Chunk7_0_checked, root0Node35Step2Chunk7_1_checked, root0Node35Step2Chunk7_2_checked, root0Node35Step2Chunk7_3_checked, root0Node35Step2Chunk7_4_checked, root0Node35Step2Chunk7_5_checked, root0Node35Step2Chunk8_0_checked, root0Node35Step2Chunk8_1_checked, root0Node35Step2Chunk8_2_checked, root0Node35Step2Chunk8_3_checked, root0Node35Step2Chunk8_4_checked, root0Node35Step2Chunk8_5_checked, Bool.true_and])
theorem root0Node35Step2_checked :
    checkReplacement table51 root0Node35Domains1 root0Node35Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root0Node35Domains1 root0Node35Domains2
    root0Node35Domains1Fast root0Node35Domains2Fast
    root0Node35Domains1_fast_eq root0Node35Domains2_fast_eq
    root0Node35Step2Narrowing_checked (by decide)
def root0Node36Domains0 : Domains 91 State := restrict root0Node35Domains2 0 (1,0)
def root0Node36Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(3,1),(7,1)]
  | 5 => some [(0,1),(1,5),(6,5)]
  | 6 => some [(7,2)]
  | 7 => some [(4,0)]
  | 8 => some [(7,3)]
  | 9 => some [(8,2)]
  | 10 => some [(5,0)]
  | 11 => some [(4,5)]
  | 12 => some [(1,0),(7,0)]
  | 13 => some [(6,1)]
  | 14 => some [(5,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(4,0),(7,4)]
  | 21 => some [(7,0)]
  | 22 => some [(8,3)]
  | 23 => some [(8,5)]
  | 24 => some [(1,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(5,1),(8,1)]
  | 29 => some [(0,1),(6,5)]
  | 30 => some [(7,2)]
  | 31 => some [(7,4)]
  | 32 => some [(1,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(8,3)]
  | 38 => some [(8,5)]
  | 39 => some [(1,0),(7,0)]
  | 40 => some [(1,1),(6,1)]
  | 41 => some [(8,1)]
  | 42 => some [(6,5)]
  | 43 => some [(0,4)]
  | 44 => some [(5,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(6,3)]
  | 49 => some [(7,2)]
  | 50 => some [(4,0),(7,4)]
  | 51 => some [(8,3)]
  | 52 => some [(5,5)]
  | 53 => some [(7,0)]
  | 54 => some [(4,3)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(4,1)]
  | 58 => some [(0,2)]
  | 59 => some [(1,1)]
  | 60 => some [(4,1),(5,1),(8,1)]
  | 61 => some [(0,5)]
  | 62 => some [(4,4)]
  | 63 => some [(1,4)]
  | 64 => some [(0,5)]
  | 65 => some [(2,0)]
  | 66 => some [(7,3)]
  | 67 => some [(5,2)]
  | 68 => some [(8,0)]
  | 69 => some [(7,3),(8,3)]
  | 70 => some [(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(6,0)]
  | 73 => some [(3,1)]
  | 74 => some [(0,1)]
  | 75 => some [(6,2)]
  | 76 => some [(8,4)]
  | 77 => some [(1,4),(6,4)]
  | 78 => some [(7,3)]
  | 79 => some [(8,2)]
  | 80 => some [(5,0)]
  | 81 => some [(4,5)]
  | 82 => some [(1,0)]
  | 83 => some [(7,1)]
  | 84 => some [(7,5)]
  | 85 => some [(1,2)]
  | 86 => some [(8,4)]
  | 87 => some [(0,0)]
  | 88 => some [(7,2)]
  | 89 => some [(4,0)]
  | _ => some [(7,3)]
theorem root0Node36Domains0_fast_eq : root0Node36Domains0 = expandDomains root0Node36Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node36Domains0 v = expandDomains root0Node36Domains0Fast v from by decide) v
def root0Node36Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(1,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(6,0)]
  | 4 => [(7,1)]
  | 5 => [(1,5)]
  | 6 => [(7,2)]
  | 7 => [(4,0)]
  | 8 => [(7,3)]
  | 9 => [(8,2)]
  | 10 => [(5,0)]
  | 11 => [(4,5)]
  | 12 => [(7,0)]
  | 13 => [(6,1)]
  | 14 => [(5,1)]
  | 15 => [(0,1)]
  | 16 => [(6,2)]
  | 17 => [(8,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(7,4)]
  | 21 => [(7,0)]
  | 22 => [(8,3)]
  | 23 => [(8,5)]
  | 24 => [(1,0)]
  | 25 => [(7,1)]
  | 26 => [(1,5)]
  | 27 => [(6,1)]
  | 28 => [(8,1)]
  | 29 => [(6,5)]
  | 30 => [(7,2)]
  | 31 => [(7,4)]
  | 32 => [(1,3)]
  | 33 => [(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(7,0)]
  | 37 => [(8,3)]
  | 38 => [(8,5)]
  | 39 => [(1,0),(7,0)]
  | 40 => [(1,1),(6,1)]
  | 41 => [(8,1)]
  | 42 => [(6,5)]
  | 43 => [(0,4)]
  | 44 => [(5,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(7,4)]
  | 48 => [(6,3)]
  | 49 => [(7,2)]
  | 50 => [(4,0),(7,4)]
  | 51 => [(8,3)]
  | 52 => [(5,5)]
  | 53 => [(7,0)]
  | 54 => [(4,3)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(4,1)]
  | 58 => [(0,2)]
  | 59 => [(1,1)]
  | 60 => [(4,1),(5,1),(8,1)]
  | 61 => [(0,5)]
  | 62 => [(4,4)]
  | 63 => [(1,4)]
  | 64 => [(0,5)]
  | 65 => [(2,0)]
  | 66 => [(7,3)]
  | 67 => [(5,2)]
  | 68 => [(8,0)]
  | 69 => [(7,3),(8,3)]
  | 70 => [(7,1)]
  | 71 => [(7,5)]
  | 72 => [(6,0)]
  | 73 => [(3,1)]
  | 74 => [(0,1)]
  | 75 => [(6,2)]
  | 76 => [(8,4)]
  | 77 => [(1,4),(6,4)]
  | 78 => [(7,3)]
  | 79 => [(8,2)]
  | 80 => [(5,0)]
  | 81 => [(4,5)]
  | 82 => [(1,0)]
  | 83 => [(7,1)]
  | 84 => [(7,5)]
  | 85 => [(1,2)]
  | 86 => [(8,4)]
  | 87 => [(0,0)]
  | 88 => [(7,2)]
  | 89 => [(4,0)]
  | _ => [(7,3)]
def root0Node36Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,1)]
  | 5 => some [(1,5)]
  | 6 => some [(7,2)]
  | 7 => some [(4,0)]
  | 8 => some [(7,3)]
  | 9 => some [(8,2)]
  | 10 => some [(5,0)]
  | 11 => some [(4,5)]
  | 12 => some [(7,0)]
  | 13 => some [(6,1)]
  | 14 => some [(5,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(7,0)]
  | 22 => some [(8,3)]
  | 23 => some [(8,5)]
  | 24 => some [(1,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(8,1)]
  | 29 => some [(6,5)]
  | 30 => some [(7,2)]
  | 31 => some [(7,4)]
  | 32 => some [(1,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(8,3)]
  | 38 => some [(8,5)]
  | 39 => some [(1,0),(7,0)]
  | 40 => some [(1,1),(6,1)]
  | 41 => some [(8,1)]
  | 42 => some [(6,5)]
  | 43 => some [(0,4)]
  | 44 => some [(5,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(6,3)]
  | 49 => some [(7,2)]
  | 50 => some [(4,0),(7,4)]
  | 51 => some [(8,3)]
  | 52 => some [(5,5)]
  | 53 => some [(7,0)]
  | 54 => some [(4,3)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(4,1)]
  | 58 => some [(0,2)]
  | 59 => some [(1,1)]
  | 60 => some [(4,1),(5,1),(8,1)]
  | 61 => some [(0,5)]
  | 62 => some [(4,4)]
  | 63 => some [(1,4)]
  | 64 => some [(0,5)]
  | 65 => some [(2,0)]
  | 66 => some [(7,3)]
  | 67 => some [(5,2)]
  | 68 => some [(8,0)]
  | 69 => some [(7,3),(8,3)]
  | 70 => some [(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(6,0)]
  | 73 => some [(3,1)]
  | 74 => some [(0,1)]
  | 75 => some [(6,2)]
  | 76 => some [(8,4)]
  | 77 => some [(1,4),(6,4)]
  | 78 => some [(7,3)]
  | 79 => some [(8,2)]
  | 80 => some [(5,0)]
  | 81 => some [(4,5)]
  | 82 => some [(1,0)]
  | 83 => some [(7,1)]
  | 84 => some [(7,5)]
  | 85 => some [(1,2)]
  | 86 => some [(8,4)]
  | 87 => some [(0,0)]
  | 88 => some [(7,2)]
  | 89 => some [(4,0)]
  | _ => some [(7,3)]
theorem root0Node36Domains1_fast_eq : root0Node36Domains1 = expandDomains root0Node36Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node36Domains1 v = expandDomains root0Node36Domains1Fast v from by decide) v
theorem root0Node36Step1Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq (by decide)
theorem root0Node36Step1Narrowing_checked :
    checkNarrowing table4 root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkNarrowing_flatten table4Scope [table4Rows0_0,table4Rows0_1,table4Rows0_2,table4Rows0_3,table4Rows0_4,table4Rows0_5,table4Rows1_0,table4Rows1_1,table4Rows1_2,table4Rows1_3,table4Rows1_4,table4Rows1_5,table4Rows2_0,table4Rows2_1,table4Rows2_2,table4Rows2_3,table4Rows2_4,table4Rows2_5,table4Rows3_0,table4Rows3_1,table4Rows3_2,table4Rows3_3,table4Rows3_4,table4Rows3_5,table4Rows4_0,table4Rows4_1,table4Rows4_2,table4Rows4_3,table4Rows4_4,table4Rows4_5,table4Rows5_0,table4Rows5_1,table4Rows5_2,table4Rows5_3,table4Rows5_4,table4Rows5_5,table4Rows6_0,table4Rows6_1,table4Rows6_2,table4Rows6_3,table4Rows6_4,table4Rows6_5,table4Rows7_0,table4Rows7_1,table4Rows7_2,table4Rows7_3,table4Rows7_4,table4Rows7_5,table4Rows8_0,table4Rows8_1,table4Rows8_2,table4Rows8_3,table4Rows8_4,table4Rows8_5]
    root0Node36Domains0 root0Node36Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node36Step1Chunk0_0_checked, root0Node36Step1Chunk0_1_checked, root0Node36Step1Chunk0_2_checked, root0Node36Step1Chunk0_3_checked, root0Node36Step1Chunk0_4_checked, root0Node36Step1Chunk0_5_checked, root0Node36Step1Chunk1_0_checked, root0Node36Step1Chunk1_1_checked, root0Node36Step1Chunk1_2_checked, root0Node36Step1Chunk1_3_checked, root0Node36Step1Chunk1_4_checked, root0Node36Step1Chunk1_5_checked, root0Node36Step1Chunk2_0_checked, root0Node36Step1Chunk2_1_checked, root0Node36Step1Chunk2_2_checked, root0Node36Step1Chunk2_3_checked, root0Node36Step1Chunk2_4_checked, root0Node36Step1Chunk2_5_checked, root0Node36Step1Chunk3_0_checked, root0Node36Step1Chunk3_1_checked, root0Node36Step1Chunk3_2_checked, root0Node36Step1Chunk3_3_checked, root0Node36Step1Chunk3_4_checked, root0Node36Step1Chunk3_5_checked, root0Node36Step1Chunk4_0_checked, root0Node36Step1Chunk4_1_checked, root0Node36Step1Chunk4_2_checked, root0Node36Step1Chunk4_3_checked, root0Node36Step1Chunk4_4_checked, root0Node36Step1Chunk4_5_checked, root0Node36Step1Chunk5_0_checked, root0Node36Step1Chunk5_1_checked, root0Node36Step1Chunk5_2_checked, root0Node36Step1Chunk5_3_checked, root0Node36Step1Chunk5_4_checked, root0Node36Step1Chunk5_5_checked, root0Node36Step1Chunk6_0_checked, root0Node36Step1Chunk6_1_checked, root0Node36Step1Chunk6_2_checked, root0Node36Step1Chunk6_3_checked, root0Node36Step1Chunk6_4_checked, root0Node36Step1Chunk6_5_checked, root0Node36Step1Chunk7_0_checked, root0Node36Step1Chunk7_1_checked, root0Node36Step1Chunk7_2_checked, root0Node36Step1Chunk7_3_checked, root0Node36Step1Chunk7_4_checked, root0Node36Step1Chunk7_5_checked, root0Node36Step1Chunk8_0_checked, root0Node36Step1Chunk8_1_checked, root0Node36Step1Chunk8_2_checked, root0Node36Step1Chunk8_3_checked, root0Node36Step1Chunk8_4_checked, root0Node36Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node36Step1_checked :
    checkReplacement table4 root0Node36Domains0 root0Node36Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node36Domains0 root0Node36Domains1
    root0Node36Domains0Fast root0Node36Domains1Fast
    root0Node36Domains0_fast_eq root0Node36Domains1_fast_eq
    root0Node36Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
