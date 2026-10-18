module

public import SpectreFinite.RadiusFiveRoot1Part44
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable1
public import SpectreFinite.RadiusFiveTable32
public import SpectreFinite.RadiusFiveTable51
public import SpectreFinite.RadiusFiveTable65

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node109Domains0 : Domains 91 State := restrict root1Node107Domains2 78 (6,2)
def root1Node109Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(5,2)]
  | 6 => some [(5,1)]
  | 7 => some [(0,1)]
  | 8 => some [(6,2)]
  | 9 => some [(8,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(8,4)]
  | 13 => some [(8,3)]
  | 14 => some [(8,5)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3)]
  | 19 => some [(8,1)]
  | 20 => some [(1,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(4,2)]
  | 27 => some [(5,3)]
  | 28 => some [(8,5)]
  | 29 => some [(7,0)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(7,3)]
  | 41 => some [(5,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(1,0)]
  | 46 => some [(2,1)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(6,2)]
  | 52 => some [(8,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(0,0)]
  | 57 => some [(3,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(5,2)]
  | 61 => some [(7,1)]
  | 62 => some [(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(7,3)]
  | 71 => some [(8,2)]
  | 72 => some [(5,0)]
  | 73 => some [(4,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(8,5)]
  | 77 => some [(1,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(0,0)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(1,3)]
  | 84 => some [(8,2)]
  | 85 => some [(7,1),(8,1)]
  | 86 => some [(1,5)]
  | 87 => some [(6,1)]
  | 88 => some [(8,1)]
  | 89 => some [(6,5)]
  | _ => some [(0,4)]
theorem root1Node109Domains0_fast_eq : root1Node109Domains0 = expandDomains root1Node109Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node109Domains0 v = expandDomains root1Node109Domains0Fast v from by decide) v
def root1Node109Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3)]
  | 5 => [(5,2)]
  | 6 => [(5,1)]
  | 7 => [(0,1)]
  | 8 => [(6,2)]
  | 9 => [(8,4)]
  | 10 => [(6,4)]
  | 11 => [(1,2)]
  | 12 => [(8,4)]
  | 13 => [(8,3)]
  | 14 => [(8,5)]
  | 15 => [(1,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(0,3)]
  | 19 => [(8,1)]
  | 20 => [(1,5)]
  | 21 => [(7,4)]
  | 22 => [(6,3)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(4,2)]
  | 27 => [(5,3)]
  | 28 => [(8,5)]
  | 29 => [(7,0)]
  | 30 => [(4,1)]
  | 31 => [(0,2)]
  | 32 => [(1,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(7,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(7,3)]
  | 41 => [(5,2)]
  | 42 => [(8,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5)]
  | 45 => [(1,0)]
  | 46 => [(2,1)]
  | 47 => [(0,2)]
  | 48 => [(1,1)]
  | 49 => [(4,1)]
  | 50 => [(0,2)]
  | 51 => [(6,2)]
  | 52 => [(8,4)]
  | 53 => [(1,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(0,0)]
  | 57 => [(3,2)]
  | 58 => [(4,0)]
  | 59 => [(7,3)]
  | 60 => [(5,2)]
  | 61 => [(7,1)]
  | 62 => [(7,5)]
  | 63 => [(6,0)]
  | 64 => [(7,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(5,1)]
  | 68 => [(0,1)]
  | 69 => [(6,2)]
  | 70 => [(7,3)]
  | 71 => [(8,2)]
  | 72 => [(5,0)]
  | 73 => [(4,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(8,5)]
  | 77 => [(1,0)]
  | 78 => [(6,2)]
  | 79 => [(8,4)]
  | 80 => [(0,0)]
  | 81 => [(7,2)]
  | 82 => [(7,4)]
  | 83 => [(1,3)]
  | 84 => [(8,2)]
  | 85 => [(7,1)]
  | 86 => [(1,5)]
  | 87 => [(6,1)]
  | 88 => [(8,1)]
  | 89 => [(6,5)]
  | _ => [(0,4)]
def root1Node109Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(5,2)]
  | 6 => some [(5,1)]
  | 7 => some [(0,1)]
  | 8 => some [(6,2)]
  | 9 => some [(8,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(8,4)]
  | 13 => some [(8,3)]
  | 14 => some [(8,5)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3)]
  | 19 => some [(8,1)]
  | 20 => some [(1,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(4,2)]
  | 27 => some [(5,3)]
  | 28 => some [(8,5)]
  | 29 => some [(7,0)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(7,3)]
  | 41 => some [(5,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(1,0)]
  | 46 => some [(2,1)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(6,2)]
  | 52 => some [(8,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(0,0)]
  | 57 => some [(3,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(5,2)]
  | 61 => some [(7,1)]
  | 62 => some [(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(7,3)]
  | 71 => some [(8,2)]
  | 72 => some [(5,0)]
  | 73 => some [(4,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(8,5)]
  | 77 => some [(1,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(0,0)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(1,3)]
  | 84 => some [(8,2)]
  | 85 => some [(7,1)]
  | 86 => some [(1,5)]
  | 87 => some [(6,1)]
  | 88 => some [(8,1)]
  | 89 => some [(6,5)]
  | _ => some [(0,4)]
theorem root1Node109Domains1_fast_eq : root1Node109Domains1 = expandDomains root1Node109Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node109Domains1 v = expandDomains root1Node109Domains1Fast v from by decide) v
theorem root1Node109Step1Chunk0_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_0⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk0_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_1⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk0_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_2⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk0_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_3⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk0_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_4⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk0_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_5⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk1_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_0⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk1_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_1⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk1_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_2⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk1_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_3⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk1_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_4⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk1_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_5⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk2_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_0⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk2_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_1⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk2_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_2⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk2_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_3⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk2_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_4⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk2_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_5⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk3_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_0⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk3_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_1⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk3_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_2⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk3_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_3⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk3_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_4⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk3_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_5⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk4_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_0⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk4_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_1⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk4_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_2⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk4_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_3⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk4_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_4⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk4_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_5⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk5_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_0⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk5_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_1⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk5_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_2⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk5_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_3⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk5_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_4⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk5_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_5⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk6_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_0⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk6_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_1⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk6_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_2⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk6_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_3⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk6_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_4⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk6_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_5⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk7_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_0⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk7_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_1⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk7_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_2⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk7_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_3⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk7_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_4⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk7_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_5⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk8_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_0⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk8_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_1⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk8_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_2⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk8_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_3⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk8_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_4⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Chunk8_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_5⟩
      root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq (by decide)
theorem root1Node109Step1Narrowing_checked :
    checkNarrowing table51 root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkNarrowing_flatten table51Scope [table51Rows0_0,table51Rows0_1,table51Rows0_2,table51Rows0_3,table51Rows0_4,table51Rows0_5,table51Rows1_0,table51Rows1_1,table51Rows1_2,table51Rows1_3,table51Rows1_4,table51Rows1_5,table51Rows2_0,table51Rows2_1,table51Rows2_2,table51Rows2_3,table51Rows2_4,table51Rows2_5,table51Rows3_0,table51Rows3_1,table51Rows3_2,table51Rows3_3,table51Rows3_4,table51Rows3_5,table51Rows4_0,table51Rows4_1,table51Rows4_2,table51Rows4_3,table51Rows4_4,table51Rows4_5,table51Rows5_0,table51Rows5_1,table51Rows5_2,table51Rows5_3,table51Rows5_4,table51Rows5_5,table51Rows6_0,table51Rows6_1,table51Rows6_2,table51Rows6_3,table51Rows6_4,table51Rows6_5,table51Rows7_0,table51Rows7_1,table51Rows7_2,table51Rows7_3,table51Rows7_4,table51Rows7_5,table51Rows8_0,table51Rows8_1,table51Rows8_2,table51Rows8_3,table51Rows8_4,table51Rows8_5]
    root1Node109Domains0 root1Node109Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node109Step1Chunk0_0_checked, root1Node109Step1Chunk0_1_checked, root1Node109Step1Chunk0_2_checked, root1Node109Step1Chunk0_3_checked, root1Node109Step1Chunk0_4_checked, root1Node109Step1Chunk0_5_checked, root1Node109Step1Chunk1_0_checked, root1Node109Step1Chunk1_1_checked, root1Node109Step1Chunk1_2_checked, root1Node109Step1Chunk1_3_checked, root1Node109Step1Chunk1_4_checked, root1Node109Step1Chunk1_5_checked, root1Node109Step1Chunk2_0_checked, root1Node109Step1Chunk2_1_checked, root1Node109Step1Chunk2_2_checked, root1Node109Step1Chunk2_3_checked, root1Node109Step1Chunk2_4_checked, root1Node109Step1Chunk2_5_checked, root1Node109Step1Chunk3_0_checked, root1Node109Step1Chunk3_1_checked, root1Node109Step1Chunk3_2_checked, root1Node109Step1Chunk3_3_checked, root1Node109Step1Chunk3_4_checked, root1Node109Step1Chunk3_5_checked, root1Node109Step1Chunk4_0_checked, root1Node109Step1Chunk4_1_checked, root1Node109Step1Chunk4_2_checked, root1Node109Step1Chunk4_3_checked, root1Node109Step1Chunk4_4_checked, root1Node109Step1Chunk4_5_checked, root1Node109Step1Chunk5_0_checked, root1Node109Step1Chunk5_1_checked, root1Node109Step1Chunk5_2_checked, root1Node109Step1Chunk5_3_checked, root1Node109Step1Chunk5_4_checked, root1Node109Step1Chunk5_5_checked, root1Node109Step1Chunk6_0_checked, root1Node109Step1Chunk6_1_checked, root1Node109Step1Chunk6_2_checked, root1Node109Step1Chunk6_3_checked, root1Node109Step1Chunk6_4_checked, root1Node109Step1Chunk6_5_checked, root1Node109Step1Chunk7_0_checked, root1Node109Step1Chunk7_1_checked, root1Node109Step1Chunk7_2_checked, root1Node109Step1Chunk7_3_checked, root1Node109Step1Chunk7_4_checked, root1Node109Step1Chunk7_5_checked, root1Node109Step1Chunk8_0_checked, root1Node109Step1Chunk8_1_checked, root1Node109Step1Chunk8_2_checked, root1Node109Step1Chunk8_3_checked, root1Node109Step1Chunk8_4_checked, root1Node109Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node109Step1_checked :
    checkReplacement table51 root1Node109Domains0 root1Node109Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node109Domains0 root1Node109Domains1
    root1Node109Domains0Fast root1Node109Domains1Fast
    root1Node109Domains0_fast_eq root1Node109Domains1_fast_eq
    root1Node109Step1Narrowing_checked (by decide)
theorem root1Node109Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node109Domains1 (.output 54) = true := by decide
def root1Node110Domains0 : Domains 91 State := restrict root1Node102Domains4 2 (8,2)
def root1Node110Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(4,2),(5,2),(8,2)]
  | 6 => some [(5,1)]
  | 7 => some [(0,1)]
  | 8 => some [(6,2)]
  | 9 => some [(8,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(7,4),(8,4)]
  | 13 => some [(5,3),(8,3)]
  | 14 => some [(8,5)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3)]
  | 19 => some [(8,1)]
  | 20 => some [(1,5),(6,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(4,2)]
  | 27 => some [(5,3)]
  | 28 => some [(8,5)]
  | 29 => some [(7,0)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3),(3,3),(7,3)]
  | 41 => some [(5,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(1,0)]
  | 46 => some [(2,1)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,4),(6,2)]
  | 52 => some [(5,4),(8,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(0,0)]
  | 57 => some [(3,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(5,2)]
  | 61 => some [(4,3),(7,1)]
  | 62 => some [(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(8,2)]
  | 72 => some [(5,0)]
  | 73 => some [(4,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(8,5)]
  | 77 => some [(1,0)]
  | 78 => some [(0,4),(1,2),(6,2)]
  | 79 => some [(5,4),(8,4)]
  | 80 => some [(0,0)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(1,3),(6,3)]
  | 84 => some [(7,2),(8,2)]
  | 85 => some [(4,3),(7,1),(8,1)]
  | 86 => some [(1,5)]
  | 87 => some [(6,1)]
  | 88 => some [(4,1),(8,1)]
  | 89 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root1Node110Domains0_fast_eq : root1Node110Domains0 = expandDomains root1Node110Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node110Domains0 v = expandDomains root1Node110Domains0Fast v from by decide) v
def root1Node110Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(8,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3)]
  | 5 => [(4,2),(5,2),(8,2)]
  | 6 => [(5,1)]
  | 7 => [(0,1)]
  | 8 => [(6,2)]
  | 9 => [(8,4)]
  | 10 => [(6,4)]
  | 11 => [(1,2)]
  | 12 => [(7,4),(8,4)]
  | 13 => [(8,3)]
  | 14 => [(8,5)]
  | 15 => [(1,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(0,3)]
  | 19 => [(8,1)]
  | 20 => [(1,5),(6,5)]
  | 21 => [(7,4)]
  | 22 => [(6,3)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(4,2)]
  | 27 => [(5,3)]
  | 28 => [(8,5)]
  | 29 => [(7,0)]
  | 30 => [(4,1)]
  | 31 => [(0,2)]
  | 32 => [(1,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(7,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(7,3)]
  | 41 => [(5,2)]
  | 42 => [(8,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5)]
  | 45 => [(1,0)]
  | 46 => [(2,1)]
  | 47 => [(0,2)]
  | 48 => [(1,1)]
  | 49 => [(4,1)]
  | 50 => [(0,2)]
  | 51 => [(6,2)]
  | 52 => [(8,4)]
  | 53 => [(1,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(0,0)]
  | 57 => [(3,2)]
  | 58 => [(4,0)]
  | 59 => [(7,3)]
  | 60 => [(5,2)]
  | 61 => [(7,1)]
  | 62 => [(7,5)]
  | 63 => [(6,0)]
  | 64 => [(7,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(5,1)]
  | 68 => [(0,1)]
  | 69 => [(6,2)]
  | 70 => [(7,3)]
  | 71 => [(8,2)]
  | 72 => [(5,0)]
  | 73 => [(4,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(8,5)]
  | 77 => [(1,0)]
  | 78 => [(0,4),(1,2),(6,2)]
  | 79 => [(5,4),(8,4)]
  | 80 => [(0,0)]
  | 81 => [(7,2)]
  | 82 => [(7,4)]
  | 83 => [(1,3),(6,3)]
  | 84 => [(7,2),(8,2)]
  | 85 => [(4,3),(7,1),(8,1)]
  | 86 => [(1,5)]
  | 87 => [(6,1)]
  | 88 => [(4,1),(8,1)]
  | 89 => [(0,2),(6,5)]
  | _ => [(0,4),(1,1)]
def root1Node110Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(4,2),(5,2),(8,2)]
  | 6 => some [(5,1)]
  | 7 => some [(0,1)]
  | 8 => some [(6,2)]
  | 9 => some [(8,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(7,4),(8,4)]
  | 13 => some [(8,3)]
  | 14 => some [(8,5)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3)]
  | 19 => some [(8,1)]
  | 20 => some [(1,5),(6,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(4,2)]
  | 27 => some [(5,3)]
  | 28 => some [(8,5)]
  | 29 => some [(7,0)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(7,3)]
  | 41 => some [(5,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(1,0)]
  | 46 => some [(2,1)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(6,2)]
  | 52 => some [(8,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(0,0)]
  | 57 => some [(3,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(5,2)]
  | 61 => some [(7,1)]
  | 62 => some [(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(7,3)]
  | 71 => some [(8,2)]
  | 72 => some [(5,0)]
  | 73 => some [(4,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(8,5)]
  | 77 => some [(1,0)]
  | 78 => some [(0,4),(1,2),(6,2)]
  | 79 => some [(5,4),(8,4)]
  | 80 => some [(0,0)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(1,3),(6,3)]
  | 84 => some [(7,2),(8,2)]
  | 85 => some [(4,3),(7,1),(8,1)]
  | 86 => some [(1,5)]
  | 87 => some [(6,1)]
  | 88 => some [(4,1),(8,1)]
  | 89 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root1Node110Domains1_fast_eq : root1Node110Domains1 = expandDomains root1Node110Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node110Domains1 v = expandDomains root1Node110Domains1Fast v from by decide) v
theorem root1Node110Step1Chunk0_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows0_0⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk0_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows0_1⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk0_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows0_2⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk0_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows0_3⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk0_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows0_4⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk0_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows0_5⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk1_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows1_0⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk1_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows1_1⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk1_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows1_2⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk1_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows1_3⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk1_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows1_4⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk1_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows1_5⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk2_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows2_0⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk2_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows2_1⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk2_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows2_2⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk2_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows2_3⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk2_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows2_4⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk2_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows2_5⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk3_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows3_0⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk3_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows3_1⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk3_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows3_2⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk3_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows3_3⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk3_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows3_4⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk3_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows3_5⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk4_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows4_0⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk4_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows4_1⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk4_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows4_2⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk4_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows4_3⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk4_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows4_4⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk4_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows4_5⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk5_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows5_0⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk5_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows5_1⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk5_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows5_2⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk5_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows5_3⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk5_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows5_4⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk5_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows5_5⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk6_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows6_0⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk6_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows6_1⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk6_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows6_2⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk6_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows6_3⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk6_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows6_4⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk6_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows6_5⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk7_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows7_0⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk7_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows7_1⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk7_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows7_2⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk7_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows7_3⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk7_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows7_4⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk7_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows7_5⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk8_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows8_0⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk8_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows8_1⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk8_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows8_2⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk8_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows8_3⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk8_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows8_4⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Chunk8_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows8_5⟩
      root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq (by decide)
theorem root1Node110Step1Narrowing_checked :
    checkNarrowing table32 root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkNarrowing_flatten table32Scope [table32Rows0_0,table32Rows0_1,table32Rows0_2,table32Rows0_3,table32Rows0_4,table32Rows0_5,table32Rows1_0,table32Rows1_1,table32Rows1_2,table32Rows1_3,table32Rows1_4,table32Rows1_5,table32Rows2_0,table32Rows2_1,table32Rows2_2,table32Rows2_3,table32Rows2_4,table32Rows2_5,table32Rows3_0,table32Rows3_1,table32Rows3_2,table32Rows3_3,table32Rows3_4,table32Rows3_5,table32Rows4_0,table32Rows4_1,table32Rows4_2,table32Rows4_3,table32Rows4_4,table32Rows4_5,table32Rows5_0,table32Rows5_1,table32Rows5_2,table32Rows5_3,table32Rows5_4,table32Rows5_5,table32Rows6_0,table32Rows6_1,table32Rows6_2,table32Rows6_3,table32Rows6_4,table32Rows6_5,table32Rows7_0,table32Rows7_1,table32Rows7_2,table32Rows7_3,table32Rows7_4,table32Rows7_5,table32Rows8_0,table32Rows8_1,table32Rows8_2,table32Rows8_3,table32Rows8_4,table32Rows8_5]
    root1Node110Domains0 root1Node110Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node110Step1Chunk0_0_checked, root1Node110Step1Chunk0_1_checked, root1Node110Step1Chunk0_2_checked, root1Node110Step1Chunk0_3_checked, root1Node110Step1Chunk0_4_checked, root1Node110Step1Chunk0_5_checked, root1Node110Step1Chunk1_0_checked, root1Node110Step1Chunk1_1_checked, root1Node110Step1Chunk1_2_checked, root1Node110Step1Chunk1_3_checked, root1Node110Step1Chunk1_4_checked, root1Node110Step1Chunk1_5_checked, root1Node110Step1Chunk2_0_checked, root1Node110Step1Chunk2_1_checked, root1Node110Step1Chunk2_2_checked, root1Node110Step1Chunk2_3_checked, root1Node110Step1Chunk2_4_checked, root1Node110Step1Chunk2_5_checked, root1Node110Step1Chunk3_0_checked, root1Node110Step1Chunk3_1_checked, root1Node110Step1Chunk3_2_checked, root1Node110Step1Chunk3_3_checked, root1Node110Step1Chunk3_4_checked, root1Node110Step1Chunk3_5_checked, root1Node110Step1Chunk4_0_checked, root1Node110Step1Chunk4_1_checked, root1Node110Step1Chunk4_2_checked, root1Node110Step1Chunk4_3_checked, root1Node110Step1Chunk4_4_checked, root1Node110Step1Chunk4_5_checked, root1Node110Step1Chunk5_0_checked, root1Node110Step1Chunk5_1_checked, root1Node110Step1Chunk5_2_checked, root1Node110Step1Chunk5_3_checked, root1Node110Step1Chunk5_4_checked, root1Node110Step1Chunk5_5_checked, root1Node110Step1Chunk6_0_checked, root1Node110Step1Chunk6_1_checked, root1Node110Step1Chunk6_2_checked, root1Node110Step1Chunk6_3_checked, root1Node110Step1Chunk6_4_checked, root1Node110Step1Chunk6_5_checked, root1Node110Step1Chunk7_0_checked, root1Node110Step1Chunk7_1_checked, root1Node110Step1Chunk7_2_checked, root1Node110Step1Chunk7_3_checked, root1Node110Step1Chunk7_4_checked, root1Node110Step1Chunk7_5_checked, root1Node110Step1Chunk8_0_checked, root1Node110Step1Chunk8_1_checked, root1Node110Step1Chunk8_2_checked, root1Node110Step1Chunk8_3_checked, root1Node110Step1Chunk8_4_checked, root1Node110Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node110Step1_checked :
    checkReplacement table32 root1Node110Domains0 root1Node110Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node110Domains0 root1Node110Domains1
    root1Node110Domains0Fast root1Node110Domains1Fast
    root1Node110Domains0_fast_eq root1Node110Domains1_fast_eq
    root1Node110Step1Narrowing_checked (by decide)
def root1Node110Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(8,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3)]
  | 5 => [(4,2),(5,2),(8,2)]
  | 6 => [(5,1)]
  | 7 => [(0,1)]
  | 8 => [(6,2)]
  | 9 => [(8,4)]
  | 10 => [(6,4)]
  | 11 => [(1,2)]
  | 12 => [(7,4),(8,4)]
  | 13 => [(8,3)]
  | 14 => [(8,5)]
  | 15 => [(1,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(0,3)]
  | 19 => [(8,1)]
  | 20 => [(1,5),(6,5)]
  | 21 => [(7,4)]
  | 22 => [(6,3)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(4,2)]
  | 27 => [(5,3)]
  | 28 => [(8,5)]
  | 29 => [(7,0)]
  | 30 => [(4,1)]
  | 31 => [(0,2)]
  | 32 => [(1,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(7,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(7,3)]
  | 41 => [(5,2)]
  | 42 => [(8,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5)]
  | 45 => [(1,0)]
  | 46 => [(2,1)]
  | 47 => [(0,2)]
  | 48 => [(1,1)]
  | 49 => [(4,1)]
  | 50 => [(0,2)]
  | 51 => [(6,2)]
  | 52 => [(8,4)]
  | 53 => [(1,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(0,0)]
  | 57 => [(3,2)]
  | 58 => [(4,0)]
  | 59 => [(7,3)]
  | 60 => [(5,2)]
  | 61 => [(7,1)]
  | 62 => [(7,5)]
  | 63 => [(6,0)]
  | 64 => [(7,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(5,1)]
  | 68 => [(0,1)]
  | 69 => [(6,2)]
  | 70 => [(7,3)]
  | 71 => [(8,2)]
  | 72 => [(5,0)]
  | 73 => [(4,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(8,5)]
  | 77 => [(1,0)]
  | 78 => [(1,2),(6,2)]
  | 79 => [(8,4)]
  | 80 => [(0,0)]
  | 81 => [(7,2)]
  | 82 => [(7,4)]
  | 83 => [(1,3)]
  | 84 => [(8,2)]
  | 85 => [(7,1),(8,1)]
  | 86 => [(1,5)]
  | 87 => [(6,1)]
  | 88 => [(8,1)]
  | 89 => [(6,5)]
  | _ => [(0,4)]
def root1Node110Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(4,2),(5,2),(8,2)]
  | 6 => some [(5,1)]
  | 7 => some [(0,1)]
  | 8 => some [(6,2)]
  | 9 => some [(8,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(7,4),(8,4)]
  | 13 => some [(8,3)]
  | 14 => some [(8,5)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3)]
  | 19 => some [(8,1)]
  | 20 => some [(1,5),(6,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(4,2)]
  | 27 => some [(5,3)]
  | 28 => some [(8,5)]
  | 29 => some [(7,0)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(7,3)]
  | 41 => some [(5,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(1,0)]
  | 46 => some [(2,1)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(6,2)]
  | 52 => some [(8,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(0,0)]
  | 57 => some [(3,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(5,2)]
  | 61 => some [(7,1)]
  | 62 => some [(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(7,3)]
  | 71 => some [(8,2)]
  | 72 => some [(5,0)]
  | 73 => some [(4,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(8,5)]
  | 77 => some [(1,0)]
  | 78 => some [(1,2),(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(0,0)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(1,3)]
  | 84 => some [(8,2)]
  | 85 => some [(7,1),(8,1)]
  | 86 => some [(1,5)]
  | 87 => some [(6,1)]
  | 88 => some [(8,1)]
  | 89 => some [(6,5)]
  | _ => some [(0,4)]
theorem root1Node110Domains2_fast_eq : root1Node110Domains2 = expandDomains root1Node110Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node110Domains2 v = expandDomains root1Node110Domains2Fast v from by decide) v
theorem root1Node110Step2Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq (by decide)
theorem root1Node110Step2Narrowing_checked :
    checkNarrowing table65 root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root1Node110Domains1 root1Node110Domains2 (by
      simp only [List.all_cons, List.all_nil, root1Node110Step2Chunk0_0_checked, root1Node110Step2Chunk0_1_checked, root1Node110Step2Chunk0_2_checked, root1Node110Step2Chunk0_3_checked, root1Node110Step2Chunk0_4_checked, root1Node110Step2Chunk0_5_checked, root1Node110Step2Chunk1_0_checked, root1Node110Step2Chunk1_1_checked, root1Node110Step2Chunk1_2_checked, root1Node110Step2Chunk1_3_checked, root1Node110Step2Chunk1_4_checked, root1Node110Step2Chunk1_5_checked, root1Node110Step2Chunk2_0_checked, root1Node110Step2Chunk2_1_checked, root1Node110Step2Chunk2_2_checked, root1Node110Step2Chunk2_3_checked, root1Node110Step2Chunk2_4_checked, root1Node110Step2Chunk2_5_checked, root1Node110Step2Chunk3_0_checked, root1Node110Step2Chunk3_1_checked, root1Node110Step2Chunk3_2_checked, root1Node110Step2Chunk3_3_checked, root1Node110Step2Chunk3_4_checked, root1Node110Step2Chunk3_5_checked, root1Node110Step2Chunk4_0_checked, root1Node110Step2Chunk4_1_checked, root1Node110Step2Chunk4_2_checked, root1Node110Step2Chunk4_3_checked, root1Node110Step2Chunk4_4_checked, root1Node110Step2Chunk4_5_checked, root1Node110Step2Chunk5_0_checked, root1Node110Step2Chunk5_1_checked, root1Node110Step2Chunk5_2_checked, root1Node110Step2Chunk5_3_checked, root1Node110Step2Chunk5_4_checked, root1Node110Step2Chunk5_5_checked, root1Node110Step2Chunk6_0_checked, root1Node110Step2Chunk6_1_checked, root1Node110Step2Chunk6_2_checked, root1Node110Step2Chunk6_3_checked, root1Node110Step2Chunk6_4_checked, root1Node110Step2Chunk6_5_checked, root1Node110Step2Chunk7_0_checked, root1Node110Step2Chunk7_1_checked, root1Node110Step2Chunk7_2_checked, root1Node110Step2Chunk7_3_checked, root1Node110Step2Chunk7_4_checked, root1Node110Step2Chunk7_5_checked, root1Node110Step2Chunk8_0_checked, root1Node110Step2Chunk8_1_checked, root1Node110Step2Chunk8_2_checked, root1Node110Step2Chunk8_3_checked, root1Node110Step2Chunk8_4_checked, root1Node110Step2Chunk8_5_checked, Bool.true_and])
theorem root1Node110Step2_checked :
    checkReplacement table65 root1Node110Domains1 root1Node110Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root1Node110Domains1 root1Node110Domains2
    root1Node110Domains1Fast root1Node110Domains2Fast
    root1Node110Domains1_fast_eq root1Node110Domains2_fast_eq
    root1Node110Step2Narrowing_checked (by decide)
def root1Node110Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(8,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3)]
  | 5 => [(4,2),(8,2)]
  | 6 => [(5,1)]
  | 7 => [(0,1)]
  | 8 => [(6,2)]
  | 9 => [(8,4)]
  | 10 => [(6,4)]
  | 11 => [(1,2)]
  | 12 => [(7,4),(8,4)]
  | 13 => [(8,3)]
  | 14 => [(8,5)]
  | 15 => [(1,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(0,3)]
  | 19 => [(8,1)]
  | 20 => [(1,5),(6,5)]
  | 21 => [(7,4)]
  | 22 => [(6,3)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(4,2)]
  | 27 => [(5,3)]
  | 28 => [(8,5)]
  | 29 => [(7,0)]
  | 30 => [(4,1)]
  | 31 => [(0,2)]
  | 32 => [(1,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(7,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(7,3)]
  | 41 => [(5,2)]
  | 42 => [(8,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5)]
  | 45 => [(1,0)]
  | 46 => [(2,1)]
  | 47 => [(0,2)]
  | 48 => [(1,1)]
  | 49 => [(4,1)]
  | 50 => [(0,2)]
  | 51 => [(6,2)]
  | 52 => [(8,4)]
  | 53 => [(1,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(0,0)]
  | 57 => [(3,2)]
  | 58 => [(4,0)]
  | 59 => [(7,3)]
  | 60 => [(5,2)]
  | 61 => [(7,1)]
  | 62 => [(7,5)]
  | 63 => [(6,0)]
  | 64 => [(7,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(5,1)]
  | 68 => [(0,1)]
  | 69 => [(6,2)]
  | 70 => [(7,3)]
  | 71 => [(8,2)]
  | 72 => [(5,0)]
  | 73 => [(4,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(8,5)]
  | 77 => [(1,0)]
  | 78 => [(1,2),(6,2)]
  | 79 => [(8,4)]
  | 80 => [(0,0)]
  | 81 => [(7,2)]
  | 82 => [(7,4)]
  | 83 => [(1,3)]
  | 84 => [(8,2)]
  | 85 => [(7,1),(8,1)]
  | 86 => [(1,5)]
  | 87 => [(6,1)]
  | 88 => [(8,1)]
  | 89 => [(6,5)]
  | _ => [(0,4)]
def root1Node110Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(4,2),(8,2)]
  | 6 => some [(5,1)]
  | 7 => some [(0,1)]
  | 8 => some [(6,2)]
  | 9 => some [(8,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(7,4),(8,4)]
  | 13 => some [(8,3)]
  | 14 => some [(8,5)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3)]
  | 19 => some [(8,1)]
  | 20 => some [(1,5),(6,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(4,2)]
  | 27 => some [(5,3)]
  | 28 => some [(8,5)]
  | 29 => some [(7,0)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(7,3)]
  | 41 => some [(5,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(1,0)]
  | 46 => some [(2,1)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(6,2)]
  | 52 => some [(8,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(0,0)]
  | 57 => some [(3,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(5,2)]
  | 61 => some [(7,1)]
  | 62 => some [(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(7,3)]
  | 71 => some [(8,2)]
  | 72 => some [(5,0)]
  | 73 => some [(4,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(8,5)]
  | 77 => some [(1,0)]
  | 78 => some [(1,2),(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(0,0)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(1,3)]
  | 84 => some [(8,2)]
  | 85 => some [(7,1),(8,1)]
  | 86 => some [(1,5)]
  | 87 => some [(6,1)]
  | 88 => some [(8,1)]
  | 89 => some [(6,5)]
  | _ => some [(0,4)]
theorem root1Node110Domains3_fast_eq : root1Node110Domains3 = expandDomains root1Node110Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node110Domains3 v = expandDomains root1Node110Domains3Fast v from by decide) v
theorem root1Node110Step3Chunk0_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_0⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk0_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_1⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk0_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_2⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk0_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_3⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk0_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_4⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk0_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_5⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk1_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_0⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk1_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_1⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk1_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_2⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk1_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_3⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk1_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_4⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk1_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_5⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk2_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_0⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk2_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_1⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk2_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_2⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk2_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_3⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk2_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_4⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk2_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_5⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk3_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_0⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk3_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_1⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk3_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_2⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk3_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_3⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk3_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_4⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk3_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_5⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk4_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_0⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk4_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_1⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk4_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_2⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk4_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_3⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk4_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_4⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk4_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_5⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk5_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_0⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk5_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_1⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk5_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_2⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk5_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_3⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk5_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_4⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk5_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_5⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk6_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_0⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk6_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_1⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk6_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_2⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk6_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_3⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk6_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_4⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk6_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_5⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk7_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_0⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk7_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_1⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk7_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_2⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk7_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_3⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk7_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_4⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk7_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_5⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk8_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_0⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk8_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_1⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk8_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_2⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk8_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_3⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk8_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_4⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Chunk8_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_5⟩
      root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq (by decide)
theorem root1Node110Step3Narrowing_checked :
    checkNarrowing table1 root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkNarrowing_flatten table1Scope [table1Rows0_0,table1Rows0_1,table1Rows0_2,table1Rows0_3,table1Rows0_4,table1Rows0_5,table1Rows1_0,table1Rows1_1,table1Rows1_2,table1Rows1_3,table1Rows1_4,table1Rows1_5,table1Rows2_0,table1Rows2_1,table1Rows2_2,table1Rows2_3,table1Rows2_4,table1Rows2_5,table1Rows3_0,table1Rows3_1,table1Rows3_2,table1Rows3_3,table1Rows3_4,table1Rows3_5,table1Rows4_0,table1Rows4_1,table1Rows4_2,table1Rows4_3,table1Rows4_4,table1Rows4_5,table1Rows5_0,table1Rows5_1,table1Rows5_2,table1Rows5_3,table1Rows5_4,table1Rows5_5,table1Rows6_0,table1Rows6_1,table1Rows6_2,table1Rows6_3,table1Rows6_4,table1Rows6_5,table1Rows7_0,table1Rows7_1,table1Rows7_2,table1Rows7_3,table1Rows7_4,table1Rows7_5,table1Rows8_0,table1Rows8_1,table1Rows8_2,table1Rows8_3,table1Rows8_4,table1Rows8_5]
    root1Node110Domains2 root1Node110Domains3 (by
      simp only [List.all_cons, List.all_nil, root1Node110Step3Chunk0_0_checked, root1Node110Step3Chunk0_1_checked, root1Node110Step3Chunk0_2_checked, root1Node110Step3Chunk0_3_checked, root1Node110Step3Chunk0_4_checked, root1Node110Step3Chunk0_5_checked, root1Node110Step3Chunk1_0_checked, root1Node110Step3Chunk1_1_checked, root1Node110Step3Chunk1_2_checked, root1Node110Step3Chunk1_3_checked, root1Node110Step3Chunk1_4_checked, root1Node110Step3Chunk1_5_checked, root1Node110Step3Chunk2_0_checked, root1Node110Step3Chunk2_1_checked, root1Node110Step3Chunk2_2_checked, root1Node110Step3Chunk2_3_checked, root1Node110Step3Chunk2_4_checked, root1Node110Step3Chunk2_5_checked, root1Node110Step3Chunk3_0_checked, root1Node110Step3Chunk3_1_checked, root1Node110Step3Chunk3_2_checked, root1Node110Step3Chunk3_3_checked, root1Node110Step3Chunk3_4_checked, root1Node110Step3Chunk3_5_checked, root1Node110Step3Chunk4_0_checked, root1Node110Step3Chunk4_1_checked, root1Node110Step3Chunk4_2_checked, root1Node110Step3Chunk4_3_checked, root1Node110Step3Chunk4_4_checked, root1Node110Step3Chunk4_5_checked, root1Node110Step3Chunk5_0_checked, root1Node110Step3Chunk5_1_checked, root1Node110Step3Chunk5_2_checked, root1Node110Step3Chunk5_3_checked, root1Node110Step3Chunk5_4_checked, root1Node110Step3Chunk5_5_checked, root1Node110Step3Chunk6_0_checked, root1Node110Step3Chunk6_1_checked, root1Node110Step3Chunk6_2_checked, root1Node110Step3Chunk6_3_checked, root1Node110Step3Chunk6_4_checked, root1Node110Step3Chunk6_5_checked, root1Node110Step3Chunk7_0_checked, root1Node110Step3Chunk7_1_checked, root1Node110Step3Chunk7_2_checked, root1Node110Step3Chunk7_3_checked, root1Node110Step3Chunk7_4_checked, root1Node110Step3Chunk7_5_checked, root1Node110Step3Chunk8_0_checked, root1Node110Step3Chunk8_1_checked, root1Node110Step3Chunk8_2_checked, root1Node110Step3Chunk8_3_checked, root1Node110Step3Chunk8_4_checked, root1Node110Step3Chunk8_5_checked, Bool.true_and])
theorem root1Node110Step3_checked :
    checkReplacement table1 root1Node110Domains2 root1Node110Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root1Node110Domains2 root1Node110Domains3
    root1Node110Domains2Fast root1Node110Domains3Fast
    root1Node110Domains2_fast_eq root1Node110Domains3_fast_eq
    root1Node110Step3Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
