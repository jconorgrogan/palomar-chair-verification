module

public import SpectreFinite.RadiusFiveRoot6Part23
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable55

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node52Domains0 : Domains 91 State := restrict root6Node51Domains2 78 (1,3)
def root6Node52Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(4,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(3,4)]
  | 21 => some [(2,2)]
  | 22 => some [(3,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(2,3)]
  | 29 => some [(0,2)]
  | 30 => some [(1,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(4,0)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(1,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(5,1)]
  | 50 => some [(0,1)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(6,5)]
  | 78 => some [(1,3)]
  | 79 => some [(7,2),(8,2)]
  | 80 => some [(4,0),(8,0)]
  | 81 => some [(7,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(8,5)]
  | 85 => some [(0,4),(1,1)]
  | 86 => some [(5,1),(5,4)]
  | 87 => some [(0,1),(6,4)]
  | 88 => some [(1,2),(6,2)]
  | 89 => some [(7,4)]
  | _ => some [(6,3)]
theorem root6Node52Domains0_fast_eq : root6Node52Domains0 = expandDomains root6Node52Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node52Domains0 v = expandDomains root6Node52Domains0Fast v from by decide) v
def root6Node52Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(4,3)]
  | 5 => [(7,5)]
  | 6 => [(1,2)]
  | 7 => [(7,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(1,3)]
  | 12 => [(4,2)]
  | 13 => [(0,3)]
  | 14 => [(4,1)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(8,1)]
  | 18 => [(6,5)]
  | 19 => [(0,4)]
  | 20 => [(3,4)]
  | 21 => [(2,2)]
  | 22 => [(3,3)]
  | 23 => [(5,2)]
  | 24 => [(8,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(2,3)]
  | 29 => [(0,2)]
  | 30 => [(1,1)]
  | 31 => [(0,1)]
  | 32 => [(6,2)]
  | 33 => [(8,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(4,0)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(1,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(5,1)]
  | 50 => [(0,1)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(8,0)]
  | 57 => [(7,3)]
  | 58 => [(4,2)]
  | 59 => [(5,3)]
  | 60 => [(8,5)]
  | 61 => [(6,1)]
  | 62 => [(5,1)]
  | 63 => [(0,1)]
  | 64 => [(6,2)]
  | 65 => [(8,4)]
  | 66 => [(6,4)]
  | 67 => [(1,2)]
  | 68 => [(7,4)]
  | 69 => [(1,3)]
  | 70 => [(8,3)]
  | 71 => [(8,5)]
  | 72 => [(1,0)]
  | 73 => [(7,1)]
  | 74 => [(7,5)]
  | 75 => [(0,3)]
  | 76 => [(8,1)]
  | 77 => [(6,5)]
  | 78 => [(1,3)]
  | 79 => [(8,2)]
  | 80 => [(8,0)]
  | 81 => [(7,3)]
  | 82 => [(4,2)]
  | 83 => [(5,3)]
  | 84 => [(8,5)]
  | 85 => [(0,4)]
  | 86 => [(5,4)]
  | 87 => [(6,4)]
  | 88 => [(1,2)]
  | 89 => [(7,4)]
  | _ => [(6,3)]
def root6Node52Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(4,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(3,4)]
  | 21 => some [(2,2)]
  | 22 => some [(3,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(2,3)]
  | 29 => some [(0,2)]
  | 30 => some [(1,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(4,0)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(1,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(5,1)]
  | 50 => some [(0,1)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(6,5)]
  | 78 => some [(1,3)]
  | 79 => some [(8,2)]
  | 80 => some [(8,0)]
  | 81 => some [(7,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(8,5)]
  | 85 => some [(0,4)]
  | 86 => some [(5,4)]
  | 87 => some [(6,4)]
  | 88 => some [(1,2)]
  | 89 => some [(7,4)]
  | _ => some [(6,3)]
theorem root6Node52Domains1_fast_eq : root6Node52Domains1 = expandDomains root6Node52Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node52Domains1 v = expandDomains root6Node52Domains1Fast v from by decide) v
theorem root6Node52Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Narrowing_checked :
    checkNarrowing table54 root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root6Node52Domains0 root6Node52Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node52Step1Chunk0_0_checked, root6Node52Step1Chunk0_1_checked, root6Node52Step1Chunk0_2_checked, root6Node52Step1Chunk0_3_checked, root6Node52Step1Chunk0_4_checked, root6Node52Step1Chunk0_5_checked, root6Node52Step1Chunk1_0_checked, root6Node52Step1Chunk1_1_checked, root6Node52Step1Chunk1_2_checked, root6Node52Step1Chunk1_3_checked, root6Node52Step1Chunk1_4_checked, root6Node52Step1Chunk1_5_checked, root6Node52Step1Chunk2_0_checked, root6Node52Step1Chunk2_1_checked, root6Node52Step1Chunk2_2_checked, root6Node52Step1Chunk2_3_checked, root6Node52Step1Chunk2_4_checked, root6Node52Step1Chunk2_5_checked, root6Node52Step1Chunk3_0_checked, root6Node52Step1Chunk3_1_checked, root6Node52Step1Chunk3_2_checked, root6Node52Step1Chunk3_3_checked, root6Node52Step1Chunk3_4_checked, root6Node52Step1Chunk3_5_checked, root6Node52Step1Chunk4_0_checked, root6Node52Step1Chunk4_1_checked, root6Node52Step1Chunk4_2_checked, root6Node52Step1Chunk4_3_checked, root6Node52Step1Chunk4_4_checked, root6Node52Step1Chunk4_5_checked, root6Node52Step1Chunk5_0_checked, root6Node52Step1Chunk5_1_checked, root6Node52Step1Chunk5_2_checked, root6Node52Step1Chunk5_3_checked, root6Node52Step1Chunk5_4_checked, root6Node52Step1Chunk5_5_checked, root6Node52Step1Chunk6_0_checked, root6Node52Step1Chunk6_1_checked, root6Node52Step1Chunk6_2_checked, root6Node52Step1Chunk6_3_checked, root6Node52Step1Chunk6_4_checked, root6Node52Step1Chunk6_5_checked, root6Node52Step1Chunk7_0_checked, root6Node52Step1Chunk7_1_checked, root6Node52Step1Chunk7_2_checked, root6Node52Step1Chunk7_3_checked, root6Node52Step1Chunk7_4_checked, root6Node52Step1Chunk7_5_checked, root6Node52Step1Chunk8_0_checked, root6Node52Step1Chunk8_1_checked, root6Node52Step1Chunk8_2_checked, root6Node52Step1Chunk8_3_checked, root6Node52Step1Chunk8_4_checked, root6Node52Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node52Step1_checked :
    checkReplacement table54 root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq
    root6Node52Step1Narrowing_checked (by decide)
theorem root6Node52Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node52Domains1 (.output 24) = true := by decide
def root6Node53Domains0 : Domains 91 State := restrict root6Node51Domains2 78 (6,3)
def root6Node53Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(4,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(3,4)]
  | 21 => some [(2,2)]
  | 22 => some [(3,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(2,3)]
  | 29 => some [(0,2)]
  | 30 => some [(1,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(4,0)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(1,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(5,1)]
  | 50 => some [(0,1)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(6,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2),(8,2)]
  | 80 => some [(4,0),(8,0)]
  | 81 => some [(7,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(8,5)]
  | 85 => some [(0,4),(1,1)]
  | 86 => some [(5,1),(5,4)]
  | 87 => some [(0,1),(6,4)]
  | 88 => some [(1,2),(6,2)]
  | 89 => some [(7,4)]
  | _ => some [(6,3)]
theorem root6Node53Domains0_fast_eq : root6Node53Domains0 = expandDomains root6Node53Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node53Domains0 v = expandDomains root6Node53Domains0Fast v from by decide) v
def root6Node53Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(4,3)]
  | 5 => [(7,5)]
  | 6 => [(1,2)]
  | 7 => [(7,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(1,3)]
  | 12 => [(4,2)]
  | 13 => [(0,3)]
  | 14 => [(4,1)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(8,1)]
  | 18 => [(6,5)]
  | 19 => [(0,4)]
  | 20 => [(3,4)]
  | 21 => [(2,2)]
  | 22 => [(3,3)]
  | 23 => [(5,2)]
  | 24 => [(8,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(2,3)]
  | 29 => [(0,2)]
  | 30 => [(1,1)]
  | 31 => [(0,1)]
  | 32 => [(6,2)]
  | 33 => [(8,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(4,0)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(1,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(5,1)]
  | 50 => [(0,1)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(8,0)]
  | 57 => [(7,3)]
  | 58 => [(4,2)]
  | 59 => [(5,3)]
  | 60 => [(8,5)]
  | 61 => [(6,1)]
  | 62 => [(5,1)]
  | 63 => [(0,1)]
  | 64 => [(6,2)]
  | 65 => [(8,4)]
  | 66 => [(6,4)]
  | 67 => [(1,2)]
  | 68 => [(7,4)]
  | 69 => [(1,3)]
  | 70 => [(8,3)]
  | 71 => [(8,5)]
  | 72 => [(1,0)]
  | 73 => [(7,1)]
  | 74 => [(7,5)]
  | 75 => [(0,3)]
  | 76 => [(8,1)]
  | 77 => [(6,5)]
  | 78 => [(6,3)]
  | 79 => [(7,2)]
  | 80 => [(4,0)]
  | 81 => [(7,3)]
  | 82 => [(4,2)]
  | 83 => [(5,3)]
  | 84 => [(8,5)]
  | 85 => [(1,1)]
  | 86 => [(5,1)]
  | 87 => [(0,1)]
  | 88 => [(6,2)]
  | 89 => [(7,4)]
  | _ => [(6,3)]
def root6Node53Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(4,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(3,4)]
  | 21 => some [(2,2)]
  | 22 => some [(3,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(2,3)]
  | 29 => some [(0,2)]
  | 30 => some [(1,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(4,0)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(1,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(5,1)]
  | 50 => some [(0,1)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(6,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(4,0)]
  | 81 => some [(7,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(8,5)]
  | 85 => some [(1,1)]
  | 86 => some [(5,1)]
  | 87 => some [(0,1)]
  | 88 => some [(6,2)]
  | 89 => some [(7,4)]
  | _ => some [(6,3)]
theorem root6Node53Domains1_fast_eq : root6Node53Domains1 = expandDomains root6Node53Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node53Domains1 v = expandDomains root6Node53Domains1Fast v from by decide) v
theorem root6Node53Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq (by decide)
theorem root6Node53Step1Narrowing_checked :
    checkNarrowing table54 root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root6Node53Domains0 root6Node53Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node53Step1Chunk0_0_checked, root6Node53Step1Chunk0_1_checked, root6Node53Step1Chunk0_2_checked, root6Node53Step1Chunk0_3_checked, root6Node53Step1Chunk0_4_checked, root6Node53Step1Chunk0_5_checked, root6Node53Step1Chunk1_0_checked, root6Node53Step1Chunk1_1_checked, root6Node53Step1Chunk1_2_checked, root6Node53Step1Chunk1_3_checked, root6Node53Step1Chunk1_4_checked, root6Node53Step1Chunk1_5_checked, root6Node53Step1Chunk2_0_checked, root6Node53Step1Chunk2_1_checked, root6Node53Step1Chunk2_2_checked, root6Node53Step1Chunk2_3_checked, root6Node53Step1Chunk2_4_checked, root6Node53Step1Chunk2_5_checked, root6Node53Step1Chunk3_0_checked, root6Node53Step1Chunk3_1_checked, root6Node53Step1Chunk3_2_checked, root6Node53Step1Chunk3_3_checked, root6Node53Step1Chunk3_4_checked, root6Node53Step1Chunk3_5_checked, root6Node53Step1Chunk4_0_checked, root6Node53Step1Chunk4_1_checked, root6Node53Step1Chunk4_2_checked, root6Node53Step1Chunk4_3_checked, root6Node53Step1Chunk4_4_checked, root6Node53Step1Chunk4_5_checked, root6Node53Step1Chunk5_0_checked, root6Node53Step1Chunk5_1_checked, root6Node53Step1Chunk5_2_checked, root6Node53Step1Chunk5_3_checked, root6Node53Step1Chunk5_4_checked, root6Node53Step1Chunk5_5_checked, root6Node53Step1Chunk6_0_checked, root6Node53Step1Chunk6_1_checked, root6Node53Step1Chunk6_2_checked, root6Node53Step1Chunk6_3_checked, root6Node53Step1Chunk6_4_checked, root6Node53Step1Chunk6_5_checked, root6Node53Step1Chunk7_0_checked, root6Node53Step1Chunk7_1_checked, root6Node53Step1Chunk7_2_checked, root6Node53Step1Chunk7_3_checked, root6Node53Step1Chunk7_4_checked, root6Node53Step1Chunk7_5_checked, root6Node53Step1Chunk8_0_checked, root6Node53Step1Chunk8_1_checked, root6Node53Step1Chunk8_2_checked, root6Node53Step1Chunk8_3_checked, root6Node53Step1Chunk8_4_checked, root6Node53Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node53Step1_checked :
    checkReplacement table54 root6Node53Domains0 root6Node53Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node53Domains0 root6Node53Domains1
    root6Node53Domains0Fast root6Node53Domains1Fast
    root6Node53Domains0_fast_eq root6Node53Domains1_fast_eq
    root6Node53Step1Narrowing_checked (by decide)
theorem root6Node53Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node53Domains1 (.output 25) = true := by decide
def root6Node54Domains0 : Domains 91 State := restrict root6Node50Domains1 21 (2,4)
def root6Node54Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(4,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(3,4)]
  | 21 => some [(2,4)]
  | 22 => some [(1,3),(3,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(2,3)]
  | 29 => some [(0,2)]
  | 30 => some [(1,1),(7,1)]
  | 31 => some [(0,1),(6,5)]
  | 32 => some [(0,4),(6,2)]
  | 33 => some [(5,4),(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(4,0)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(1,0),(7,0)]
  | 43 => some [(4,3),(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(5,1)]
  | 50 => some [(0,1)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0),(7,4)]
  | 54 => some [(1,3),(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1),(8,1)]
  | 63 => some [(0,1),(6,5)]
  | 64 => some [(0,4),(6,2)]
  | 65 => some [(5,4),(8,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3),(6,3)]
  | 70 => some [(8,3)]
  | 71 => some [(5,5),(8,5)]
  | 72 => some [(1,0),(7,0)]
  | 73 => some [(4,3),(7,1)]
  | 74 => some [(3,5),(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(4,1),(8,1)]
  | 77 => some [(0,2),(6,5)]
  | 78 => some [(0,5),(1,3),(6,3)]
  | 79 => some [(4,4),(7,2),(8,2)]
  | 80 => some [(1,4),(4,0),(7,4),(8,0)]
  | 81 => some [(0,5),(1,3),(6,3),(7,3)]
  | 82 => some [(2,2),(2,4),(4,2)]
  | 83 => some [(1,3),(3,3),(5,3)]
  | 84 => some [(5,2),(5,5),(8,5)]
  | 85 => some [(0,4),(1,1),(7,1)]
  | 86 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 87 => some [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 88 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 89 => some [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => some [(0,4),(0,5),(6,2),(6,3)]
theorem root6Node54Domains0_fast_eq : root6Node54Domains0 = expandDomains root6Node54Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node54Domains0 v = expandDomains root6Node54Domains0Fast v from by decide) v
def root6Node54Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(4,3)]
  | 5 => [(7,5)]
  | 6 => [(1,2)]
  | 7 => [(7,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(1,3)]
  | 12 => [(4,2)]
  | 13 => [(0,3)]
  | 14 => [(4,1)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(8,1)]
  | 18 => [(6,5)]
  | 19 => [(0,4)]
  | 20 => [(3,4)]
  | 21 => [(2,4)]
  | 22 => [(1,3)]
  | 23 => [(5,2)]
  | 24 => [(8,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(2,3)]
  | 29 => [(0,2)]
  | 30 => [(7,1)]
  | 31 => [(6,5)]
  | 32 => [(0,4)]
  | 33 => [(5,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(4,0)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(4,3)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(5,1)]
  | 50 => [(0,1)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3)]
  | 55 => [(8,2)]
  | 56 => [(8,0)]
  | 57 => [(7,3)]
  | 58 => [(4,2)]
  | 59 => [(5,3)]
  | 60 => [(8,5)]
  | 61 => [(6,1)]
  | 62 => [(8,1)]
  | 63 => [(6,5)]
  | 64 => [(0,4)]
  | 65 => [(5,4)]
  | 66 => [(6,4)]
  | 67 => [(1,2)]
  | 68 => [(7,4)]
  | 69 => [(1,3),(6,3)]
  | 70 => [(8,3)]
  | 71 => [(5,5),(8,5)]
  | 72 => [(7,0)]
  | 73 => [(4,3)]
  | 74 => [(3,5),(7,5)]
  | 75 => [(0,3)]
  | 76 => [(4,1),(8,1)]
  | 77 => [(0,2),(6,5)]
  | 78 => [(0,5),(6,3)]
  | 79 => [(4,4),(7,2)]
  | 80 => [(1,4),(7,4)]
  | 81 => [(0,5),(1,3),(6,3)]
  | 82 => [(2,2),(2,4),(4,2)]
  | 83 => [(1,3),(3,3),(5,3)]
  | 84 => [(5,2),(5,5),(8,5)]
  | 85 => [(1,1),(7,1)]
  | 86 => [(4,1),(7,5),(8,1)]
  | 87 => [(0,2),(6,0),(6,5)]
  | 88 => [(0,4),(1,1),(7,1)]
  | 89 => [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => [(0,4),(0,5),(6,2),(6,3)]
def root6Node54Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(4,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(3,4)]
  | 21 => some [(2,4)]
  | 22 => some [(1,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(2,3)]
  | 29 => some [(0,2)]
  | 30 => some [(7,1)]
  | 31 => some [(6,5)]
  | 32 => some [(0,4)]
  | 33 => some [(5,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(4,0)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(4,3)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(5,1)]
  | 50 => some [(0,1)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3),(6,3)]
  | 70 => some [(8,3)]
  | 71 => some [(5,5),(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(3,5),(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(4,1),(8,1)]
  | 77 => some [(0,2),(6,5)]
  | 78 => some [(0,5),(6,3)]
  | 79 => some [(4,4),(7,2)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(1,3),(6,3)]
  | 82 => some [(2,2),(2,4),(4,2)]
  | 83 => some [(1,3),(3,3),(5,3)]
  | 84 => some [(5,2),(5,5),(8,5)]
  | 85 => some [(1,1),(7,1)]
  | 86 => some [(4,1),(7,5),(8,1)]
  | 87 => some [(0,2),(6,0),(6,5)]
  | 88 => some [(0,4),(1,1),(7,1)]
  | 89 => some [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => some [(0,4),(0,5),(6,2),(6,3)]
theorem root6Node54Domains1_fast_eq : root6Node54Domains1 = expandDomains root6Node54Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node54Domains1 v = expandDomains root6Node54Domains1Fast v from by decide) v
theorem root6Node54Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Narrowing_checked :
    checkNarrowing table54 root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root6Node54Domains0 root6Node54Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node54Step1Chunk0_0_checked, root6Node54Step1Chunk0_1_checked, root6Node54Step1Chunk0_2_checked, root6Node54Step1Chunk0_3_checked, root6Node54Step1Chunk0_4_checked, root6Node54Step1Chunk0_5_checked, root6Node54Step1Chunk1_0_checked, root6Node54Step1Chunk1_1_checked, root6Node54Step1Chunk1_2_checked, root6Node54Step1Chunk1_3_checked, root6Node54Step1Chunk1_4_checked, root6Node54Step1Chunk1_5_checked, root6Node54Step1Chunk2_0_checked, root6Node54Step1Chunk2_1_checked, root6Node54Step1Chunk2_2_checked, root6Node54Step1Chunk2_3_checked, root6Node54Step1Chunk2_4_checked, root6Node54Step1Chunk2_5_checked, root6Node54Step1Chunk3_0_checked, root6Node54Step1Chunk3_1_checked, root6Node54Step1Chunk3_2_checked, root6Node54Step1Chunk3_3_checked, root6Node54Step1Chunk3_4_checked, root6Node54Step1Chunk3_5_checked, root6Node54Step1Chunk4_0_checked, root6Node54Step1Chunk4_1_checked, root6Node54Step1Chunk4_2_checked, root6Node54Step1Chunk4_3_checked, root6Node54Step1Chunk4_4_checked, root6Node54Step1Chunk4_5_checked, root6Node54Step1Chunk5_0_checked, root6Node54Step1Chunk5_1_checked, root6Node54Step1Chunk5_2_checked, root6Node54Step1Chunk5_3_checked, root6Node54Step1Chunk5_4_checked, root6Node54Step1Chunk5_5_checked, root6Node54Step1Chunk6_0_checked, root6Node54Step1Chunk6_1_checked, root6Node54Step1Chunk6_2_checked, root6Node54Step1Chunk6_3_checked, root6Node54Step1Chunk6_4_checked, root6Node54Step1Chunk6_5_checked, root6Node54Step1Chunk7_0_checked, root6Node54Step1Chunk7_1_checked, root6Node54Step1Chunk7_2_checked, root6Node54Step1Chunk7_3_checked, root6Node54Step1Chunk7_4_checked, root6Node54Step1Chunk7_5_checked, root6Node54Step1Chunk8_0_checked, root6Node54Step1Chunk8_1_checked, root6Node54Step1Chunk8_2_checked, root6Node54Step1Chunk8_3_checked, root6Node54Step1Chunk8_4_checked, root6Node54Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node54Step1_checked :
    checkReplacement table54 root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq
    root6Node54Step1Narrowing_checked (by decide)
def root6Node54Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(4,3)]
  | 5 => [(7,5)]
  | 6 => [(1,2)]
  | 7 => [(7,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(1,3)]
  | 12 => [(4,2)]
  | 13 => [(0,3)]
  | 14 => [(4,1)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(8,1)]
  | 18 => [(6,5)]
  | 19 => [(0,4)]
  | 20 => [(3,4)]
  | 21 => [(2,4)]
  | 22 => [(1,3)]
  | 23 => [(5,2)]
  | 24 => [(8,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(2,3)]
  | 29 => [(0,2)]
  | 30 => [(7,1)]
  | 31 => [(6,5)]
  | 32 => [(0,4)]
  | 33 => [(5,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(4,0)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(4,3)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(5,1)]
  | 50 => [(0,1)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3)]
  | 55 => [(8,2)]
  | 56 => [(8,0)]
  | 57 => [(7,3)]
  | 58 => [(4,2)]
  | 59 => [(5,3)]
  | 60 => [(8,5)]
  | 61 => [(6,1)]
  | 62 => [(8,1)]
  | 63 => [(6,5)]
  | 64 => [(0,4)]
  | 65 => [(5,4)]
  | 66 => [(6,4)]
  | 67 => [(1,2)]
  | 68 => [(7,4)]
  | 69 => [(1,3),(6,3)]
  | 70 => [(8,3)]
  | 71 => [(5,5),(8,5)]
  | 72 => [(7,0)]
  | 73 => [(4,3)]
  | 74 => [(3,5),(7,5)]
  | 75 => [(0,3)]
  | 76 => [(4,1),(8,1)]
  | 77 => [(0,2),(6,5)]
  | 78 => [(0,5),(6,3)]
  | 79 => [(4,4),(7,2)]
  | 80 => [(1,4),(7,4)]
  | 81 => [(0,5),(1,3),(6,3)]
  | 82 => [(2,2),(2,4),(4,2)]
  | 83 => [(1,3),(3,3),(5,3)]
  | 84 => [(5,2),(5,5),(8,5)]
  | 85 => [(1,1),(7,1)]
  | 86 => [(4,1),(7,5),(8,1)]
  | 87 => [(0,2),(6,0),(6,5)]
  | 88 => [(0,4),(1,1),(7,1)]
  | 89 => [(0,1),(1,4),(3,4),(6,5)]
  | _ => [(0,4),(0,5),(6,2),(6,3)]
def root6Node54Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(4,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(3,4)]
  | 21 => some [(2,4)]
  | 22 => some [(1,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(2,3)]
  | 29 => some [(0,2)]
  | 30 => some [(7,1)]
  | 31 => some [(6,5)]
  | 32 => some [(0,4)]
  | 33 => some [(5,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(4,0)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(4,3)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(5,1)]
  | 50 => some [(0,1)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3),(6,3)]
  | 70 => some [(8,3)]
  | 71 => some [(5,5),(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(3,5),(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(4,1),(8,1)]
  | 77 => some [(0,2),(6,5)]
  | 78 => some [(0,5),(6,3)]
  | 79 => some [(4,4),(7,2)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(1,3),(6,3)]
  | 82 => some [(2,2),(2,4),(4,2)]
  | 83 => some [(1,3),(3,3),(5,3)]
  | 84 => some [(5,2),(5,5),(8,5)]
  | 85 => some [(1,1),(7,1)]
  | 86 => some [(4,1),(7,5),(8,1)]
  | 87 => some [(0,2),(6,0),(6,5)]
  | 88 => some [(0,4),(1,1),(7,1)]
  | 89 => some [(0,1),(1,4),(3,4),(6,5)]
  | _ => some [(0,4),(0,5),(6,2),(6,3)]
theorem root6Node54Domains2_fast_eq : root6Node54Domains2 = expandDomains root6Node54Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node54Domains2 v = expandDomains root6Node54Domains2Fast v from by decide) v
theorem root6Node54Step2Chunk0_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_0⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk0_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_1⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk0_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_2⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk0_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_3⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk0_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_4⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk0_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_5⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk1_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_0⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk1_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_1⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk1_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_2⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk1_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_3⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk1_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_4⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk1_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_5⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk2_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_0⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk2_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_1⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk2_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_2⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk2_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_3⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk2_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_4⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk2_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_5⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk3_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_0⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk3_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_1⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk3_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_2⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk3_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_3⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk3_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_4⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk3_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_5⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk4_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_0⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk4_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_1⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk4_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_2⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk4_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_3⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk4_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_4⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk4_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_5⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk5_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_0⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk5_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_1⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk5_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_2⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk5_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_3⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk5_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_4⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk5_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_5⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk6_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_0⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk6_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_1⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk6_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_2⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk6_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_3⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk6_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_4⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk6_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_5⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk7_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_0⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk7_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_1⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk7_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_2⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk7_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_3⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk7_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_4⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk7_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_5⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk8_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_0⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk8_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_1⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk8_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_2⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk8_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_3⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk8_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_4⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Chunk8_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_5⟩
      root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq (by decide)
theorem root6Node54Step2Narrowing_checked :
    checkNarrowing table55 root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkNarrowing_flatten table55Scope [table55Rows0_0,table55Rows0_1,table55Rows0_2,table55Rows0_3,table55Rows0_4,table55Rows0_5,table55Rows1_0,table55Rows1_1,table55Rows1_2,table55Rows1_3,table55Rows1_4,table55Rows1_5,table55Rows2_0,table55Rows2_1,table55Rows2_2,table55Rows2_3,table55Rows2_4,table55Rows2_5,table55Rows3_0,table55Rows3_1,table55Rows3_2,table55Rows3_3,table55Rows3_4,table55Rows3_5,table55Rows4_0,table55Rows4_1,table55Rows4_2,table55Rows4_3,table55Rows4_4,table55Rows4_5,table55Rows5_0,table55Rows5_1,table55Rows5_2,table55Rows5_3,table55Rows5_4,table55Rows5_5,table55Rows6_0,table55Rows6_1,table55Rows6_2,table55Rows6_3,table55Rows6_4,table55Rows6_5,table55Rows7_0,table55Rows7_1,table55Rows7_2,table55Rows7_3,table55Rows7_4,table55Rows7_5,table55Rows8_0,table55Rows8_1,table55Rows8_2,table55Rows8_3,table55Rows8_4,table55Rows8_5]
    root6Node54Domains1 root6Node54Domains2 (by
      simp only [List.all_cons, List.all_nil, root6Node54Step2Chunk0_0_checked, root6Node54Step2Chunk0_1_checked, root6Node54Step2Chunk0_2_checked, root6Node54Step2Chunk0_3_checked, root6Node54Step2Chunk0_4_checked, root6Node54Step2Chunk0_5_checked, root6Node54Step2Chunk1_0_checked, root6Node54Step2Chunk1_1_checked, root6Node54Step2Chunk1_2_checked, root6Node54Step2Chunk1_3_checked, root6Node54Step2Chunk1_4_checked, root6Node54Step2Chunk1_5_checked, root6Node54Step2Chunk2_0_checked, root6Node54Step2Chunk2_1_checked, root6Node54Step2Chunk2_2_checked, root6Node54Step2Chunk2_3_checked, root6Node54Step2Chunk2_4_checked, root6Node54Step2Chunk2_5_checked, root6Node54Step2Chunk3_0_checked, root6Node54Step2Chunk3_1_checked, root6Node54Step2Chunk3_2_checked, root6Node54Step2Chunk3_3_checked, root6Node54Step2Chunk3_4_checked, root6Node54Step2Chunk3_5_checked, root6Node54Step2Chunk4_0_checked, root6Node54Step2Chunk4_1_checked, root6Node54Step2Chunk4_2_checked, root6Node54Step2Chunk4_3_checked, root6Node54Step2Chunk4_4_checked, root6Node54Step2Chunk4_5_checked, root6Node54Step2Chunk5_0_checked, root6Node54Step2Chunk5_1_checked, root6Node54Step2Chunk5_2_checked, root6Node54Step2Chunk5_3_checked, root6Node54Step2Chunk5_4_checked, root6Node54Step2Chunk5_5_checked, root6Node54Step2Chunk6_0_checked, root6Node54Step2Chunk6_1_checked, root6Node54Step2Chunk6_2_checked, root6Node54Step2Chunk6_3_checked, root6Node54Step2Chunk6_4_checked, root6Node54Step2Chunk6_5_checked, root6Node54Step2Chunk7_0_checked, root6Node54Step2Chunk7_1_checked, root6Node54Step2Chunk7_2_checked, root6Node54Step2Chunk7_3_checked, root6Node54Step2Chunk7_4_checked, root6Node54Step2Chunk7_5_checked, root6Node54Step2Chunk8_0_checked, root6Node54Step2Chunk8_1_checked, root6Node54Step2Chunk8_2_checked, root6Node54Step2Chunk8_3_checked, root6Node54Step2Chunk8_4_checked, root6Node54Step2Chunk8_5_checked, Bool.true_and])
theorem root6Node54Step2_checked :
    checkReplacement table55 root6Node54Domains1 root6Node54Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root6Node54Domains1 root6Node54Domains2
    root6Node54Domains1Fast root6Node54Domains2Fast
    root6Node54Domains1_fast_eq root6Node54Domains2_fast_eq
    root6Node54Step2Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
