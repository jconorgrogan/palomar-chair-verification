module

public import SpectreFinite.RadiusFiveRoot6Part49
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable54

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node123Domains0 : Domains 91 State := restrict root6Node122Domains1 78 (1,3)
def root6Node123Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(4,2)]
  | 13 => some [(6,1)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(3,4)]
  | 21 => some [(2,0)]
  | 22 => some [(7,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(2,3)]
  | 29 => some [(0,2)]
  | 30 => some [(3,1)]
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
theorem root6Node123Domains0_fast_eq : root6Node123Domains0 = expandDomains root6Node123Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node123Domains0 v = expandDomains root6Node123Domains0Fast v from by decide) v
def root6Node123Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(4,3)]
  | 5 => [(7,5)]
  | 6 => [(7,2)]
  | 7 => [(7,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(1,3)]
  | 12 => [(4,2)]
  | 13 => [(6,1)]
  | 14 => [(4,1)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(8,1)]
  | 18 => [(6,5)]
  | 19 => [(0,4)]
  | 20 => [(3,4)]
  | 21 => [(2,0)]
  | 22 => [(7,3)]
  | 23 => [(5,2)]
  | 24 => [(8,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(2,3)]
  | 29 => [(0,2)]
  | 30 => [(3,1)]
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
def root6Node123Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(4,2)]
  | 13 => some [(6,1)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(3,4)]
  | 21 => some [(2,0)]
  | 22 => some [(7,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(2,3)]
  | 29 => some [(0,2)]
  | 30 => some [(3,1)]
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
theorem root6Node123Domains1_fast_eq : root6Node123Domains1 = expandDomains root6Node123Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node123Domains1 v = expandDomains root6Node123Domains1Fast v from by decide) v
theorem root6Node123Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq (by decide)
theorem root6Node123Step1Narrowing_checked :
    checkNarrowing table54 root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root6Node123Domains0 root6Node123Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node123Step1Chunk0_0_checked, root6Node123Step1Chunk0_1_checked, root6Node123Step1Chunk0_2_checked, root6Node123Step1Chunk0_3_checked, root6Node123Step1Chunk0_4_checked, root6Node123Step1Chunk0_5_checked, root6Node123Step1Chunk1_0_checked, root6Node123Step1Chunk1_1_checked, root6Node123Step1Chunk1_2_checked, root6Node123Step1Chunk1_3_checked, root6Node123Step1Chunk1_4_checked, root6Node123Step1Chunk1_5_checked, root6Node123Step1Chunk2_0_checked, root6Node123Step1Chunk2_1_checked, root6Node123Step1Chunk2_2_checked, root6Node123Step1Chunk2_3_checked, root6Node123Step1Chunk2_4_checked, root6Node123Step1Chunk2_5_checked, root6Node123Step1Chunk3_0_checked, root6Node123Step1Chunk3_1_checked, root6Node123Step1Chunk3_2_checked, root6Node123Step1Chunk3_3_checked, root6Node123Step1Chunk3_4_checked, root6Node123Step1Chunk3_5_checked, root6Node123Step1Chunk4_0_checked, root6Node123Step1Chunk4_1_checked, root6Node123Step1Chunk4_2_checked, root6Node123Step1Chunk4_3_checked, root6Node123Step1Chunk4_4_checked, root6Node123Step1Chunk4_5_checked, root6Node123Step1Chunk5_0_checked, root6Node123Step1Chunk5_1_checked, root6Node123Step1Chunk5_2_checked, root6Node123Step1Chunk5_3_checked, root6Node123Step1Chunk5_4_checked, root6Node123Step1Chunk5_5_checked, root6Node123Step1Chunk6_0_checked, root6Node123Step1Chunk6_1_checked, root6Node123Step1Chunk6_2_checked, root6Node123Step1Chunk6_3_checked, root6Node123Step1Chunk6_4_checked, root6Node123Step1Chunk6_5_checked, root6Node123Step1Chunk7_0_checked, root6Node123Step1Chunk7_1_checked, root6Node123Step1Chunk7_2_checked, root6Node123Step1Chunk7_3_checked, root6Node123Step1Chunk7_4_checked, root6Node123Step1Chunk7_5_checked, root6Node123Step1Chunk8_0_checked, root6Node123Step1Chunk8_1_checked, root6Node123Step1Chunk8_2_checked, root6Node123Step1Chunk8_3_checked, root6Node123Step1Chunk8_4_checked, root6Node123Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node123Step1_checked :
    checkReplacement table54 root6Node123Domains0 root6Node123Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node123Domains0 root6Node123Domains1
    root6Node123Domains0Fast root6Node123Domains1Fast
    root6Node123Domains0_fast_eq root6Node123Domains1_fast_eq
    root6Node123Step1Narrowing_checked (by decide)
theorem root6Node123Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node123Domains1 (.output 61) = true := by decide
def root6Node124Domains0 : Domains 91 State := restrict root6Node122Domains1 78 (6,3)
def root6Node124Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(4,2)]
  | 13 => some [(6,1)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(3,4)]
  | 21 => some [(2,0)]
  | 22 => some [(7,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(2,3)]
  | 29 => some [(0,2)]
  | 30 => some [(3,1)]
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
theorem root6Node124Domains0_fast_eq : root6Node124Domains0 = expandDomains root6Node124Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node124Domains0 v = expandDomains root6Node124Domains0Fast v from by decide) v
def root6Node124Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(4,3)]
  | 5 => [(7,5)]
  | 6 => [(7,2)]
  | 7 => [(7,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(1,3)]
  | 12 => [(4,2)]
  | 13 => [(6,1)]
  | 14 => [(4,1)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(8,1)]
  | 18 => [(6,5)]
  | 19 => [(0,4)]
  | 20 => [(3,4)]
  | 21 => [(2,0)]
  | 22 => [(7,3)]
  | 23 => [(5,2)]
  | 24 => [(8,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(2,3)]
  | 29 => [(0,2)]
  | 30 => [(3,1)]
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
def root6Node124Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(4,2)]
  | 13 => some [(6,1)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(3,4)]
  | 21 => some [(2,0)]
  | 22 => some [(7,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(2,3)]
  | 29 => some [(0,2)]
  | 30 => some [(3,1)]
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
theorem root6Node124Domains1_fast_eq : root6Node124Domains1 = expandDomains root6Node124Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node124Domains1 v = expandDomains root6Node124Domains1Fast v from by decide) v
theorem root6Node124Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq (by decide)
theorem root6Node124Step1Narrowing_checked :
    checkNarrowing table54 root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root6Node124Domains0 root6Node124Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node124Step1Chunk0_0_checked, root6Node124Step1Chunk0_1_checked, root6Node124Step1Chunk0_2_checked, root6Node124Step1Chunk0_3_checked, root6Node124Step1Chunk0_4_checked, root6Node124Step1Chunk0_5_checked, root6Node124Step1Chunk1_0_checked, root6Node124Step1Chunk1_1_checked, root6Node124Step1Chunk1_2_checked, root6Node124Step1Chunk1_3_checked, root6Node124Step1Chunk1_4_checked, root6Node124Step1Chunk1_5_checked, root6Node124Step1Chunk2_0_checked, root6Node124Step1Chunk2_1_checked, root6Node124Step1Chunk2_2_checked, root6Node124Step1Chunk2_3_checked, root6Node124Step1Chunk2_4_checked, root6Node124Step1Chunk2_5_checked, root6Node124Step1Chunk3_0_checked, root6Node124Step1Chunk3_1_checked, root6Node124Step1Chunk3_2_checked, root6Node124Step1Chunk3_3_checked, root6Node124Step1Chunk3_4_checked, root6Node124Step1Chunk3_5_checked, root6Node124Step1Chunk4_0_checked, root6Node124Step1Chunk4_1_checked, root6Node124Step1Chunk4_2_checked, root6Node124Step1Chunk4_3_checked, root6Node124Step1Chunk4_4_checked, root6Node124Step1Chunk4_5_checked, root6Node124Step1Chunk5_0_checked, root6Node124Step1Chunk5_1_checked, root6Node124Step1Chunk5_2_checked, root6Node124Step1Chunk5_3_checked, root6Node124Step1Chunk5_4_checked, root6Node124Step1Chunk5_5_checked, root6Node124Step1Chunk6_0_checked, root6Node124Step1Chunk6_1_checked, root6Node124Step1Chunk6_2_checked, root6Node124Step1Chunk6_3_checked, root6Node124Step1Chunk6_4_checked, root6Node124Step1Chunk6_5_checked, root6Node124Step1Chunk7_0_checked, root6Node124Step1Chunk7_1_checked, root6Node124Step1Chunk7_2_checked, root6Node124Step1Chunk7_3_checked, root6Node124Step1Chunk7_4_checked, root6Node124Step1Chunk7_5_checked, root6Node124Step1Chunk8_0_checked, root6Node124Step1Chunk8_1_checked, root6Node124Step1Chunk8_2_checked, root6Node124Step1Chunk8_3_checked, root6Node124Step1Chunk8_4_checked, root6Node124Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node124Step1_checked :
    checkReplacement table54 root6Node124Domains0 root6Node124Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node124Domains0 root6Node124Domains1
    root6Node124Domains0Fast root6Node124Domains1Fast
    root6Node124Domains0_fast_eq root6Node124Domains1_fast_eq
    root6Node124Step1Narrowing_checked (by decide)
theorem root6Node124Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node124Domains1 (.output 62) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
