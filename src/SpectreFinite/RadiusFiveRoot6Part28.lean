module

public import SpectreFinite.RadiusFiveRoot6Part27
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable52
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node65Domains0 : Domains 91 State := restrict root6Node63Domains1 78 (6,3)
def root6Node65Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(8,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(2,2)]
  | 22 => some [(3,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(1,5)]
  | 30 => some [(1,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,0)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(1,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(3,1)]
  | 50 => some [(0,1)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
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
theorem root6Node65Domains0_fast_eq : root6Node65Domains0 = expandDomains root6Node65Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node65Domains0 v = expandDomains root6Node65Domains0Fast v from by decide) v
def root6Node65Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(8,3)]
  | 5 => [(8,5)]
  | 6 => [(1,2)]
  | 7 => [(7,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(1,3)]
  | 12 => [(8,2)]
  | 13 => [(0,3)]
  | 14 => [(4,1)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(8,1)]
  | 18 => [(6,5)]
  | 19 => [(0,4)]
  | 20 => [(5,4)]
  | 21 => [(2,2)]
  | 22 => [(3,3)]
  | 23 => [(5,2)]
  | 24 => [(8,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(4,3)]
  | 29 => [(1,5)]
  | 30 => [(1,1)]
  | 31 => [(0,1)]
  | 32 => [(6,2)]
  | 33 => [(8,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(2,0)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(1,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(3,1)]
  | 50 => [(0,1)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(8,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(6,1)]
  | 62 => [(5,1)]
  | 63 => [(0,1)]
  | 64 => [(6,2)]
  | 65 => [(8,4)]
  | 66 => [(6,4)]
  | 67 => [(1,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0)]
  | 70 => [(8,3)]
  | 71 => [(8,5)]
  | 72 => [(1,0)]
  | 73 => [(7,1)]
  | 74 => [(7,5)]
  | 75 => [(0,3)]
  | 76 => [(8,1)]
  | 77 => [(1,5)]
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
def root6Node65Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(8,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(2,2)]
  | 22 => some [(3,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(1,5)]
  | 30 => some [(1,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,0)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(1,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(3,1)]
  | 50 => some [(0,1)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
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
theorem root6Node65Domains1_fast_eq : root6Node65Domains1 = expandDomains root6Node65Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node65Domains1 v = expandDomains root6Node65Domains1Fast v from by decide) v
theorem root6Node65Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq (by decide)
theorem root6Node65Step1Narrowing_checked :
    checkNarrowing table54 root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root6Node65Domains0 root6Node65Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node65Step1Chunk0_0_checked, root6Node65Step1Chunk0_1_checked, root6Node65Step1Chunk0_2_checked, root6Node65Step1Chunk0_3_checked, root6Node65Step1Chunk0_4_checked, root6Node65Step1Chunk0_5_checked, root6Node65Step1Chunk1_0_checked, root6Node65Step1Chunk1_1_checked, root6Node65Step1Chunk1_2_checked, root6Node65Step1Chunk1_3_checked, root6Node65Step1Chunk1_4_checked, root6Node65Step1Chunk1_5_checked, root6Node65Step1Chunk2_0_checked, root6Node65Step1Chunk2_1_checked, root6Node65Step1Chunk2_2_checked, root6Node65Step1Chunk2_3_checked, root6Node65Step1Chunk2_4_checked, root6Node65Step1Chunk2_5_checked, root6Node65Step1Chunk3_0_checked, root6Node65Step1Chunk3_1_checked, root6Node65Step1Chunk3_2_checked, root6Node65Step1Chunk3_3_checked, root6Node65Step1Chunk3_4_checked, root6Node65Step1Chunk3_5_checked, root6Node65Step1Chunk4_0_checked, root6Node65Step1Chunk4_1_checked, root6Node65Step1Chunk4_2_checked, root6Node65Step1Chunk4_3_checked, root6Node65Step1Chunk4_4_checked, root6Node65Step1Chunk4_5_checked, root6Node65Step1Chunk5_0_checked, root6Node65Step1Chunk5_1_checked, root6Node65Step1Chunk5_2_checked, root6Node65Step1Chunk5_3_checked, root6Node65Step1Chunk5_4_checked, root6Node65Step1Chunk5_5_checked, root6Node65Step1Chunk6_0_checked, root6Node65Step1Chunk6_1_checked, root6Node65Step1Chunk6_2_checked, root6Node65Step1Chunk6_3_checked, root6Node65Step1Chunk6_4_checked, root6Node65Step1Chunk6_5_checked, root6Node65Step1Chunk7_0_checked, root6Node65Step1Chunk7_1_checked, root6Node65Step1Chunk7_2_checked, root6Node65Step1Chunk7_3_checked, root6Node65Step1Chunk7_4_checked, root6Node65Step1Chunk7_5_checked, root6Node65Step1Chunk8_0_checked, root6Node65Step1Chunk8_1_checked, root6Node65Step1Chunk8_2_checked, root6Node65Step1Chunk8_3_checked, root6Node65Step1Chunk8_4_checked, root6Node65Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node65Step1_checked :
    checkReplacement table54 root6Node65Domains0 root6Node65Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node65Domains0 root6Node65Domains1
    root6Node65Domains0Fast root6Node65Domains1Fast
    root6Node65Domains0_fast_eq root6Node65Domains1_fast_eq
    root6Node65Step1Narrowing_checked (by decide)
theorem root6Node65Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node65Domains1 (.output 31) = true := by decide
def root6Node66Domains0 : Domains 91 State := restrict root6Node62Domains2 29 (3,5)
def root6Node66Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(8,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(2,2)]
  | 22 => some [(3,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(3,5)]
  | 30 => some [(1,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,0),(2,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(1,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(3,1),(7,1)]
  | 50 => some [(0,1),(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(1,3),(6,3)]
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
theorem root6Node66Domains0_fast_eq : root6Node66Domains0 = expandDomains root6Node66Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node66Domains0 v = expandDomains root6Node66Domains0Fast v from by decide) v
def root6Node66Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(8,3)]
  | 5 => [(8,5)]
  | 6 => [(1,2)]
  | 7 => [(7,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(1,3)]
  | 12 => [(8,2)]
  | 13 => [(0,3)]
  | 14 => [(4,1)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(8,1)]
  | 18 => [(6,5)]
  | 19 => [(0,4)]
  | 20 => [(5,4)]
  | 21 => [(2,2)]
  | 22 => [(3,3)]
  | 23 => [(5,2)]
  | 24 => [(8,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(4,3)]
  | 29 => [(3,5)]
  | 30 => [(1,1)]
  | 31 => [(0,1)]
  | 32 => [(6,2)]
  | 33 => [(8,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(2,4)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(1,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(7,1)]
  | 50 => [(6,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(8,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(6,1)]
  | 62 => [(5,1)]
  | 63 => [(0,1)]
  | 64 => [(6,2)]
  | 65 => [(8,4)]
  | 66 => [(6,4)]
  | 67 => [(1,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0)]
  | 70 => [(8,3)]
  | 71 => [(8,5)]
  | 72 => [(1,0)]
  | 73 => [(7,1)]
  | 74 => [(7,5)]
  | 75 => [(0,3)]
  | 76 => [(8,1)]
  | 77 => [(1,5)]
  | 78 => [(1,3),(6,3)]
  | 79 => [(7,2),(8,2)]
  | 80 => [(4,0)]
  | 81 => [(7,3)]
  | 82 => [(4,2)]
  | 83 => [(5,3)]
  | 84 => [(8,5)]
  | 85 => [(0,4),(1,1)]
  | 86 => [(5,1),(5,4)]
  | 87 => [(0,1)]
  | 88 => [(6,2)]
  | 89 => [(7,4)]
  | _ => [(6,3)]
def root6Node66Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(8,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(2,2)]
  | 22 => some [(3,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(3,5)]
  | 30 => some [(1,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(1,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(1,3),(6,3)]
  | 79 => some [(7,2),(8,2)]
  | 80 => some [(4,0)]
  | 81 => some [(7,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(8,5)]
  | 85 => some [(0,4),(1,1)]
  | 86 => some [(5,1),(5,4)]
  | 87 => some [(0,1)]
  | 88 => some [(6,2)]
  | 89 => some [(7,4)]
  | _ => some [(6,3)]
theorem root6Node66Domains1_fast_eq : root6Node66Domains1 = expandDomains root6Node66Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node66Domains1 v = expandDomains root6Node66Domains1Fast v from by decide) v
theorem root6Node66Step1Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq (by decide)
theorem root6Node66Step1Narrowing_checked :
    checkNarrowing table57 root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root6Node66Domains0 root6Node66Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node66Step1Chunk0_0_checked, root6Node66Step1Chunk0_1_checked, root6Node66Step1Chunk0_2_checked, root6Node66Step1Chunk0_3_checked, root6Node66Step1Chunk0_4_checked, root6Node66Step1Chunk0_5_checked, root6Node66Step1Chunk1_0_checked, root6Node66Step1Chunk1_1_checked, root6Node66Step1Chunk1_2_checked, root6Node66Step1Chunk1_3_checked, root6Node66Step1Chunk1_4_checked, root6Node66Step1Chunk1_5_checked, root6Node66Step1Chunk2_0_checked, root6Node66Step1Chunk2_1_checked, root6Node66Step1Chunk2_2_checked, root6Node66Step1Chunk2_3_checked, root6Node66Step1Chunk2_4_checked, root6Node66Step1Chunk2_5_checked, root6Node66Step1Chunk3_0_checked, root6Node66Step1Chunk3_1_checked, root6Node66Step1Chunk3_2_checked, root6Node66Step1Chunk3_3_checked, root6Node66Step1Chunk3_4_checked, root6Node66Step1Chunk3_5_checked, root6Node66Step1Chunk4_0_checked, root6Node66Step1Chunk4_1_checked, root6Node66Step1Chunk4_2_checked, root6Node66Step1Chunk4_3_checked, root6Node66Step1Chunk4_4_checked, root6Node66Step1Chunk4_5_checked, root6Node66Step1Chunk5_0_checked, root6Node66Step1Chunk5_1_checked, root6Node66Step1Chunk5_2_checked, root6Node66Step1Chunk5_3_checked, root6Node66Step1Chunk5_4_checked, root6Node66Step1Chunk5_5_checked, root6Node66Step1Chunk6_0_checked, root6Node66Step1Chunk6_1_checked, root6Node66Step1Chunk6_2_checked, root6Node66Step1Chunk6_3_checked, root6Node66Step1Chunk6_4_checked, root6Node66Step1Chunk6_5_checked, root6Node66Step1Chunk7_0_checked, root6Node66Step1Chunk7_1_checked, root6Node66Step1Chunk7_2_checked, root6Node66Step1Chunk7_3_checked, root6Node66Step1Chunk7_4_checked, root6Node66Step1Chunk7_5_checked, root6Node66Step1Chunk8_0_checked, root6Node66Step1Chunk8_1_checked, root6Node66Step1Chunk8_2_checked, root6Node66Step1Chunk8_3_checked, root6Node66Step1Chunk8_4_checked, root6Node66Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node66Step1_checked :
    checkReplacement table57 root6Node66Domains0 root6Node66Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node66Domains0 root6Node66Domains1
    root6Node66Domains0Fast root6Node66Domains1Fast
    root6Node66Domains0_fast_eq root6Node66Domains1_fast_eq
    root6Node66Step1Narrowing_checked (by decide)
def root6Node66Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(8,3)]
  | 5 => [(8,5)]
  | 6 => [(1,2)]
  | 7 => [(7,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(1,3)]
  | 12 => [(8,2)]
  | 13 => [(0,3)]
  | 14 => [(4,1)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(8,1)]
  | 18 => [(6,5)]
  | 19 => [(0,4)]
  | 20 => [(5,4)]
  | 21 => [(2,2)]
  | 22 => [(3,3)]
  | 23 => [(5,2)]
  | 24 => [(8,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(4,3)]
  | 29 => [(3,5)]
  | 30 => [(1,1)]
  | 31 => [(0,1)]
  | 32 => [(6,2)]
  | 33 => [(8,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(2,4)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(1,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(7,1)]
  | 50 => [(6,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(8,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(6,1)]
  | 62 => [(5,1)]
  | 63 => [(0,1)]
  | 64 => [(6,2)]
  | 65 => [(8,4)]
  | 66 => [(6,4)]
  | 67 => [(1,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0)]
  | 70 => [(8,3)]
  | 71 => [(8,5)]
  | 72 => [(1,0)]
  | 73 => [(7,1)]
  | 74 => [(7,5)]
  | 75 => [(0,3)]
  | 76 => [(8,1)]
  | 77 => [(1,5)]
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
def root6Node66Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(8,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(2,2)]
  | 22 => some [(3,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(3,5)]
  | 30 => some [(1,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(1,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
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
theorem root6Node66Domains2_fast_eq : root6Node66Domains2 = expandDomains root6Node66Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node66Domains2 v = expandDomains root6Node66Domains2Fast v from by decide) v
theorem root6Node66Step2Chunk0_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_0⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk0_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_1⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk0_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_2⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk0_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_3⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk0_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_4⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk0_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_5⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk1_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_0⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk1_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_1⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk1_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_2⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk1_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_3⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk1_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_4⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk1_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_5⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk2_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_0⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk2_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_1⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk2_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_2⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk2_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_3⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk2_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_4⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk2_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_5⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk3_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_0⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk3_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_1⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk3_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_2⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk3_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_3⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk3_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_4⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk3_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_5⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk4_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_0⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk4_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_1⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk4_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_2⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk4_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_3⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk4_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_4⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk4_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_5⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk5_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_0⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk5_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_1⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk5_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_2⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk5_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_3⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk5_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_4⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk5_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_5⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk6_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_0⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk6_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_1⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk6_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_2⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk6_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_3⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk6_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_4⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk6_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_5⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk7_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_0⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk7_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_1⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk7_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_2⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk7_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_3⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk7_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_4⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk7_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_5⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk8_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_0⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk8_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_1⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk8_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_2⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk8_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_3⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk8_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_4⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Chunk8_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_5⟩
      root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq (by decide)
theorem root6Node66Step2Narrowing_checked :
    checkNarrowing table52 root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkNarrowing_flatten table52Scope [table52Rows0_0,table52Rows0_1,table52Rows0_2,table52Rows0_3,table52Rows0_4,table52Rows0_5,table52Rows1_0,table52Rows1_1,table52Rows1_2,table52Rows1_3,table52Rows1_4,table52Rows1_5,table52Rows2_0,table52Rows2_1,table52Rows2_2,table52Rows2_3,table52Rows2_4,table52Rows2_5,table52Rows3_0,table52Rows3_1,table52Rows3_2,table52Rows3_3,table52Rows3_4,table52Rows3_5,table52Rows4_0,table52Rows4_1,table52Rows4_2,table52Rows4_3,table52Rows4_4,table52Rows4_5,table52Rows5_0,table52Rows5_1,table52Rows5_2,table52Rows5_3,table52Rows5_4,table52Rows5_5,table52Rows6_0,table52Rows6_1,table52Rows6_2,table52Rows6_3,table52Rows6_4,table52Rows6_5,table52Rows7_0,table52Rows7_1,table52Rows7_2,table52Rows7_3,table52Rows7_4,table52Rows7_5,table52Rows8_0,table52Rows8_1,table52Rows8_2,table52Rows8_3,table52Rows8_4,table52Rows8_5]
    root6Node66Domains1 root6Node66Domains2 (by
      simp only [List.all_cons, List.all_nil, root6Node66Step2Chunk0_0_checked, root6Node66Step2Chunk0_1_checked, root6Node66Step2Chunk0_2_checked, root6Node66Step2Chunk0_3_checked, root6Node66Step2Chunk0_4_checked, root6Node66Step2Chunk0_5_checked, root6Node66Step2Chunk1_0_checked, root6Node66Step2Chunk1_1_checked, root6Node66Step2Chunk1_2_checked, root6Node66Step2Chunk1_3_checked, root6Node66Step2Chunk1_4_checked, root6Node66Step2Chunk1_5_checked, root6Node66Step2Chunk2_0_checked, root6Node66Step2Chunk2_1_checked, root6Node66Step2Chunk2_2_checked, root6Node66Step2Chunk2_3_checked, root6Node66Step2Chunk2_4_checked, root6Node66Step2Chunk2_5_checked, root6Node66Step2Chunk3_0_checked, root6Node66Step2Chunk3_1_checked, root6Node66Step2Chunk3_2_checked, root6Node66Step2Chunk3_3_checked, root6Node66Step2Chunk3_4_checked, root6Node66Step2Chunk3_5_checked, root6Node66Step2Chunk4_0_checked, root6Node66Step2Chunk4_1_checked, root6Node66Step2Chunk4_2_checked, root6Node66Step2Chunk4_3_checked, root6Node66Step2Chunk4_4_checked, root6Node66Step2Chunk4_5_checked, root6Node66Step2Chunk5_0_checked, root6Node66Step2Chunk5_1_checked, root6Node66Step2Chunk5_2_checked, root6Node66Step2Chunk5_3_checked, root6Node66Step2Chunk5_4_checked, root6Node66Step2Chunk5_5_checked, root6Node66Step2Chunk6_0_checked, root6Node66Step2Chunk6_1_checked, root6Node66Step2Chunk6_2_checked, root6Node66Step2Chunk6_3_checked, root6Node66Step2Chunk6_4_checked, root6Node66Step2Chunk6_5_checked, root6Node66Step2Chunk7_0_checked, root6Node66Step2Chunk7_1_checked, root6Node66Step2Chunk7_2_checked, root6Node66Step2Chunk7_3_checked, root6Node66Step2Chunk7_4_checked, root6Node66Step2Chunk7_5_checked, root6Node66Step2Chunk8_0_checked, root6Node66Step2Chunk8_1_checked, root6Node66Step2Chunk8_2_checked, root6Node66Step2Chunk8_3_checked, root6Node66Step2Chunk8_4_checked, root6Node66Step2Chunk8_5_checked, Bool.true_and])
theorem root6Node66Step2_checked :
    checkReplacement table52 root6Node66Domains1 root6Node66Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root6Node66Domains1 root6Node66Domains2
    root6Node66Domains1Fast root6Node66Domains2Fast
    root6Node66Domains1_fast_eq root6Node66Domains2_fast_eq
    root6Node66Step2Narrowing_checked (by decide)
theorem root6Node66Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node66Domains2 (.output 32) = true := by decide
def root6Node67Domains0 : Domains 91 State := restrict root6Node61Domains2 21 (2,4)
def root6Node67Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(8,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(2,4)]
  | 22 => some [(1,3),(3,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(1,5),(3,5)]
  | 30 => some [(1,1),(7,1)]
  | 31 => some [(0,1),(6,5)]
  | 32 => some [(0,4),(6,2)]
  | 33 => some [(5,4),(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,0),(2,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(1,0),(7,0)]
  | 43 => some [(4,3),(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(3,1),(7,1)]
  | 50 => some [(0,1),(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0),(7,4)]
  | 54 => some [(1,3),(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1),(8,1)]
  | 63 => some [(0,1),(6,5)]
  | 64 => some [(0,4),(6,2)]
  | 65 => some [(5,4),(8,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0),(7,0)]
  | 73 => some [(4,3),(7,1)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(1,3),(6,3)]
  | 79 => some [(7,2),(8,2)]
  | 80 => some [(4,0),(7,4),(8,0)]
  | 81 => some [(1,3),(7,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(5,5),(8,5)]
  | 85 => some [(0,4),(1,1)]
  | 86 => some [(5,1),(5,4),(8,1)]
  | 87 => some [(0,1),(6,4),(6,5)]
  | 88 => some [(0,4),(1,2),(6,2)]
  | 89 => some [(1,4),(3,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root6Node67Domains0_fast_eq : root6Node67Domains0 = expandDomains root6Node67Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node67Domains0 v = expandDomains root6Node67Domains0Fast v from by decide) v
def root6Node67Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(8,3)]
  | 5 => [(8,5)]
  | 6 => [(1,2)]
  | 7 => [(7,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(1,3)]
  | 12 => [(8,2)]
  | 13 => [(0,3)]
  | 14 => [(4,1)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(8,1)]
  | 18 => [(6,5)]
  | 19 => [(0,4)]
  | 20 => [(5,4)]
  | 21 => [(2,4)]
  | 22 => [(1,3)]
  | 23 => [(5,2)]
  | 24 => [(8,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(4,3)]
  | 29 => [(1,5),(3,5)]
  | 30 => [(7,1)]
  | 31 => [(6,5)]
  | 32 => [(0,4)]
  | 33 => [(5,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(2,0),(2,4)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(4,3)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(3,1),(7,1)]
  | 50 => [(0,1),(6,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3)]
  | 55 => [(8,2)]
  | 56 => [(8,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(6,1)]
  | 62 => [(8,1)]
  | 63 => [(6,5)]
  | 64 => [(0,4)]
  | 65 => [(5,4)]
  | 66 => [(6,4)]
  | 67 => [(1,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0)]
  | 70 => [(8,3)]
  | 71 => [(8,5)]
  | 72 => [(7,0)]
  | 73 => [(4,3)]
  | 74 => [(7,5)]
  | 75 => [(0,3)]
  | 76 => [(8,1)]
  | 77 => [(1,5)]
  | 78 => [(6,3)]
  | 79 => [(7,2)]
  | 80 => [(7,4)]
  | 81 => [(1,3)]
  | 82 => [(4,2)]
  | 83 => [(5,3)]
  | 84 => [(5,5),(8,5)]
  | 85 => [(1,1)]
  | 86 => [(8,1)]
  | 87 => [(6,5)]
  | 88 => [(0,4)]
  | 89 => [(1,4),(3,4),(7,4)]
  | _ => [(0,5),(6,3)]
def root6Node67Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(8,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(2,4)]
  | 22 => some [(1,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(1,5),(3,5)]
  | 30 => some [(7,1)]
  | 31 => some [(6,5)]
  | 32 => some [(0,4)]
  | 33 => some [(5,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,0),(2,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(4,3)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(3,1),(7,1)]
  | 50 => some [(0,1),(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,1)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(5,5),(8,5)]
  | 85 => some [(1,1)]
  | 86 => some [(8,1)]
  | 87 => some [(6,5)]
  | 88 => some [(0,4)]
  | 89 => some [(1,4),(3,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root6Node67Domains1_fast_eq : root6Node67Domains1 = expandDomains root6Node67Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node67Domains1 v = expandDomains root6Node67Domains1Fast v from by decide) v
theorem root6Node67Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq (by decide)
theorem root6Node67Step1Narrowing_checked :
    checkNarrowing table54 root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root6Node67Domains0 root6Node67Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node67Step1Chunk0_0_checked, root6Node67Step1Chunk0_1_checked, root6Node67Step1Chunk0_2_checked, root6Node67Step1Chunk0_3_checked, root6Node67Step1Chunk0_4_checked, root6Node67Step1Chunk0_5_checked, root6Node67Step1Chunk1_0_checked, root6Node67Step1Chunk1_1_checked, root6Node67Step1Chunk1_2_checked, root6Node67Step1Chunk1_3_checked, root6Node67Step1Chunk1_4_checked, root6Node67Step1Chunk1_5_checked, root6Node67Step1Chunk2_0_checked, root6Node67Step1Chunk2_1_checked, root6Node67Step1Chunk2_2_checked, root6Node67Step1Chunk2_3_checked, root6Node67Step1Chunk2_4_checked, root6Node67Step1Chunk2_5_checked, root6Node67Step1Chunk3_0_checked, root6Node67Step1Chunk3_1_checked, root6Node67Step1Chunk3_2_checked, root6Node67Step1Chunk3_3_checked, root6Node67Step1Chunk3_4_checked, root6Node67Step1Chunk3_5_checked, root6Node67Step1Chunk4_0_checked, root6Node67Step1Chunk4_1_checked, root6Node67Step1Chunk4_2_checked, root6Node67Step1Chunk4_3_checked, root6Node67Step1Chunk4_4_checked, root6Node67Step1Chunk4_5_checked, root6Node67Step1Chunk5_0_checked, root6Node67Step1Chunk5_1_checked, root6Node67Step1Chunk5_2_checked, root6Node67Step1Chunk5_3_checked, root6Node67Step1Chunk5_4_checked, root6Node67Step1Chunk5_5_checked, root6Node67Step1Chunk6_0_checked, root6Node67Step1Chunk6_1_checked, root6Node67Step1Chunk6_2_checked, root6Node67Step1Chunk6_3_checked, root6Node67Step1Chunk6_4_checked, root6Node67Step1Chunk6_5_checked, root6Node67Step1Chunk7_0_checked, root6Node67Step1Chunk7_1_checked, root6Node67Step1Chunk7_2_checked, root6Node67Step1Chunk7_3_checked, root6Node67Step1Chunk7_4_checked, root6Node67Step1Chunk7_5_checked, root6Node67Step1Chunk8_0_checked, root6Node67Step1Chunk8_1_checked, root6Node67Step1Chunk8_2_checked, root6Node67Step1Chunk8_3_checked, root6Node67Step1Chunk8_4_checked, root6Node67Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node67Step1_checked :
    checkReplacement table54 root6Node67Domains0 root6Node67Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node67Domains0 root6Node67Domains1
    root6Node67Domains0Fast root6Node67Domains1Fast
    root6Node67Domains0_fast_eq root6Node67Domains1_fast_eq
    root6Node67Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
