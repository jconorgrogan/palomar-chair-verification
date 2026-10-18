module

public import SpectreFinite.RadiusFiveRoot0Part11
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
def root0Node23Domains0 : Domains 91 State := restrict root0Node22Domains1 85 (5,5)
def root0Node23Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 85 => some [(5,5)]
  | 86 => some [(7,0)]
  | 87 => some [(8,3)]
  | 88 => some [(5,5),(8,5)]
  | 89 => some [(7,0)]
  | _ => some [(4,3)]
theorem root0Node23Domains0_fast_eq : root0Node23Domains0 = expandDomains root0Node23Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node23Domains0 v = expandDomains root0Node23Domains0Fast v from by decide) v
def root0Node23Domains1 (v : Fin 91) : List State :=
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
  | 85 => [(5,5)]
  | 86 => [(7,0)]
  | 87 => [(8,3)]
  | 88 => [(5,5)]
  | 89 => [(7,0)]
  | _ => [(4,3)]
def root0Node23Domains1Fast (v : Fin 91) : Option (List State) :=
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
  | 85 => some [(5,5)]
  | 86 => some [(7,0)]
  | 87 => some [(8,3)]
  | 88 => some [(5,5)]
  | 89 => some [(7,0)]
  | _ => some [(4,3)]
theorem root0Node23Domains1_fast_eq : root0Node23Domains1 = expandDomains root0Node23Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node23Domains1 v = expandDomains root0Node23Domains1Fast v from by decide) v
theorem root0Node23Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Narrowing_checked :
    checkNarrowing table54 root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root0Node23Domains0 root0Node23Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node23Step1Chunk0_0_checked, root0Node23Step1Chunk0_1_checked, root0Node23Step1Chunk0_2_checked, root0Node23Step1Chunk0_3_checked, root0Node23Step1Chunk0_4_checked, root0Node23Step1Chunk0_5_checked, root0Node23Step1Chunk1_0_checked, root0Node23Step1Chunk1_1_checked, root0Node23Step1Chunk1_2_checked, root0Node23Step1Chunk1_3_checked, root0Node23Step1Chunk1_4_checked, root0Node23Step1Chunk1_5_checked, root0Node23Step1Chunk2_0_checked, root0Node23Step1Chunk2_1_checked, root0Node23Step1Chunk2_2_checked, root0Node23Step1Chunk2_3_checked, root0Node23Step1Chunk2_4_checked, root0Node23Step1Chunk2_5_checked, root0Node23Step1Chunk3_0_checked, root0Node23Step1Chunk3_1_checked, root0Node23Step1Chunk3_2_checked, root0Node23Step1Chunk3_3_checked, root0Node23Step1Chunk3_4_checked, root0Node23Step1Chunk3_5_checked, root0Node23Step1Chunk4_0_checked, root0Node23Step1Chunk4_1_checked, root0Node23Step1Chunk4_2_checked, root0Node23Step1Chunk4_3_checked, root0Node23Step1Chunk4_4_checked, root0Node23Step1Chunk4_5_checked, root0Node23Step1Chunk5_0_checked, root0Node23Step1Chunk5_1_checked, root0Node23Step1Chunk5_2_checked, root0Node23Step1Chunk5_3_checked, root0Node23Step1Chunk5_4_checked, root0Node23Step1Chunk5_5_checked, root0Node23Step1Chunk6_0_checked, root0Node23Step1Chunk6_1_checked, root0Node23Step1Chunk6_2_checked, root0Node23Step1Chunk6_3_checked, root0Node23Step1Chunk6_4_checked, root0Node23Step1Chunk6_5_checked, root0Node23Step1Chunk7_0_checked, root0Node23Step1Chunk7_1_checked, root0Node23Step1Chunk7_2_checked, root0Node23Step1Chunk7_3_checked, root0Node23Step1Chunk7_4_checked, root0Node23Step1Chunk7_5_checked, root0Node23Step1Chunk8_0_checked, root0Node23Step1Chunk8_1_checked, root0Node23Step1Chunk8_2_checked, root0Node23Step1Chunk8_3_checked, root0Node23Step1Chunk8_4_checked, root0Node23Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node23Step1_checked :
    checkReplacement table54 root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq
    root0Node23Step1Narrowing_checked (by decide)
theorem root0Node23Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node23Domains1 (.output 10) = true := by decide
def root0Node24Domains0 : Domains 91 State := restrict root0Node22Domains1 85 (8,5)
def root0Node24Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 85 => some [(8,5)]
  | 86 => some [(7,0)]
  | 87 => some [(8,3)]
  | 88 => some [(5,5),(8,5)]
  | 89 => some [(7,0)]
  | _ => some [(4,3)]
theorem root0Node24Domains0_fast_eq : root0Node24Domains0 = expandDomains root0Node24Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node24Domains0 v = expandDomains root0Node24Domains0Fast v from by decide) v
def root0Node24Domains1 (v : Fin 91) : List State :=
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
  | 85 => [(8,5)]
  | 86 => [(7,0)]
  | 87 => [(8,3)]
  | 88 => [(8,5)]
  | 89 => [(7,0)]
  | _ => [(4,3)]
def root0Node24Domains1Fast (v : Fin 91) : Option (List State) :=
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
  | 85 => some [(8,5)]
  | 86 => some [(7,0)]
  | 87 => some [(8,3)]
  | 88 => some [(8,5)]
  | 89 => some [(7,0)]
  | _ => some [(4,3)]
theorem root0Node24Domains1_fast_eq : root0Node24Domains1 = expandDomains root0Node24Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node24Domains1 v = expandDomains root0Node24Domains1Fast v from by decide) v
theorem root0Node24Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Narrowing_checked :
    checkNarrowing table54 root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root0Node24Domains0 root0Node24Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node24Step1Chunk0_0_checked, root0Node24Step1Chunk0_1_checked, root0Node24Step1Chunk0_2_checked, root0Node24Step1Chunk0_3_checked, root0Node24Step1Chunk0_4_checked, root0Node24Step1Chunk0_5_checked, root0Node24Step1Chunk1_0_checked, root0Node24Step1Chunk1_1_checked, root0Node24Step1Chunk1_2_checked, root0Node24Step1Chunk1_3_checked, root0Node24Step1Chunk1_4_checked, root0Node24Step1Chunk1_5_checked, root0Node24Step1Chunk2_0_checked, root0Node24Step1Chunk2_1_checked, root0Node24Step1Chunk2_2_checked, root0Node24Step1Chunk2_3_checked, root0Node24Step1Chunk2_4_checked, root0Node24Step1Chunk2_5_checked, root0Node24Step1Chunk3_0_checked, root0Node24Step1Chunk3_1_checked, root0Node24Step1Chunk3_2_checked, root0Node24Step1Chunk3_3_checked, root0Node24Step1Chunk3_4_checked, root0Node24Step1Chunk3_5_checked, root0Node24Step1Chunk4_0_checked, root0Node24Step1Chunk4_1_checked, root0Node24Step1Chunk4_2_checked, root0Node24Step1Chunk4_3_checked, root0Node24Step1Chunk4_4_checked, root0Node24Step1Chunk4_5_checked, root0Node24Step1Chunk5_0_checked, root0Node24Step1Chunk5_1_checked, root0Node24Step1Chunk5_2_checked, root0Node24Step1Chunk5_3_checked, root0Node24Step1Chunk5_4_checked, root0Node24Step1Chunk5_5_checked, root0Node24Step1Chunk6_0_checked, root0Node24Step1Chunk6_1_checked, root0Node24Step1Chunk6_2_checked, root0Node24Step1Chunk6_3_checked, root0Node24Step1Chunk6_4_checked, root0Node24Step1Chunk6_5_checked, root0Node24Step1Chunk7_0_checked, root0Node24Step1Chunk7_1_checked, root0Node24Step1Chunk7_2_checked, root0Node24Step1Chunk7_3_checked, root0Node24Step1Chunk7_4_checked, root0Node24Step1Chunk7_5_checked, root0Node24Step1Chunk8_0_checked, root0Node24Step1Chunk8_1_checked, root0Node24Step1Chunk8_2_checked, root0Node24Step1Chunk8_3_checked, root0Node24Step1Chunk8_4_checked, root0Node24Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node24Step1_checked :
    checkReplacement table54 root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq
    root0Node24Step1Narrowing_checked (by decide)
theorem root0Node24Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node24Domains1 (.output 11) = true := by decide
def root0Node25Domains0 : Domains 91 State := restrict root0Node21Domains1 70 (6,2)
def root0Node25Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 70 => some [(6,2)]
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
theorem root0Node25Domains0_fast_eq : root0Node25Domains0 = expandDomains root0Node25Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node25Domains0 v = expandDomains root0Node25Domains0Fast v from by decide) v
def root0Node25Domains1 (v : Fin 91) : List State :=
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
  | 70 => [(6,2)]
  | 71 => [(8,4)]
  | 72 => [(0,0)]
  | 73 => [(7,2)]
  | 74 => [(7,4)]
  | 75 => [(1,3)]
  | 76 => [(8,2)]
  | 77 => [(8,0)]
  | 78 => [(7,1)]
  | 79 => [(1,5)]
  | 80 => [(6,1)]
  | 81 => [(8,1)]
  | 82 => [(6,5)]
  | 83 => [(0,4)]
  | 84 => [(5,4)]
  | 85 => [(4,5)]
  | 86 => [(7,0)]
  | 87 => [(8,3)]
  | 88 => [(8,5)]
  | 89 => [(7,0)]
  | _ => [(4,3)]
def root0Node25Domains1Fast (v : Fin 91) : Option (List State) :=
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
  | 70 => some [(6,2)]
  | 71 => some [(8,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3)]
  | 76 => some [(8,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(8,1)]
  | 82 => some [(6,5)]
  | 83 => some [(0,4)]
  | 84 => some [(5,4)]
  | 85 => some [(4,5)]
  | 86 => some [(7,0)]
  | 87 => some [(8,3)]
  | 88 => some [(8,5)]
  | 89 => some [(7,0)]
  | _ => some [(4,3)]
theorem root0Node25Domains1_fast_eq : root0Node25Domains1 = expandDomains root0Node25Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node25Domains1 v = expandDomains root0Node25Domains1Fast v from by decide) v
theorem root0Node25Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Narrowing_checked :
    checkNarrowing table54 root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root0Node25Domains0 root0Node25Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node25Step1Chunk0_0_checked, root0Node25Step1Chunk0_1_checked, root0Node25Step1Chunk0_2_checked, root0Node25Step1Chunk0_3_checked, root0Node25Step1Chunk0_4_checked, root0Node25Step1Chunk0_5_checked, root0Node25Step1Chunk1_0_checked, root0Node25Step1Chunk1_1_checked, root0Node25Step1Chunk1_2_checked, root0Node25Step1Chunk1_3_checked, root0Node25Step1Chunk1_4_checked, root0Node25Step1Chunk1_5_checked, root0Node25Step1Chunk2_0_checked, root0Node25Step1Chunk2_1_checked, root0Node25Step1Chunk2_2_checked, root0Node25Step1Chunk2_3_checked, root0Node25Step1Chunk2_4_checked, root0Node25Step1Chunk2_5_checked, root0Node25Step1Chunk3_0_checked, root0Node25Step1Chunk3_1_checked, root0Node25Step1Chunk3_2_checked, root0Node25Step1Chunk3_3_checked, root0Node25Step1Chunk3_4_checked, root0Node25Step1Chunk3_5_checked, root0Node25Step1Chunk4_0_checked, root0Node25Step1Chunk4_1_checked, root0Node25Step1Chunk4_2_checked, root0Node25Step1Chunk4_3_checked, root0Node25Step1Chunk4_4_checked, root0Node25Step1Chunk4_5_checked, root0Node25Step1Chunk5_0_checked, root0Node25Step1Chunk5_1_checked, root0Node25Step1Chunk5_2_checked, root0Node25Step1Chunk5_3_checked, root0Node25Step1Chunk5_4_checked, root0Node25Step1Chunk5_5_checked, root0Node25Step1Chunk6_0_checked, root0Node25Step1Chunk6_1_checked, root0Node25Step1Chunk6_2_checked, root0Node25Step1Chunk6_3_checked, root0Node25Step1Chunk6_4_checked, root0Node25Step1Chunk6_5_checked, root0Node25Step1Chunk7_0_checked, root0Node25Step1Chunk7_1_checked, root0Node25Step1Chunk7_2_checked, root0Node25Step1Chunk7_3_checked, root0Node25Step1Chunk7_4_checked, root0Node25Step1Chunk7_5_checked, root0Node25Step1Chunk8_0_checked, root0Node25Step1Chunk8_1_checked, root0Node25Step1Chunk8_2_checked, root0Node25Step1Chunk8_3_checked, root0Node25Step1Chunk8_4_checked, root0Node25Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node25Step1_checked :
    checkReplacement table54 root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq
    root0Node25Step1Narrowing_checked (by decide)
theorem root0Node25Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node25Domains1 (.output 12) = true := by decide
def root0Node26Domains0 : Domains 91 State := restrict root0Node12Domains2 34 (5,0)
def root0Node26Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0),(6,5)]
  | 1 => some [(0,4),(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 3 => some [(0,0),(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 4 => some [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 5 => some [(0,1),(1,4),(1,5),(6,5),(7,4),(8,4)]
  | 6 => some [(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,5)]
  | 7 => some [(4,0),(7,0),(8,0)]
  | 8 => some [(4,3),(7,3),(8,3)]
  | 9 => some [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 10 => some [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 11 => some [(2,1),(2,5),(4,1),(4,5),(8,1)]
  | 12 => some [(0,2),(1,0),(1,5),(6,0),(6,5),(7,0)]
  | 13 => some [(0,0),(0,3),(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 14 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 15 => some [(0,1),(1,4),(7,4)]
  | 16 => some [(0,5),(1,3),(6,2),(6,3)]
  | 17 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(8,4)]
  | 18 => some [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 19 => some [(3,2),(5,2),(5,5),(7,2)]
  | 20 => some [(4,0),(7,0),(7,4),(8,0)]
  | 21 => some [(0,2),(1,0),(1,5),(4,2),(6,0),(7,0)]
  | 22 => some [(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 23 => some [(4,1),(7,5),(8,1),(8,5)]
  | 24 => some [(0,2),(1,0),(6,0),(6,5)]
  | 25 => some [(0,4),(1,1),(3,1),(7,1)]
  | 26 => some [(0,1),(1,4),(1,5),(6,5)]
  | 27 => some [(0,4),(0,5),(6,1),(6,2)]
  | 28 => some [(4,4),(5,1),(5,4),(8,1),(8,4)]
  | 29 => some [(0,1),(1,4),(6,4),(6,5)]
  | 30 => some [(1,2),(3,2),(5,2),(5,5),(7,2),(8,2)]
  | 31 => some [(4,0),(7,0),(7,4),(8,0)]
  | 32 => some [(1,3),(7,3),(8,3)]
  | 33 => some [(5,2),(5,5),(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(2,5),(4,5)]
  | 36 => some [(1,0),(6,0),(7,0)]
  | 37 => some [(4,3),(7,1),(8,3)]
  | 38 => some [(7,5),(8,5)]
  | 39 => some [(0,3),(1,0),(6,0),(7,0)]
  | 40 => some [(0,3),(0,4),(0,5),(1,1),(6,1),(6,2)]
  | 41 => some [(4,4),(5,1),(5,4),(8,1),(8,4)]
  | 42 => some [(0,1),(1,4),(6,4),(6,5)]
  | 43 => some [(0,4),(0,5),(1,2),(6,2)]
  | 44 => some [(4,4),(5,4),(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0),(7,4)]
  | 48 => some [(1,3),(6,3),(7,3)]
  | 49 => some [(4,2),(7,2),(8,2)]
  | 50 => some [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 51 => some [(4,3),(5,3),(7,1),(8,3)]
  | 52 => some [(5,5),(7,5),(8,5)]
  | 53 => some [(0,3),(1,0),(6,0),(7,0)]
  | 54 => some [(4,3),(7,1),(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(4,1),(5,1),(8,1)]
  | 58 => some [(0,1),(0,2),(6,5)]
  | 59 => some [(0,4),(1,1),(6,2)]
  | 60 => some [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(8,1),(8,4)]
  | 61 => some [(0,5),(1,3),(7,3)]
  | 62 => some [(4,2),(4,4),(8,2)]
  | 63 => some [(1,4),(5,0),(5,3)]
  | 64 => some [(0,5),(4,5),(5,5),(8,5)]
  | 65 => some [(2,0),(7,0)]
  | 66 => some [(7,3),(8,3)]
  | 67 => some [(5,2),(5,5),(8,5)]
  | 68 => some [(1,0),(3,0),(7,0),(8,0)]
  | 69 => some [(2,1),(2,3),(2,5),(4,3),(7,1),(7,3),(8,3)]
  | 70 => some [(0,4),(1,2),(6,2),(7,1)]
  | 71 => some [(1,4),(3,4),(5,4),(7,4),(7,5),(8,4)]
  | 72 => some [(0,0),(0,5),(6,0),(6,3)]
  | 73 => some [(3,1),(4,4),(7,2)]
  | 74 => some [(0,1),(1,4),(7,4)]
  | 75 => some [(0,5),(1,3),(6,2),(6,3)]
  | 76 => some [(4,4),(7,2),(8,2),(8,4)]
  | 77 => some [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 78 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(7,3),(8,1)]
  | 79 => some [(0,2),(1,5),(6,0),(8,2)]
  | 80 => some [(1,1),(5,0),(6,1),(7,1)]
  | 81 => some [(4,1),(4,5),(7,5),(8,1)]
  | 82 => some [(0,2),(1,0),(6,0),(6,5)]
  | 83 => some [(0,4),(1,1),(7,1)]
  | 84 => some [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 85 => some [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(6,2),(7,2),(8,5)]
  | 86 => some [(2,0),(4,0),(7,0),(8,0),(8,4)]
  | 87 => some [(0,0),(7,3),(8,3)]
  | 88 => some [(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 89 => some [(4,0),(5,0),(7,0),(8,0)]
  | _ => some [(4,3),(4,5),(7,3),(8,3)]
theorem root0Node26Domains0_fast_eq : root0Node26Domains0 = expandDomains root0Node26Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node26Domains0 v = expandDomains root0Node26Domains0Fast v from by decide) v
def root0Node26Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(1,5),(6,0),(6,5)]
  | 1 => [(0,4),(1,1),(6,1),(7,1)]
  | 2 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 3 => [(0,0),(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 4 => [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 5 => [(0,1),(1,4),(1,5),(6,5),(7,4),(8,4)]
  | 6 => [(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,5)]
  | 7 => [(4,0),(7,0),(8,0)]
  | 8 => [(4,3),(7,3),(8,3)]
  | 9 => [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 10 => [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 11 => [(2,1),(2,5),(4,1),(4,5),(8,1)]
  | 12 => [(0,2),(1,0),(1,5),(6,0),(6,5),(7,0)]
  | 13 => [(0,3),(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 14 => [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 15 => [(0,1),(1,4),(7,4)]
  | 16 => [(0,5),(6,2),(6,3)]
  | 17 => [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 18 => [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 19 => [(3,2),(5,2),(5,5),(7,2)]
  | 20 => [(4,0),(7,0),(7,4),(8,0)]
  | 21 => [(0,2),(1,0),(4,2),(6,0),(7,0)]
  | 22 => [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 23 => [(4,1),(7,5),(8,5)]
  | 24 => [(0,2),(1,0),(6,0)]
  | 25 => [(1,1),(3,1),(7,1)]
  | 26 => [(0,1),(1,5),(6,5)]
  | 27 => [(0,4),(0,5),(6,1),(6,2)]
  | 28 => [(4,4),(5,1),(5,4),(8,1),(8,4)]
  | 29 => [(0,1),(1,4),(6,4),(6,5)]
  | 30 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 31 => [(4,0),(7,4),(8,0)]
  | 32 => [(1,3),(7,3)]
  | 33 => [(5,2),(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(1,0),(7,0)]
  | 37 => [(4,3),(7,1),(8,3)]
  | 38 => [(7,5),(8,5)]
  | 39 => [(0,3),(1,0),(6,0),(7,0)]
  | 40 => [(0,3),(0,4),(1,1),(6,1),(6,2)]
  | 41 => [(5,1),(5,4),(8,1),(8,4)]
  | 42 => [(0,1),(6,4),(6,5)]
  | 43 => [(0,4),(1,2),(6,2)]
  | 44 => [(5,4),(8,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(4,0),(7,4)]
  | 48 => [(1,3),(6,3),(7,3)]
  | 49 => [(4,2),(7,2),(8,2)]
  | 50 => [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 51 => [(4,3),(5,3),(7,1),(8,3)]
  | 52 => [(5,5),(7,5),(8,5)]
  | 53 => [(0,3),(1,0),(7,0)]
  | 54 => [(4,3),(7,1),(8,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(4,1),(5,1),(8,1)]
  | 58 => [(0,1),(0,2),(6,5)]
  | 59 => [(0,4),(1,1),(6,2)]
  | 60 => [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(8,1),(8,4)]
  | 61 => [(0,5),(1,3),(7,3)]
  | 62 => [(4,2),(4,4),(8,2)]
  | 63 => [(1,4),(5,0),(5,3)]
  | 64 => [(0,5),(4,5),(5,5),(8,5)]
  | 65 => [(2,0),(7,0)]
  | 66 => [(7,3),(8,3)]
  | 67 => [(5,2),(5,5),(8,5)]
  | 68 => [(1,0),(3,0),(7,0),(8,0)]
  | 69 => [(2,1),(2,3),(2,5),(4,3),(7,1),(7,3),(8,3)]
  | 70 => [(0,4),(1,2),(6,2),(7,1)]
  | 71 => [(1,4),(3,4),(5,4),(7,4),(7,5)]
  | 72 => [(0,0),(0,5),(6,0),(6,3)]
  | 73 => [(3,1),(4,4),(7,2)]
  | 74 => [(0,1),(1,4),(7,4)]
  | 75 => [(0,5),(1,3),(6,2),(6,3)]
  | 76 => [(4,4),(7,2),(8,2),(8,4)]
  | 77 => [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 78 => [(2,1),(2,3),(2,5),(4,1),(4,3),(7,3)]
  | 79 => [(0,2),(1,5),(6,0),(8,2)]
  | 80 => [(1,1),(5,0),(6,1),(7,1)]
  | 81 => [(4,1),(4,5),(7,5),(8,1)]
  | 82 => [(0,2),(1,0),(6,0),(6,5)]
  | 83 => [(0,4),(1,1),(7,1)]
  | 84 => [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 85 => [(0,5),(1,2),(3,2),(5,2),(6,2),(7,2)]
  | 86 => [(2,0),(4,0),(8,0),(8,4)]
  | 87 => [(0,0),(7,3),(8,3)]
  | 88 => [(5,2),(5,5),(7,2),(8,2)]
  | 89 => [(4,0),(5,0),(7,0),(8,0)]
  | _ => [(4,3),(4,5),(7,3),(8,3)]
def root0Node26Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0),(6,5)]
  | 1 => some [(0,4),(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 3 => some [(0,0),(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 4 => some [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 5 => some [(0,1),(1,4),(1,5),(6,5),(7,4),(8,4)]
  | 6 => some [(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,5)]
  | 7 => some [(4,0),(7,0),(8,0)]
  | 8 => some [(4,3),(7,3),(8,3)]
  | 9 => some [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 10 => some [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 11 => some [(2,1),(2,5),(4,1),(4,5),(8,1)]
  | 12 => some [(0,2),(1,0),(1,5),(6,0),(6,5),(7,0)]
  | 13 => some [(0,3),(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 14 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 15 => some [(0,1),(1,4),(7,4)]
  | 16 => some [(0,5),(6,2),(6,3)]
  | 17 => some [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 18 => some [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 19 => some [(3,2),(5,2),(5,5),(7,2)]
  | 20 => some [(4,0),(7,0),(7,4),(8,0)]
  | 21 => some [(0,2),(1,0),(4,2),(6,0),(7,0)]
  | 22 => some [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 23 => some [(4,1),(7,5),(8,5)]
  | 24 => some [(0,2),(1,0),(6,0)]
  | 25 => some [(1,1),(3,1),(7,1)]
  | 26 => some [(0,1),(1,5),(6,5)]
  | 27 => some [(0,4),(0,5),(6,1),(6,2)]
  | 28 => some [(4,4),(5,1),(5,4),(8,1),(8,4)]
  | 29 => some [(0,1),(1,4),(6,4),(6,5)]
  | 30 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 31 => some [(4,0),(7,4),(8,0)]
  | 32 => some [(1,3),(7,3)]
  | 33 => some [(5,2),(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(1,0),(7,0)]
  | 37 => some [(4,3),(7,1),(8,3)]
  | 38 => some [(7,5),(8,5)]
  | 39 => some [(0,3),(1,0),(6,0),(7,0)]
  | 40 => some [(0,3),(0,4),(1,1),(6,1),(6,2)]
  | 41 => some [(5,1),(5,4),(8,1),(8,4)]
  | 42 => some [(0,1),(6,4),(6,5)]
  | 43 => some [(0,4),(1,2),(6,2)]
  | 44 => some [(5,4),(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0),(7,4)]
  | 48 => some [(1,3),(6,3),(7,3)]
  | 49 => some [(4,2),(7,2),(8,2)]
  | 50 => some [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 51 => some [(4,3),(5,3),(7,1),(8,3)]
  | 52 => some [(5,5),(7,5),(8,5)]
  | 53 => some [(0,3),(1,0),(7,0)]
  | 54 => some [(4,3),(7,1),(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(4,1),(5,1),(8,1)]
  | 58 => some [(0,1),(0,2),(6,5)]
  | 59 => some [(0,4),(1,1),(6,2)]
  | 60 => some [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(8,1),(8,4)]
  | 61 => some [(0,5),(1,3),(7,3)]
  | 62 => some [(4,2),(4,4),(8,2)]
  | 63 => some [(1,4),(5,0),(5,3)]
  | 64 => some [(0,5),(4,5),(5,5),(8,5)]
  | 65 => some [(2,0),(7,0)]
  | 66 => some [(7,3),(8,3)]
  | 67 => some [(5,2),(5,5),(8,5)]
  | 68 => some [(1,0),(3,0),(7,0),(8,0)]
  | 69 => some [(2,1),(2,3),(2,5),(4,3),(7,1),(7,3),(8,3)]
  | 70 => some [(0,4),(1,2),(6,2),(7,1)]
  | 71 => some [(1,4),(3,4),(5,4),(7,4),(7,5)]
  | 72 => some [(0,0),(0,5),(6,0),(6,3)]
  | 73 => some [(3,1),(4,4),(7,2)]
  | 74 => some [(0,1),(1,4),(7,4)]
  | 75 => some [(0,5),(1,3),(6,2),(6,3)]
  | 76 => some [(4,4),(7,2),(8,2),(8,4)]
  | 77 => some [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 78 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,3)]
  | 79 => some [(0,2),(1,5),(6,0),(8,2)]
  | 80 => some [(1,1),(5,0),(6,1),(7,1)]
  | 81 => some [(4,1),(4,5),(7,5),(8,1)]
  | 82 => some [(0,2),(1,0),(6,0),(6,5)]
  | 83 => some [(0,4),(1,1),(7,1)]
  | 84 => some [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 85 => some [(0,5),(1,2),(3,2),(5,2),(6,2),(7,2)]
  | 86 => some [(2,0),(4,0),(8,0),(8,4)]
  | 87 => some [(0,0),(7,3),(8,3)]
  | 88 => some [(5,2),(5,5),(7,2),(8,2)]
  | 89 => some [(4,0),(5,0),(7,0),(8,0)]
  | _ => some [(4,3),(4,5),(7,3),(8,3)]
theorem root0Node26Domains1_fast_eq : root0Node26Domains1 = expandDomains root0Node26Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node26Domains1 v = expandDomains root0Node26Domains1Fast v from by decide) v
theorem root0Node26Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq (by decide)
theorem root0Node26Step1Narrowing_checked :
    checkNarrowing table54 root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root0Node26Domains0 root0Node26Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node26Step1Chunk0_0_checked, root0Node26Step1Chunk0_1_checked, root0Node26Step1Chunk0_2_checked, root0Node26Step1Chunk0_3_checked, root0Node26Step1Chunk0_4_checked, root0Node26Step1Chunk0_5_checked, root0Node26Step1Chunk1_0_checked, root0Node26Step1Chunk1_1_checked, root0Node26Step1Chunk1_2_checked, root0Node26Step1Chunk1_3_checked, root0Node26Step1Chunk1_4_checked, root0Node26Step1Chunk1_5_checked, root0Node26Step1Chunk2_0_checked, root0Node26Step1Chunk2_1_checked, root0Node26Step1Chunk2_2_checked, root0Node26Step1Chunk2_3_checked, root0Node26Step1Chunk2_4_checked, root0Node26Step1Chunk2_5_checked, root0Node26Step1Chunk3_0_checked, root0Node26Step1Chunk3_1_checked, root0Node26Step1Chunk3_2_checked, root0Node26Step1Chunk3_3_checked, root0Node26Step1Chunk3_4_checked, root0Node26Step1Chunk3_5_checked, root0Node26Step1Chunk4_0_checked, root0Node26Step1Chunk4_1_checked, root0Node26Step1Chunk4_2_checked, root0Node26Step1Chunk4_3_checked, root0Node26Step1Chunk4_4_checked, root0Node26Step1Chunk4_5_checked, root0Node26Step1Chunk5_0_checked, root0Node26Step1Chunk5_1_checked, root0Node26Step1Chunk5_2_checked, root0Node26Step1Chunk5_3_checked, root0Node26Step1Chunk5_4_checked, root0Node26Step1Chunk5_5_checked, root0Node26Step1Chunk6_0_checked, root0Node26Step1Chunk6_1_checked, root0Node26Step1Chunk6_2_checked, root0Node26Step1Chunk6_3_checked, root0Node26Step1Chunk6_4_checked, root0Node26Step1Chunk6_5_checked, root0Node26Step1Chunk7_0_checked, root0Node26Step1Chunk7_1_checked, root0Node26Step1Chunk7_2_checked, root0Node26Step1Chunk7_3_checked, root0Node26Step1Chunk7_4_checked, root0Node26Step1Chunk7_5_checked, root0Node26Step1Chunk8_0_checked, root0Node26Step1Chunk8_1_checked, root0Node26Step1Chunk8_2_checked, root0Node26Step1Chunk8_3_checked, root0Node26Step1Chunk8_4_checked, root0Node26Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node26Step1_checked :
    checkReplacement table54 root0Node26Domains0 root0Node26Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node26Domains0 root0Node26Domains1
    root0Node26Domains0Fast root0Node26Domains1Fast
    root0Node26Domains0_fast_eq root0Node26Domains1_fast_eq
    root0Node26Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
