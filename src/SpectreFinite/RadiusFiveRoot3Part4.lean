module

public import SpectreFinite.RadiusFiveRoot3Part3
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root3Node8Domains0 : Domains 91 State := restrict root3Node7Domains1 40 (1,3)
def root3Node8Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,3)]
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3)]
  | 19 => some [(8,1)]
  | 20 => some [(1,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2)]
  | 27 => some [(5,3)]
  | 28 => some [(5,5)]
  | 29 => some [(7,0)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(1,4)]
  | 40 => some [(1,3)]
  | 41 => some [(5,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(3,0)]
  | 46 => some [(2,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(6,0)]
  | 51 => some [(0,4),(6,2)]
  | 52 => some [(5,4),(8,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(8,2)]
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
  | 78 => some [(0,4),(6,2)]
  | 79 => some [(5,4),(8,4)]
  | 80 => some [(0,0)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(1,3),(6,3)]
  | 84 => some [(7,2),(8,2)]
  | 85 => some [(4,3),(7,1)]
  | 86 => some [(1,5)]
  | 87 => some [(6,1)]
  | 88 => some [(4,1),(8,1)]
  | 89 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root3Node8Domains0_fast_eq : root3Node8Domains0 = expandDomains root3Node8Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root3Node8Domains0 v = expandDomains root3Node8Domains0Fast v from by decide) v
def root3Node8Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3)]
  | 5 => [(8,2)]
  | 6 => [(8,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(6,4)]
  | 11 => [(1,2)]
  | 12 => [(8,4)]
  | 13 => [(5,3)]
  | 14 => [(8,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(0,3)]
  | 19 => [(8,1)]
  | 20 => [(1,5)]
  | 21 => [(7,4)]
  | 22 => [(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(4,2)]
  | 27 => [(5,3)]
  | 28 => [(5,5)]
  | 29 => [(7,0)]
  | 30 => [(4,1)]
  | 31 => [(0,2)]
  | 32 => [(1,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(1,4)]
  | 40 => [(1,3)]
  | 41 => [(5,2)]
  | 42 => [(8,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5)]
  | 45 => [(3,0)]
  | 46 => [(2,5)]
  | 47 => [(6,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(6,0)]
  | 51 => [(0,4)]
  | 52 => [(5,4)]
  | 53 => [(1,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(4,0)]
  | 59 => [(7,3)]
  | 60 => [(8,2)]
  | 61 => [(4,3)]
  | 62 => [(7,5)]
  | 63 => [(6,0)]
  | 64 => [(7,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(5,1)]
  | 68 => [(0,1)]
  | 69 => [(6,2)]
  | 70 => [(1,3)]
  | 71 => [(8,2)]
  | 72 => [(5,0)]
  | 73 => [(4,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(8,5)]
  | 77 => [(1,0)]
  | 78 => [(0,4)]
  | 79 => [(5,4)]
  | 80 => [(0,0)]
  | 81 => [(7,2)]
  | 82 => [(7,4)]
  | 83 => [(1,3),(6,3)]
  | 84 => [(7,2),(8,2)]
  | 85 => [(4,3)]
  | 86 => [(1,5)]
  | 87 => [(6,1)]
  | 88 => [(4,1)]
  | 89 => [(0,2),(6,5)]
  | _ => [(0,4),(1,1)]
def root3Node8Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,3)]
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3)]
  | 19 => some [(8,1)]
  | 20 => some [(1,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2)]
  | 27 => some [(5,3)]
  | 28 => some [(5,5)]
  | 29 => some [(7,0)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(1,4)]
  | 40 => some [(1,3)]
  | 41 => some [(5,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(3,0)]
  | 46 => some [(2,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(6,0)]
  | 51 => some [(0,4)]
  | 52 => some [(5,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(8,2)]
  | 61 => some [(4,3)]
  | 62 => some [(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(1,3)]
  | 71 => some [(8,2)]
  | 72 => some [(5,0)]
  | 73 => some [(4,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(8,5)]
  | 77 => some [(1,0)]
  | 78 => some [(0,4)]
  | 79 => some [(5,4)]
  | 80 => some [(0,0)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(1,3),(6,3)]
  | 84 => some [(7,2),(8,2)]
  | 85 => some [(4,3)]
  | 86 => some [(1,5)]
  | 87 => some [(6,1)]
  | 88 => some [(4,1)]
  | 89 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root3Node8Domains1_fast_eq : root3Node8Domains1 = expandDomains root3Node8Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root3Node8Domains1 v = expandDomains root3Node8Domains1Fast v from by decide) v
theorem root3Node8Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq (by decide)
theorem root3Node8Step1Narrowing_checked :
    checkNarrowing table54 root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root3Node8Domains0 root3Node8Domains1 (by
      simp only [List.all_cons, List.all_nil, root3Node8Step1Chunk0_0_checked, root3Node8Step1Chunk0_1_checked, root3Node8Step1Chunk0_2_checked, root3Node8Step1Chunk0_3_checked, root3Node8Step1Chunk0_4_checked, root3Node8Step1Chunk0_5_checked, root3Node8Step1Chunk1_0_checked, root3Node8Step1Chunk1_1_checked, root3Node8Step1Chunk1_2_checked, root3Node8Step1Chunk1_3_checked, root3Node8Step1Chunk1_4_checked, root3Node8Step1Chunk1_5_checked, root3Node8Step1Chunk2_0_checked, root3Node8Step1Chunk2_1_checked, root3Node8Step1Chunk2_2_checked, root3Node8Step1Chunk2_3_checked, root3Node8Step1Chunk2_4_checked, root3Node8Step1Chunk2_5_checked, root3Node8Step1Chunk3_0_checked, root3Node8Step1Chunk3_1_checked, root3Node8Step1Chunk3_2_checked, root3Node8Step1Chunk3_3_checked, root3Node8Step1Chunk3_4_checked, root3Node8Step1Chunk3_5_checked, root3Node8Step1Chunk4_0_checked, root3Node8Step1Chunk4_1_checked, root3Node8Step1Chunk4_2_checked, root3Node8Step1Chunk4_3_checked, root3Node8Step1Chunk4_4_checked, root3Node8Step1Chunk4_5_checked, root3Node8Step1Chunk5_0_checked, root3Node8Step1Chunk5_1_checked, root3Node8Step1Chunk5_2_checked, root3Node8Step1Chunk5_3_checked, root3Node8Step1Chunk5_4_checked, root3Node8Step1Chunk5_5_checked, root3Node8Step1Chunk6_0_checked, root3Node8Step1Chunk6_1_checked, root3Node8Step1Chunk6_2_checked, root3Node8Step1Chunk6_3_checked, root3Node8Step1Chunk6_4_checked, root3Node8Step1Chunk6_5_checked, root3Node8Step1Chunk7_0_checked, root3Node8Step1Chunk7_1_checked, root3Node8Step1Chunk7_2_checked, root3Node8Step1Chunk7_3_checked, root3Node8Step1Chunk7_4_checked, root3Node8Step1Chunk7_5_checked, root3Node8Step1Chunk8_0_checked, root3Node8Step1Chunk8_1_checked, root3Node8Step1Chunk8_2_checked, root3Node8Step1Chunk8_3_checked, root3Node8Step1Chunk8_4_checked, root3Node8Step1Chunk8_5_checked, Bool.true_and])
theorem root3Node8Step1_checked :
    checkReplacement table54 root3Node8Domains0 root3Node8Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root3Node8Domains0 root3Node8Domains1
    root3Node8Domains0Fast root3Node8Domains1Fast
    root3Node8Domains0_fast_eq root3Node8Domains1_fast_eq
    root3Node8Step1Narrowing_checked (by decide)
def root3Node8Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3)]
  | 5 => [(8,2)]
  | 6 => [(8,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(6,4)]
  | 11 => [(1,2)]
  | 12 => [(8,4)]
  | 13 => [(5,3)]
  | 14 => [(8,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(0,3)]
  | 19 => [(8,1)]
  | 20 => [(1,5)]
  | 21 => [(7,4)]
  | 22 => [(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(4,2)]
  | 27 => [(5,3)]
  | 28 => [(5,5)]
  | 29 => [(7,0)]
  | 30 => [(4,1)]
  | 31 => [(0,2)]
  | 32 => [(1,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(1,4)]
  | 40 => [(1,3)]
  | 41 => [(5,2)]
  | 42 => [(8,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5)]
  | 45 => [(3,0)]
  | 46 => [(2,5)]
  | 47 => [(6,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(6,0)]
  | 51 => [(0,4)]
  | 52 => [(5,4)]
  | 53 => [(1,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(4,0)]
  | 59 => [(7,3)]
  | 60 => [(8,2)]
  | 61 => [(4,3)]
  | 62 => [(7,5)]
  | 63 => [(6,0)]
  | 64 => [(7,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(5,1)]
  | 68 => [(0,1)]
  | 69 => [(6,2)]
  | 70 => [(1,3)]
  | 71 => [(8,2)]
  | 72 => [(5,0)]
  | 73 => [(4,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(8,5)]
  | 77 => [(1,0)]
  | 78 => [(0,4)]
  | 79 => [(5,4)]
  | 80 => [(0,0)]
  | 81 => [(7,2)]
  | 82 => [(7,4)]
  | 83 => [(6,3)]
  | 84 => [(7,2)]
  | 85 => [(4,3)]
  | 86 => [(1,5)]
  | 87 => [(6,1)]
  | 88 => [(4,1)]
  | 89 => [(0,2)]
  | _ => [(1,1)]
def root3Node8Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,3)]
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3)]
  | 19 => some [(8,1)]
  | 20 => some [(1,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2)]
  | 27 => some [(5,3)]
  | 28 => some [(5,5)]
  | 29 => some [(7,0)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(1,4)]
  | 40 => some [(1,3)]
  | 41 => some [(5,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(3,0)]
  | 46 => some [(2,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(6,0)]
  | 51 => some [(0,4)]
  | 52 => some [(5,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(8,2)]
  | 61 => some [(4,3)]
  | 62 => some [(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(1,3)]
  | 71 => some [(8,2)]
  | 72 => some [(5,0)]
  | 73 => some [(4,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(8,5)]
  | 77 => some [(1,0)]
  | 78 => some [(0,4)]
  | 79 => some [(5,4)]
  | 80 => some [(0,0)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3)]
  | 86 => some [(1,5)]
  | 87 => some [(6,1)]
  | 88 => some [(4,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root3Node8Domains2_fast_eq : root3Node8Domains2 = expandDomains root3Node8Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root3Node8Domains2 v = expandDomains root3Node8Domains2Fast v from by decide) v
theorem root3Node8Step2Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq (by decide)
theorem root3Node8Step2Narrowing_checked :
    checkNarrowing table56 root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root3Node8Domains1 root3Node8Domains2 (by
      simp only [List.all_cons, List.all_nil, root3Node8Step2Chunk0_0_checked, root3Node8Step2Chunk0_1_checked, root3Node8Step2Chunk0_2_checked, root3Node8Step2Chunk0_3_checked, root3Node8Step2Chunk0_4_checked, root3Node8Step2Chunk0_5_checked, root3Node8Step2Chunk1_0_checked, root3Node8Step2Chunk1_1_checked, root3Node8Step2Chunk1_2_checked, root3Node8Step2Chunk1_3_checked, root3Node8Step2Chunk1_4_checked, root3Node8Step2Chunk1_5_checked, root3Node8Step2Chunk2_0_checked, root3Node8Step2Chunk2_1_checked, root3Node8Step2Chunk2_2_checked, root3Node8Step2Chunk2_3_checked, root3Node8Step2Chunk2_4_checked, root3Node8Step2Chunk2_5_checked, root3Node8Step2Chunk3_0_checked, root3Node8Step2Chunk3_1_checked, root3Node8Step2Chunk3_2_checked, root3Node8Step2Chunk3_3_checked, root3Node8Step2Chunk3_4_checked, root3Node8Step2Chunk3_5_checked, root3Node8Step2Chunk4_0_checked, root3Node8Step2Chunk4_1_checked, root3Node8Step2Chunk4_2_checked, root3Node8Step2Chunk4_3_checked, root3Node8Step2Chunk4_4_checked, root3Node8Step2Chunk4_5_checked, root3Node8Step2Chunk5_0_checked, root3Node8Step2Chunk5_1_checked, root3Node8Step2Chunk5_2_checked, root3Node8Step2Chunk5_3_checked, root3Node8Step2Chunk5_4_checked, root3Node8Step2Chunk5_5_checked, root3Node8Step2Chunk6_0_checked, root3Node8Step2Chunk6_1_checked, root3Node8Step2Chunk6_2_checked, root3Node8Step2Chunk6_3_checked, root3Node8Step2Chunk6_4_checked, root3Node8Step2Chunk6_5_checked, root3Node8Step2Chunk7_0_checked, root3Node8Step2Chunk7_1_checked, root3Node8Step2Chunk7_2_checked, root3Node8Step2Chunk7_3_checked, root3Node8Step2Chunk7_4_checked, root3Node8Step2Chunk7_5_checked, root3Node8Step2Chunk8_0_checked, root3Node8Step2Chunk8_1_checked, root3Node8Step2Chunk8_2_checked, root3Node8Step2Chunk8_3_checked, root3Node8Step2Chunk8_4_checked, root3Node8Step2Chunk8_5_checked, Bool.true_and])
theorem root3Node8Step2_checked :
    checkReplacement table56 root3Node8Domains1 root3Node8Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root3Node8Domains1 root3Node8Domains2
    root3Node8Domains1Fast root3Node8Domains2Fast
    root3Node8Domains1_fast_eq root3Node8Domains2_fast_eq
    root3Node8Step2Narrowing_checked (by decide)
theorem root3Node8Leaf_checked :
    checkCover 1 constraints root3Outputs root3Node8Domains2 (.output 3) = true := by decide
def root3Node9Domains0 : Domains 91 State := restrict root3Node7Domains1 40 (3,3)
def root3Node9Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,3)]
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3)]
  | 19 => some [(8,1)]
  | 20 => some [(1,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2)]
  | 27 => some [(5,3)]
  | 28 => some [(5,5)]
  | 29 => some [(7,0)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(1,4)]
  | 40 => some [(3,3)]
  | 41 => some [(5,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(3,0)]
  | 46 => some [(2,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(6,0)]
  | 51 => some [(0,4),(6,2)]
  | 52 => some [(5,4),(8,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(8,2)]
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
  | 78 => some [(0,4),(6,2)]
  | 79 => some [(5,4),(8,4)]
  | 80 => some [(0,0)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(1,3),(6,3)]
  | 84 => some [(7,2),(8,2)]
  | 85 => some [(4,3),(7,1)]
  | 86 => some [(1,5)]
  | 87 => some [(6,1)]
  | 88 => some [(4,1),(8,1)]
  | 89 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root3Node9Domains0_fast_eq : root3Node9Domains0 = expandDomains root3Node9Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root3Node9Domains0 v = expandDomains root3Node9Domains0Fast v from by decide) v
def root3Node9Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3)]
  | 5 => [(8,2)]
  | 6 => [(8,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(6,4)]
  | 11 => [(1,2)]
  | 12 => [(8,4)]
  | 13 => [(5,3)]
  | 14 => [(8,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(0,3)]
  | 19 => [(8,1)]
  | 20 => [(1,5)]
  | 21 => [(7,4)]
  | 22 => [(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(4,2)]
  | 27 => [(5,3)]
  | 28 => [(5,5)]
  | 29 => [(7,0)]
  | 30 => [(4,1)]
  | 31 => [(0,2)]
  | 32 => [(1,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(1,4)]
  | 40 => [(3,3)]
  | 41 => [(5,2)]
  | 42 => [(8,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5)]
  | 45 => [(3,0)]
  | 46 => [(2,5)]
  | 47 => [(6,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(6,0)]
  | 51 => [(6,2)]
  | 52 => [(8,4)]
  | 53 => [(1,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(4,0)]
  | 59 => [(7,3)]
  | 60 => [(8,2)]
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
  | 83 => [(1,3),(6,3)]
  | 84 => [(7,2),(8,2)]
  | 85 => [(7,1)]
  | 86 => [(1,5)]
  | 87 => [(6,1)]
  | 88 => [(8,1)]
  | 89 => [(0,2),(6,5)]
  | _ => [(0,4),(1,1)]
def root3Node9Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,3)]
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3)]
  | 19 => some [(8,1)]
  | 20 => some [(1,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2)]
  | 27 => some [(5,3)]
  | 28 => some [(5,5)]
  | 29 => some [(7,0)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(1,4)]
  | 40 => some [(3,3)]
  | 41 => some [(5,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(3,0)]
  | 46 => some [(2,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(6,0)]
  | 51 => some [(6,2)]
  | 52 => some [(8,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(8,2)]
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
  | 83 => some [(1,3),(6,3)]
  | 84 => some [(7,2),(8,2)]
  | 85 => some [(7,1)]
  | 86 => some [(1,5)]
  | 87 => some [(6,1)]
  | 88 => some [(8,1)]
  | 89 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root3Node9Domains1_fast_eq : root3Node9Domains1 = expandDomains root3Node9Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root3Node9Domains1 v = expandDomains root3Node9Domains1Fast v from by decide) v
theorem root3Node9Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq (by decide)
theorem root3Node9Step1Narrowing_checked :
    checkNarrowing table54 root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root3Node9Domains0 root3Node9Domains1 (by
      simp only [List.all_cons, List.all_nil, root3Node9Step1Chunk0_0_checked, root3Node9Step1Chunk0_1_checked, root3Node9Step1Chunk0_2_checked, root3Node9Step1Chunk0_3_checked, root3Node9Step1Chunk0_4_checked, root3Node9Step1Chunk0_5_checked, root3Node9Step1Chunk1_0_checked, root3Node9Step1Chunk1_1_checked, root3Node9Step1Chunk1_2_checked, root3Node9Step1Chunk1_3_checked, root3Node9Step1Chunk1_4_checked, root3Node9Step1Chunk1_5_checked, root3Node9Step1Chunk2_0_checked, root3Node9Step1Chunk2_1_checked, root3Node9Step1Chunk2_2_checked, root3Node9Step1Chunk2_3_checked, root3Node9Step1Chunk2_4_checked, root3Node9Step1Chunk2_5_checked, root3Node9Step1Chunk3_0_checked, root3Node9Step1Chunk3_1_checked, root3Node9Step1Chunk3_2_checked, root3Node9Step1Chunk3_3_checked, root3Node9Step1Chunk3_4_checked, root3Node9Step1Chunk3_5_checked, root3Node9Step1Chunk4_0_checked, root3Node9Step1Chunk4_1_checked, root3Node9Step1Chunk4_2_checked, root3Node9Step1Chunk4_3_checked, root3Node9Step1Chunk4_4_checked, root3Node9Step1Chunk4_5_checked, root3Node9Step1Chunk5_0_checked, root3Node9Step1Chunk5_1_checked, root3Node9Step1Chunk5_2_checked, root3Node9Step1Chunk5_3_checked, root3Node9Step1Chunk5_4_checked, root3Node9Step1Chunk5_5_checked, root3Node9Step1Chunk6_0_checked, root3Node9Step1Chunk6_1_checked, root3Node9Step1Chunk6_2_checked, root3Node9Step1Chunk6_3_checked, root3Node9Step1Chunk6_4_checked, root3Node9Step1Chunk6_5_checked, root3Node9Step1Chunk7_0_checked, root3Node9Step1Chunk7_1_checked, root3Node9Step1Chunk7_2_checked, root3Node9Step1Chunk7_3_checked, root3Node9Step1Chunk7_4_checked, root3Node9Step1Chunk7_5_checked, root3Node9Step1Chunk8_0_checked, root3Node9Step1Chunk8_1_checked, root3Node9Step1Chunk8_2_checked, root3Node9Step1Chunk8_3_checked, root3Node9Step1Chunk8_4_checked, root3Node9Step1Chunk8_5_checked, Bool.true_and])
theorem root3Node9Step1_checked :
    checkReplacement table54 root3Node9Domains0 root3Node9Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root3Node9Domains0 root3Node9Domains1
    root3Node9Domains0Fast root3Node9Domains1Fast
    root3Node9Domains0_fast_eq root3Node9Domains1_fast_eq
    root3Node9Step1Narrowing_checked (by decide)
def root3Node9Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3)]
  | 5 => [(8,2)]
  | 6 => [(8,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(6,4)]
  | 11 => [(1,2)]
  | 12 => [(8,4)]
  | 13 => [(5,3)]
  | 14 => [(8,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(0,3)]
  | 19 => [(8,1)]
  | 20 => [(1,5)]
  | 21 => [(7,4)]
  | 22 => [(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(4,2)]
  | 27 => [(5,3)]
  | 28 => [(5,5)]
  | 29 => [(7,0)]
  | 30 => [(4,1)]
  | 31 => [(0,2)]
  | 32 => [(1,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(1,4)]
  | 40 => [(3,3)]
  | 41 => [(5,2)]
  | 42 => [(8,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5)]
  | 45 => [(3,0)]
  | 46 => [(2,5)]
  | 47 => [(6,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(6,0)]
  | 51 => [(6,2)]
  | 52 => [(8,4)]
  | 53 => [(1,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(4,0)]
  | 59 => [(7,3)]
  | 60 => [(8,2)]
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
def root3Node9Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,3)]
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3)]
  | 19 => some [(8,1)]
  | 20 => some [(1,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2)]
  | 27 => some [(5,3)]
  | 28 => some [(5,5)]
  | 29 => some [(7,0)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(1,4)]
  | 40 => some [(3,3)]
  | 41 => some [(5,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(3,0)]
  | 46 => some [(2,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(6,0)]
  | 51 => some [(6,2)]
  | 52 => some [(8,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(8,2)]
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
theorem root3Node9Domains2_fast_eq : root3Node9Domains2 = expandDomains root3Node9Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root3Node9Domains2 v = expandDomains root3Node9Domains2Fast v from by decide) v
theorem root3Node9Step2Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq (by decide)
theorem root3Node9Step2Narrowing_checked :
    checkNarrowing table56 root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root3Node9Domains1 root3Node9Domains2 (by
      simp only [List.all_cons, List.all_nil, root3Node9Step2Chunk0_0_checked, root3Node9Step2Chunk0_1_checked, root3Node9Step2Chunk0_2_checked, root3Node9Step2Chunk0_3_checked, root3Node9Step2Chunk0_4_checked, root3Node9Step2Chunk0_5_checked, root3Node9Step2Chunk1_0_checked, root3Node9Step2Chunk1_1_checked, root3Node9Step2Chunk1_2_checked, root3Node9Step2Chunk1_3_checked, root3Node9Step2Chunk1_4_checked, root3Node9Step2Chunk1_5_checked, root3Node9Step2Chunk2_0_checked, root3Node9Step2Chunk2_1_checked, root3Node9Step2Chunk2_2_checked, root3Node9Step2Chunk2_3_checked, root3Node9Step2Chunk2_4_checked, root3Node9Step2Chunk2_5_checked, root3Node9Step2Chunk3_0_checked, root3Node9Step2Chunk3_1_checked, root3Node9Step2Chunk3_2_checked, root3Node9Step2Chunk3_3_checked, root3Node9Step2Chunk3_4_checked, root3Node9Step2Chunk3_5_checked, root3Node9Step2Chunk4_0_checked, root3Node9Step2Chunk4_1_checked, root3Node9Step2Chunk4_2_checked, root3Node9Step2Chunk4_3_checked, root3Node9Step2Chunk4_4_checked, root3Node9Step2Chunk4_5_checked, root3Node9Step2Chunk5_0_checked, root3Node9Step2Chunk5_1_checked, root3Node9Step2Chunk5_2_checked, root3Node9Step2Chunk5_3_checked, root3Node9Step2Chunk5_4_checked, root3Node9Step2Chunk5_5_checked, root3Node9Step2Chunk6_0_checked, root3Node9Step2Chunk6_1_checked, root3Node9Step2Chunk6_2_checked, root3Node9Step2Chunk6_3_checked, root3Node9Step2Chunk6_4_checked, root3Node9Step2Chunk6_5_checked, root3Node9Step2Chunk7_0_checked, root3Node9Step2Chunk7_1_checked, root3Node9Step2Chunk7_2_checked, root3Node9Step2Chunk7_3_checked, root3Node9Step2Chunk7_4_checked, root3Node9Step2Chunk7_5_checked, root3Node9Step2Chunk8_0_checked, root3Node9Step2Chunk8_1_checked, root3Node9Step2Chunk8_2_checked, root3Node9Step2Chunk8_3_checked, root3Node9Step2Chunk8_4_checked, root3Node9Step2Chunk8_5_checked, Bool.true_and])
theorem root3Node9Step2_checked :
    checkReplacement table56 root3Node9Domains1 root3Node9Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root3Node9Domains1 root3Node9Domains2
    root3Node9Domains1Fast root3Node9Domains2Fast
    root3Node9Domains1_fast_eq root3Node9Domains2_fast_eq
    root3Node9Step2Narrowing_checked (by decide)
theorem root3Node9Leaf_checked :
    checkCover 1 constraints root3Outputs root3Node9Domains2 (.output 4) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
