module

public import SpectreFinite.RadiusFiveRoot3Part4
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable51
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root3Node10Domains0 : Domains 91 State := restrict root3Node6Domains1 13 (8,3)
def root3Node10Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 13 => some [(8,3)]
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
  | 40 => some [(1,3),(3,3),(7,3)]
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
theorem root3Node10Domains0_fast_eq : root3Node10Domains0 = expandDomains root3Node10Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root3Node10Domains0 v = expandDomains root3Node10Domains0Fast v from by decide) v
def root3Node10Domains1 (v : Fin 91) : List State :=
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
  | 13 => [(8,3)]
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
  | 40 => [(7,3)]
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
  | 78 => [(1,2),(6,2)]
  | 79 => [(8,4)]
  | 80 => [(0,0)]
  | 81 => [(7,2)]
  | 82 => [(7,4)]
  | 83 => [(1,3),(6,3)]
  | 84 => [(7,2),(8,2)]
  | 85 => [(7,1),(8,1)]
  | 86 => [(1,5)]
  | 87 => [(6,1)]
  | 88 => [(8,1)]
  | 89 => [(0,2),(6,5)]
  | _ => [(0,4),(1,1)]
def root3Node10Domains1Fast (v : Fin 91) : Option (List State) :=
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
  | 13 => some [(8,3)]
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
  | 40 => some [(7,3)]
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
  | 78 => some [(1,2),(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(0,0)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(1,3),(6,3)]
  | 84 => some [(7,2),(8,2)]
  | 85 => some [(7,1),(8,1)]
  | 86 => some [(1,5)]
  | 87 => some [(6,1)]
  | 88 => some [(8,1)]
  | 89 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root3Node10Domains1_fast_eq : root3Node10Domains1 = expandDomains root3Node10Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root3Node10Domains1 v = expandDomains root3Node10Domains1Fast v from by decide) v
theorem root3Node10Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq (by decide)
theorem root3Node10Step1Narrowing_checked :
    checkNarrowing table54 root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root3Node10Domains0 root3Node10Domains1 (by
      simp only [List.all_cons, List.all_nil, root3Node10Step1Chunk0_0_checked, root3Node10Step1Chunk0_1_checked, root3Node10Step1Chunk0_2_checked, root3Node10Step1Chunk0_3_checked, root3Node10Step1Chunk0_4_checked, root3Node10Step1Chunk0_5_checked, root3Node10Step1Chunk1_0_checked, root3Node10Step1Chunk1_1_checked, root3Node10Step1Chunk1_2_checked, root3Node10Step1Chunk1_3_checked, root3Node10Step1Chunk1_4_checked, root3Node10Step1Chunk1_5_checked, root3Node10Step1Chunk2_0_checked, root3Node10Step1Chunk2_1_checked, root3Node10Step1Chunk2_2_checked, root3Node10Step1Chunk2_3_checked, root3Node10Step1Chunk2_4_checked, root3Node10Step1Chunk2_5_checked, root3Node10Step1Chunk3_0_checked, root3Node10Step1Chunk3_1_checked, root3Node10Step1Chunk3_2_checked, root3Node10Step1Chunk3_3_checked, root3Node10Step1Chunk3_4_checked, root3Node10Step1Chunk3_5_checked, root3Node10Step1Chunk4_0_checked, root3Node10Step1Chunk4_1_checked, root3Node10Step1Chunk4_2_checked, root3Node10Step1Chunk4_3_checked, root3Node10Step1Chunk4_4_checked, root3Node10Step1Chunk4_5_checked, root3Node10Step1Chunk5_0_checked, root3Node10Step1Chunk5_1_checked, root3Node10Step1Chunk5_2_checked, root3Node10Step1Chunk5_3_checked, root3Node10Step1Chunk5_4_checked, root3Node10Step1Chunk5_5_checked, root3Node10Step1Chunk6_0_checked, root3Node10Step1Chunk6_1_checked, root3Node10Step1Chunk6_2_checked, root3Node10Step1Chunk6_3_checked, root3Node10Step1Chunk6_4_checked, root3Node10Step1Chunk6_5_checked, root3Node10Step1Chunk7_0_checked, root3Node10Step1Chunk7_1_checked, root3Node10Step1Chunk7_2_checked, root3Node10Step1Chunk7_3_checked, root3Node10Step1Chunk7_4_checked, root3Node10Step1Chunk7_5_checked, root3Node10Step1Chunk8_0_checked, root3Node10Step1Chunk8_1_checked, root3Node10Step1Chunk8_2_checked, root3Node10Step1Chunk8_3_checked, root3Node10Step1Chunk8_4_checked, root3Node10Step1Chunk8_5_checked, Bool.true_and])
theorem root3Node10Step1_checked :
    checkReplacement table54 root3Node10Domains0 root3Node10Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root3Node10Domains0 root3Node10Domains1
    root3Node10Domains0Fast root3Node10Domains1Fast
    root3Node10Domains0_fast_eq root3Node10Domains1_fast_eq
    root3Node10Step1Narrowing_checked (by decide)
def root3Node10Domains2 (v : Fin 91) : List State :=
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
  | 13 => [(8,3)]
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
  | 40 => [(7,3)]
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
def root3Node10Domains2Fast (v : Fin 91) : Option (List State) :=
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
  | 13 => some [(8,3)]
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
  | 40 => some [(7,3)]
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
theorem root3Node10Domains2_fast_eq : root3Node10Domains2 = expandDomains root3Node10Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root3Node10Domains2 v = expandDomains root3Node10Domains2Fast v from by decide) v
theorem root3Node10Step2Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq (by decide)
theorem root3Node10Step2Narrowing_checked :
    checkNarrowing table56 root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root3Node10Domains1 root3Node10Domains2 (by
      simp only [List.all_cons, List.all_nil, root3Node10Step2Chunk0_0_checked, root3Node10Step2Chunk0_1_checked, root3Node10Step2Chunk0_2_checked, root3Node10Step2Chunk0_3_checked, root3Node10Step2Chunk0_4_checked, root3Node10Step2Chunk0_5_checked, root3Node10Step2Chunk1_0_checked, root3Node10Step2Chunk1_1_checked, root3Node10Step2Chunk1_2_checked, root3Node10Step2Chunk1_3_checked, root3Node10Step2Chunk1_4_checked, root3Node10Step2Chunk1_5_checked, root3Node10Step2Chunk2_0_checked, root3Node10Step2Chunk2_1_checked, root3Node10Step2Chunk2_2_checked, root3Node10Step2Chunk2_3_checked, root3Node10Step2Chunk2_4_checked, root3Node10Step2Chunk2_5_checked, root3Node10Step2Chunk3_0_checked, root3Node10Step2Chunk3_1_checked, root3Node10Step2Chunk3_2_checked, root3Node10Step2Chunk3_3_checked, root3Node10Step2Chunk3_4_checked, root3Node10Step2Chunk3_5_checked, root3Node10Step2Chunk4_0_checked, root3Node10Step2Chunk4_1_checked, root3Node10Step2Chunk4_2_checked, root3Node10Step2Chunk4_3_checked, root3Node10Step2Chunk4_4_checked, root3Node10Step2Chunk4_5_checked, root3Node10Step2Chunk5_0_checked, root3Node10Step2Chunk5_1_checked, root3Node10Step2Chunk5_2_checked, root3Node10Step2Chunk5_3_checked, root3Node10Step2Chunk5_4_checked, root3Node10Step2Chunk5_5_checked, root3Node10Step2Chunk6_0_checked, root3Node10Step2Chunk6_1_checked, root3Node10Step2Chunk6_2_checked, root3Node10Step2Chunk6_3_checked, root3Node10Step2Chunk6_4_checked, root3Node10Step2Chunk6_5_checked, root3Node10Step2Chunk7_0_checked, root3Node10Step2Chunk7_1_checked, root3Node10Step2Chunk7_2_checked, root3Node10Step2Chunk7_3_checked, root3Node10Step2Chunk7_4_checked, root3Node10Step2Chunk7_5_checked, root3Node10Step2Chunk8_0_checked, root3Node10Step2Chunk8_1_checked, root3Node10Step2Chunk8_2_checked, root3Node10Step2Chunk8_3_checked, root3Node10Step2Chunk8_4_checked, root3Node10Step2Chunk8_5_checked, Bool.true_and])
theorem root3Node10Step2_checked :
    checkReplacement table56 root3Node10Domains1 root3Node10Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root3Node10Domains1 root3Node10Domains2
    root3Node10Domains1Fast root3Node10Domains2Fast
    root3Node10Domains1_fast_eq root3Node10Domains2_fast_eq
    root3Node10Step2Narrowing_checked (by decide)
def root3Node11Domains0 : Domains 91 State := restrict root3Node10Domains2 78 (1,2)
def root3Node11Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 13 => some [(8,3)]
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
  | 40 => some [(7,3)]
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
  | 78 => some [(1,2)]
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
theorem root3Node11Domains0_fast_eq : root3Node11Domains0 = expandDomains root3Node11Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root3Node11Domains0 v = expandDomains root3Node11Domains0Fast v from by decide) v
def root3Node11Domains1 (v : Fin 91) : List State :=
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
  | 13 => [(8,3)]
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
  | 40 => [(7,3)]
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
  | 78 => [(1,2)]
  | 79 => [(8,4)]
  | 80 => [(0,0)]
  | 81 => [(7,2)]
  | 82 => [(7,4)]
  | 83 => [(1,3)]
  | 84 => [(8,2)]
  | 85 => [(8,1)]
  | 86 => [(1,5)]
  | 87 => [(6,1)]
  | 88 => [(8,1)]
  | 89 => [(6,5)]
  | _ => [(0,4)]
def root3Node11Domains1Fast (v : Fin 91) : Option (List State) :=
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
  | 13 => some [(8,3)]
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
  | 40 => some [(7,3)]
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
  | 78 => some [(1,2)]
  | 79 => some [(8,4)]
  | 80 => some [(0,0)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(1,3)]
  | 84 => some [(8,2)]
  | 85 => some [(8,1)]
  | 86 => some [(1,5)]
  | 87 => some [(6,1)]
  | 88 => some [(8,1)]
  | 89 => some [(6,5)]
  | _ => some [(0,4)]
theorem root3Node11Domains1_fast_eq : root3Node11Domains1 = expandDomains root3Node11Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root3Node11Domains1 v = expandDomains root3Node11Domains1Fast v from by decide) v
theorem root3Node11Step1Chunk0_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_0⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk0_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_1⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk0_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_2⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk0_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_3⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk0_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_4⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk0_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_5⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk1_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_0⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk1_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_1⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk1_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_2⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk1_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_3⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk1_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_4⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk1_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_5⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk2_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_0⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk2_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_1⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk2_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_2⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk2_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_3⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk2_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_4⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk2_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_5⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk3_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_0⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk3_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_1⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk3_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_2⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk3_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_3⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk3_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_4⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk3_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_5⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk4_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_0⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk4_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_1⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk4_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_2⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk4_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_3⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk4_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_4⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk4_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_5⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk5_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_0⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk5_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_1⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk5_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_2⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk5_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_3⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk5_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_4⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk5_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_5⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk6_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_0⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk6_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_1⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk6_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_2⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk6_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_3⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk6_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_4⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk6_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_5⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk7_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_0⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk7_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_1⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk7_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_2⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk7_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_3⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk7_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_4⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk7_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_5⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk8_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_0⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk8_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_1⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk8_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_2⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk8_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_3⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk8_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_4⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Chunk8_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_5⟩
      root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq (by decide)
theorem root3Node11Step1Narrowing_checked :
    checkNarrowing table51 root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkNarrowing_flatten table51Scope [table51Rows0_0,table51Rows0_1,table51Rows0_2,table51Rows0_3,table51Rows0_4,table51Rows0_5,table51Rows1_0,table51Rows1_1,table51Rows1_2,table51Rows1_3,table51Rows1_4,table51Rows1_5,table51Rows2_0,table51Rows2_1,table51Rows2_2,table51Rows2_3,table51Rows2_4,table51Rows2_5,table51Rows3_0,table51Rows3_1,table51Rows3_2,table51Rows3_3,table51Rows3_4,table51Rows3_5,table51Rows4_0,table51Rows4_1,table51Rows4_2,table51Rows4_3,table51Rows4_4,table51Rows4_5,table51Rows5_0,table51Rows5_1,table51Rows5_2,table51Rows5_3,table51Rows5_4,table51Rows5_5,table51Rows6_0,table51Rows6_1,table51Rows6_2,table51Rows6_3,table51Rows6_4,table51Rows6_5,table51Rows7_0,table51Rows7_1,table51Rows7_2,table51Rows7_3,table51Rows7_4,table51Rows7_5,table51Rows8_0,table51Rows8_1,table51Rows8_2,table51Rows8_3,table51Rows8_4,table51Rows8_5]
    root3Node11Domains0 root3Node11Domains1 (by
      simp only [List.all_cons, List.all_nil, root3Node11Step1Chunk0_0_checked, root3Node11Step1Chunk0_1_checked, root3Node11Step1Chunk0_2_checked, root3Node11Step1Chunk0_3_checked, root3Node11Step1Chunk0_4_checked, root3Node11Step1Chunk0_5_checked, root3Node11Step1Chunk1_0_checked, root3Node11Step1Chunk1_1_checked, root3Node11Step1Chunk1_2_checked, root3Node11Step1Chunk1_3_checked, root3Node11Step1Chunk1_4_checked, root3Node11Step1Chunk1_5_checked, root3Node11Step1Chunk2_0_checked, root3Node11Step1Chunk2_1_checked, root3Node11Step1Chunk2_2_checked, root3Node11Step1Chunk2_3_checked, root3Node11Step1Chunk2_4_checked, root3Node11Step1Chunk2_5_checked, root3Node11Step1Chunk3_0_checked, root3Node11Step1Chunk3_1_checked, root3Node11Step1Chunk3_2_checked, root3Node11Step1Chunk3_3_checked, root3Node11Step1Chunk3_4_checked, root3Node11Step1Chunk3_5_checked, root3Node11Step1Chunk4_0_checked, root3Node11Step1Chunk4_1_checked, root3Node11Step1Chunk4_2_checked, root3Node11Step1Chunk4_3_checked, root3Node11Step1Chunk4_4_checked, root3Node11Step1Chunk4_5_checked, root3Node11Step1Chunk5_0_checked, root3Node11Step1Chunk5_1_checked, root3Node11Step1Chunk5_2_checked, root3Node11Step1Chunk5_3_checked, root3Node11Step1Chunk5_4_checked, root3Node11Step1Chunk5_5_checked, root3Node11Step1Chunk6_0_checked, root3Node11Step1Chunk6_1_checked, root3Node11Step1Chunk6_2_checked, root3Node11Step1Chunk6_3_checked, root3Node11Step1Chunk6_4_checked, root3Node11Step1Chunk6_5_checked, root3Node11Step1Chunk7_0_checked, root3Node11Step1Chunk7_1_checked, root3Node11Step1Chunk7_2_checked, root3Node11Step1Chunk7_3_checked, root3Node11Step1Chunk7_4_checked, root3Node11Step1Chunk7_5_checked, root3Node11Step1Chunk8_0_checked, root3Node11Step1Chunk8_1_checked, root3Node11Step1Chunk8_2_checked, root3Node11Step1Chunk8_3_checked, root3Node11Step1Chunk8_4_checked, root3Node11Step1Chunk8_5_checked, Bool.true_and])
theorem root3Node11Step1_checked :
    checkReplacement table51 root3Node11Domains0 root3Node11Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root3Node11Domains0 root3Node11Domains1
    root3Node11Domains0Fast root3Node11Domains1Fast
    root3Node11Domains0_fast_eq root3Node11Domains1_fast_eq
    root3Node11Step1Narrowing_checked (by decide)
theorem root3Node11Leaf_checked :
    checkCover 1 constraints root3Outputs root3Node11Domains1 (.output 5) = true := by decide
def root3Node12Domains0 : Domains 91 State := restrict root3Node10Domains2 78 (6,2)
def root3Node12Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 13 => some [(8,3)]
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
  | 40 => some [(7,3)]
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
  | 85 => some [(7,1),(8,1)]
  | 86 => some [(1,5)]
  | 87 => some [(6,1)]
  | 88 => some [(8,1)]
  | 89 => some [(6,5)]
  | _ => some [(0,4)]
theorem root3Node12Domains0_fast_eq : root3Node12Domains0 = expandDomains root3Node12Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root3Node12Domains0 v = expandDomains root3Node12Domains0Fast v from by decide) v
def root3Node12Domains1 (v : Fin 91) : List State :=
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
  | 13 => [(8,3)]
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
  | 40 => [(7,3)]
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
def root3Node12Domains1Fast (v : Fin 91) : Option (List State) :=
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
  | 13 => some [(8,3)]
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
  | 40 => some [(7,3)]
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
theorem root3Node12Domains1_fast_eq : root3Node12Domains1 = expandDomains root3Node12Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root3Node12Domains1 v = expandDomains root3Node12Domains1Fast v from by decide) v
theorem root3Node12Step1Chunk0_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_0⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk0_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_1⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk0_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_2⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk0_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_3⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk0_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_4⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk0_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_5⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk1_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_0⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk1_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_1⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk1_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_2⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk1_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_3⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk1_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_4⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk1_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_5⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk2_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_0⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk2_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_1⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk2_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_2⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk2_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_3⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk2_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_4⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk2_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_5⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk3_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_0⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk3_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_1⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk3_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_2⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk3_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_3⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk3_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_4⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk3_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_5⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk4_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_0⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk4_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_1⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk4_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_2⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk4_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_3⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk4_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_4⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk4_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_5⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk5_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_0⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk5_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_1⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk5_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_2⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk5_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_3⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk5_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_4⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk5_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_5⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk6_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_0⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk6_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_1⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk6_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_2⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk6_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_3⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk6_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_4⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk6_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_5⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk7_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_0⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk7_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_1⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk7_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_2⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk7_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_3⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk7_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_4⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk7_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_5⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk8_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_0⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk8_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_1⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk8_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_2⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk8_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_3⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk8_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_4⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Chunk8_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_5⟩
      root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq (by decide)
theorem root3Node12Step1Narrowing_checked :
    checkNarrowing table51 root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkNarrowing_flatten table51Scope [table51Rows0_0,table51Rows0_1,table51Rows0_2,table51Rows0_3,table51Rows0_4,table51Rows0_5,table51Rows1_0,table51Rows1_1,table51Rows1_2,table51Rows1_3,table51Rows1_4,table51Rows1_5,table51Rows2_0,table51Rows2_1,table51Rows2_2,table51Rows2_3,table51Rows2_4,table51Rows2_5,table51Rows3_0,table51Rows3_1,table51Rows3_2,table51Rows3_3,table51Rows3_4,table51Rows3_5,table51Rows4_0,table51Rows4_1,table51Rows4_2,table51Rows4_3,table51Rows4_4,table51Rows4_5,table51Rows5_0,table51Rows5_1,table51Rows5_2,table51Rows5_3,table51Rows5_4,table51Rows5_5,table51Rows6_0,table51Rows6_1,table51Rows6_2,table51Rows6_3,table51Rows6_4,table51Rows6_5,table51Rows7_0,table51Rows7_1,table51Rows7_2,table51Rows7_3,table51Rows7_4,table51Rows7_5,table51Rows8_0,table51Rows8_1,table51Rows8_2,table51Rows8_3,table51Rows8_4,table51Rows8_5]
    root3Node12Domains0 root3Node12Domains1 (by
      simp only [List.all_cons, List.all_nil, root3Node12Step1Chunk0_0_checked, root3Node12Step1Chunk0_1_checked, root3Node12Step1Chunk0_2_checked, root3Node12Step1Chunk0_3_checked, root3Node12Step1Chunk0_4_checked, root3Node12Step1Chunk0_5_checked, root3Node12Step1Chunk1_0_checked, root3Node12Step1Chunk1_1_checked, root3Node12Step1Chunk1_2_checked, root3Node12Step1Chunk1_3_checked, root3Node12Step1Chunk1_4_checked, root3Node12Step1Chunk1_5_checked, root3Node12Step1Chunk2_0_checked, root3Node12Step1Chunk2_1_checked, root3Node12Step1Chunk2_2_checked, root3Node12Step1Chunk2_3_checked, root3Node12Step1Chunk2_4_checked, root3Node12Step1Chunk2_5_checked, root3Node12Step1Chunk3_0_checked, root3Node12Step1Chunk3_1_checked, root3Node12Step1Chunk3_2_checked, root3Node12Step1Chunk3_3_checked, root3Node12Step1Chunk3_4_checked, root3Node12Step1Chunk3_5_checked, root3Node12Step1Chunk4_0_checked, root3Node12Step1Chunk4_1_checked, root3Node12Step1Chunk4_2_checked, root3Node12Step1Chunk4_3_checked, root3Node12Step1Chunk4_4_checked, root3Node12Step1Chunk4_5_checked, root3Node12Step1Chunk5_0_checked, root3Node12Step1Chunk5_1_checked, root3Node12Step1Chunk5_2_checked, root3Node12Step1Chunk5_3_checked, root3Node12Step1Chunk5_4_checked, root3Node12Step1Chunk5_5_checked, root3Node12Step1Chunk6_0_checked, root3Node12Step1Chunk6_1_checked, root3Node12Step1Chunk6_2_checked, root3Node12Step1Chunk6_3_checked, root3Node12Step1Chunk6_4_checked, root3Node12Step1Chunk6_5_checked, root3Node12Step1Chunk7_0_checked, root3Node12Step1Chunk7_1_checked, root3Node12Step1Chunk7_2_checked, root3Node12Step1Chunk7_3_checked, root3Node12Step1Chunk7_4_checked, root3Node12Step1Chunk7_5_checked, root3Node12Step1Chunk8_0_checked, root3Node12Step1Chunk8_1_checked, root3Node12Step1Chunk8_2_checked, root3Node12Step1Chunk8_3_checked, root3Node12Step1Chunk8_4_checked, root3Node12Step1Chunk8_5_checked, Bool.true_and])
theorem root3Node12Step1_checked :
    checkReplacement table51 root3Node12Domains0 root3Node12Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root3Node12Domains0 root3Node12Domains1
    root3Node12Domains0Fast root3Node12Domains1Fast
    root3Node12Domains0_fast_eq root3Node12Domains1_fast_eq
    root3Node12Step1Narrowing_checked (by decide)
theorem root3Node12Leaf_checked :
    checkCover 1 constraints root3Outputs root3Node12Domains1 (.output 6) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
