module

public import SpectreFinite.RadiusFiveRoot5Part9
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable53
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node20Domains0 : Domains 91 State := restrict root5Node19Domains3 13 (5,3)
def root5Node20Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(5,0)]
  | 4 => some [(4,5)]
  | 5 => some [(7,0)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(0,0)]
  | 11 => some [(7,2)]
  | 12 => some [(7,4)]
  | 13 => some [(5,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(1,5)]
  | 18 => some [(6,1)]
  | 19 => some [(4,1)]
  | 20 => some [(0,2)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(2,0)]
  | 27 => some [(7,3)]
  | 28 => some [(5,2)]
  | 29 => some [(8,0)]
  | 30 => some [(2,5),(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(3,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(0,0),(1,3),(7,3)]
  | 41 => some [(7,2),(8,2)]
  | 42 => some [(4,0),(8,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(0,3),(6,0)]
  | 51 => some [(0,4),(6,1),(6,2)]
  | 52 => some [(5,1),(5,4),(8,4)]
  | 53 => some [(0,1),(6,4)]
  | 54 => some [(1,2),(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(4,2),(8,2)]
  | 61 => some [(4,3),(7,1),(8,3)]
  | 62 => some [(7,5),(8,5)]
  | 63 => some [(0,3),(1,0)]
  | 64 => some [(7,1),(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(4,2),(8,2)]
  | 72 => some [(5,0),(5,3)]
  | 73 => some [(4,5),(5,5),(8,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(1,0)]
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
theorem root5Node20Domains0_fast_eq : root5Node20Domains0 = expandDomains root5Node20Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node20Domains0 v = expandDomains root5Node20Domains0Fast v from by decide) v
def root5Node20Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(5,0)]
  | 4 => [(4,5)]
  | 5 => [(7,0)]
  | 6 => [(8,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(0,0)]
  | 11 => [(7,2)]
  | 12 => [(7,4)]
  | 13 => [(5,3)]
  | 14 => [(5,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(1,5)]
  | 18 => [(6,1)]
  | 19 => [(4,1)]
  | 20 => [(0,2)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(2,0)]
  | 27 => [(7,3)]
  | 28 => [(5,2)]
  | 29 => [(8,0)]
  | 30 => [(2,5)]
  | 31 => [(6,0)]
  | 32 => [(7,1)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(3,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(1,4),(6,4)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(4,0)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(0,3),(6,0)]
  | 51 => [(6,1)]
  | 52 => [(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(4,0)]
  | 59 => [(7,3)]
  | 60 => [(4,2),(8,2)]
  | 61 => [(8,3)]
  | 62 => [(8,5)]
  | 63 => [(1,0)]
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
  | 76 => [(5,5),(8,5)]
  | 77 => [(1,0)]
  | 78 => [(0,4)]
  | 79 => [(5,4)]
  | 80 => [(0,0)]
  | 81 => [(7,2)]
  | 82 => [(7,4)]
  | 83 => [(0,5),(1,3),(6,3)]
  | 84 => [(4,4),(7,2),(8,2)]
  | 85 => [(4,3)]
  | 86 => [(1,5)]
  | 87 => [(6,1)]
  | 88 => [(4,1)]
  | 89 => [(0,2),(6,0),(6,5)]
  | _ => [(0,4),(1,1),(7,1)]
def root5Node20Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(5,0)]
  | 4 => some [(4,5)]
  | 5 => some [(7,0)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(0,0)]
  | 11 => some [(7,2)]
  | 12 => some [(7,4)]
  | 13 => some [(5,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(1,5)]
  | 18 => some [(6,1)]
  | 19 => some [(4,1)]
  | 20 => some [(0,2)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(2,0)]
  | 27 => some [(7,3)]
  | 28 => some [(5,2)]
  | 29 => some [(8,0)]
  | 30 => some [(2,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(3,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(0,3),(6,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(4,2),(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
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
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(1,0)]
  | 78 => some [(0,4)]
  | 79 => some [(5,4)]
  | 80 => some [(0,0)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(0,5),(1,3),(6,3)]
  | 84 => some [(4,4),(7,2),(8,2)]
  | 85 => some [(4,3)]
  | 86 => some [(1,5)]
  | 87 => some [(6,1)]
  | 88 => some [(4,1)]
  | 89 => some [(0,2),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root5Node20Domains1_fast_eq : root5Node20Domains1 = expandDomains root5Node20Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node20Domains1 v = expandDomains root5Node20Domains1Fast v from by decide) v
theorem root5Node20Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Narrowing_checked :
    checkNarrowing table54 root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root5Node20Domains0 root5Node20Domains1 (by
      simp only [List.all_cons, List.all_nil, root5Node20Step1Chunk0_0_checked, root5Node20Step1Chunk0_1_checked, root5Node20Step1Chunk0_2_checked, root5Node20Step1Chunk0_3_checked, root5Node20Step1Chunk0_4_checked, root5Node20Step1Chunk0_5_checked, root5Node20Step1Chunk1_0_checked, root5Node20Step1Chunk1_1_checked, root5Node20Step1Chunk1_2_checked, root5Node20Step1Chunk1_3_checked, root5Node20Step1Chunk1_4_checked, root5Node20Step1Chunk1_5_checked, root5Node20Step1Chunk2_0_checked, root5Node20Step1Chunk2_1_checked, root5Node20Step1Chunk2_2_checked, root5Node20Step1Chunk2_3_checked, root5Node20Step1Chunk2_4_checked, root5Node20Step1Chunk2_5_checked, root5Node20Step1Chunk3_0_checked, root5Node20Step1Chunk3_1_checked, root5Node20Step1Chunk3_2_checked, root5Node20Step1Chunk3_3_checked, root5Node20Step1Chunk3_4_checked, root5Node20Step1Chunk3_5_checked, root5Node20Step1Chunk4_0_checked, root5Node20Step1Chunk4_1_checked, root5Node20Step1Chunk4_2_checked, root5Node20Step1Chunk4_3_checked, root5Node20Step1Chunk4_4_checked, root5Node20Step1Chunk4_5_checked, root5Node20Step1Chunk5_0_checked, root5Node20Step1Chunk5_1_checked, root5Node20Step1Chunk5_2_checked, root5Node20Step1Chunk5_3_checked, root5Node20Step1Chunk5_4_checked, root5Node20Step1Chunk5_5_checked, root5Node20Step1Chunk6_0_checked, root5Node20Step1Chunk6_1_checked, root5Node20Step1Chunk6_2_checked, root5Node20Step1Chunk6_3_checked, root5Node20Step1Chunk6_4_checked, root5Node20Step1Chunk6_5_checked, root5Node20Step1Chunk7_0_checked, root5Node20Step1Chunk7_1_checked, root5Node20Step1Chunk7_2_checked, root5Node20Step1Chunk7_3_checked, root5Node20Step1Chunk7_4_checked, root5Node20Step1Chunk7_5_checked, root5Node20Step1Chunk8_0_checked, root5Node20Step1Chunk8_1_checked, root5Node20Step1Chunk8_2_checked, root5Node20Step1Chunk8_3_checked, root5Node20Step1Chunk8_4_checked, root5Node20Step1Chunk8_5_checked, Bool.true_and])
theorem root5Node20Step1_checked :
    checkReplacement table54 root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq
    root5Node20Step1Narrowing_checked (by decide)
def root5Node20Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(5,0)]
  | 4 => [(4,5)]
  | 5 => [(7,0)]
  | 6 => [(8,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(0,0)]
  | 11 => [(7,2)]
  | 12 => [(7,4)]
  | 13 => [(5,3)]
  | 14 => [(5,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(1,5)]
  | 18 => [(6,1)]
  | 19 => [(4,1)]
  | 20 => [(0,2)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(2,0)]
  | 27 => [(7,3)]
  | 28 => [(5,2)]
  | 29 => [(8,0)]
  | 30 => [(2,5)]
  | 31 => [(6,0)]
  | 32 => [(7,1)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(3,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(1,4)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(4,0)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(6,0)]
  | 51 => [(6,1)]
  | 52 => [(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(4,0)]
  | 59 => [(7,3)]
  | 60 => [(8,2)]
  | 61 => [(8,3)]
  | 62 => [(8,5)]
  | 63 => [(1,0)]
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
def root5Node20Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(5,0)]
  | 4 => some [(4,5)]
  | 5 => some [(7,0)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(0,0)]
  | 11 => some [(7,2)]
  | 12 => some [(7,4)]
  | 13 => some [(5,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(1,5)]
  | 18 => some [(6,1)]
  | 19 => some [(4,1)]
  | 20 => some [(0,2)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(2,0)]
  | 27 => some [(7,3)]
  | 28 => some [(5,2)]
  | 29 => some [(8,0)]
  | 30 => some [(2,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(3,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(6,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
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
theorem root5Node20Domains2_fast_eq : root5Node20Domains2 = expandDomains root5Node20Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node20Domains2 v = expandDomains root5Node20Domains2Fast v from by decide) v
theorem root5Node20Step2Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Narrowing_checked :
    checkNarrowing table57 root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root5Node20Domains1 root5Node20Domains2 (by
      simp only [List.all_cons, List.all_nil, root5Node20Step2Chunk0_0_checked, root5Node20Step2Chunk0_1_checked, root5Node20Step2Chunk0_2_checked, root5Node20Step2Chunk0_3_checked, root5Node20Step2Chunk0_4_checked, root5Node20Step2Chunk0_5_checked, root5Node20Step2Chunk1_0_checked, root5Node20Step2Chunk1_1_checked, root5Node20Step2Chunk1_2_checked, root5Node20Step2Chunk1_3_checked, root5Node20Step2Chunk1_4_checked, root5Node20Step2Chunk1_5_checked, root5Node20Step2Chunk2_0_checked, root5Node20Step2Chunk2_1_checked, root5Node20Step2Chunk2_2_checked, root5Node20Step2Chunk2_3_checked, root5Node20Step2Chunk2_4_checked, root5Node20Step2Chunk2_5_checked, root5Node20Step2Chunk3_0_checked, root5Node20Step2Chunk3_1_checked, root5Node20Step2Chunk3_2_checked, root5Node20Step2Chunk3_3_checked, root5Node20Step2Chunk3_4_checked, root5Node20Step2Chunk3_5_checked, root5Node20Step2Chunk4_0_checked, root5Node20Step2Chunk4_1_checked, root5Node20Step2Chunk4_2_checked, root5Node20Step2Chunk4_3_checked, root5Node20Step2Chunk4_4_checked, root5Node20Step2Chunk4_5_checked, root5Node20Step2Chunk5_0_checked, root5Node20Step2Chunk5_1_checked, root5Node20Step2Chunk5_2_checked, root5Node20Step2Chunk5_3_checked, root5Node20Step2Chunk5_4_checked, root5Node20Step2Chunk5_5_checked, root5Node20Step2Chunk6_0_checked, root5Node20Step2Chunk6_1_checked, root5Node20Step2Chunk6_2_checked, root5Node20Step2Chunk6_3_checked, root5Node20Step2Chunk6_4_checked, root5Node20Step2Chunk6_5_checked, root5Node20Step2Chunk7_0_checked, root5Node20Step2Chunk7_1_checked, root5Node20Step2Chunk7_2_checked, root5Node20Step2Chunk7_3_checked, root5Node20Step2Chunk7_4_checked, root5Node20Step2Chunk7_5_checked, root5Node20Step2Chunk8_0_checked, root5Node20Step2Chunk8_1_checked, root5Node20Step2Chunk8_2_checked, root5Node20Step2Chunk8_3_checked, root5Node20Step2Chunk8_4_checked, root5Node20Step2Chunk8_5_checked, Bool.true_and])
theorem root5Node20Step2_checked :
    checkReplacement table57 root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq
    root5Node20Step2Narrowing_checked (by decide)
theorem root5Node20Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node20Domains2 (.output 8) = true := by decide
def root5Node21Domains0 : Domains 91 State := restrict root5Node19Domains3 13 (8,3)
def root5Node21Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(5,0)]
  | 4 => some [(4,5)]
  | 5 => some [(7,0)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(0,0)]
  | 11 => some [(7,2)]
  | 12 => some [(7,4)]
  | 13 => some [(8,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(1,5)]
  | 18 => some [(6,1)]
  | 19 => some [(4,1)]
  | 20 => some [(0,2)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(2,0)]
  | 27 => some [(7,3)]
  | 28 => some [(5,2)]
  | 29 => some [(8,0)]
  | 30 => some [(2,5),(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(3,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(0,0),(1,3),(7,3)]
  | 41 => some [(7,2),(8,2)]
  | 42 => some [(4,0),(8,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(0,3),(6,0)]
  | 51 => some [(0,4),(6,1),(6,2)]
  | 52 => some [(5,1),(5,4),(8,4)]
  | 53 => some [(0,1),(6,4)]
  | 54 => some [(1,2),(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(4,2),(8,2)]
  | 61 => some [(4,3),(7,1),(8,3)]
  | 62 => some [(7,5),(8,5)]
  | 63 => some [(0,3),(1,0)]
  | 64 => some [(7,1),(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(4,2),(8,2)]
  | 72 => some [(5,0),(5,3)]
  | 73 => some [(4,5),(5,5),(8,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(1,0)]
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
theorem root5Node21Domains0_fast_eq : root5Node21Domains0 = expandDomains root5Node21Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node21Domains0 v = expandDomains root5Node21Domains0Fast v from by decide) v
def root5Node21Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(5,0)]
  | 4 => [(4,5)]
  | 5 => [(7,0)]
  | 6 => [(8,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(0,0)]
  | 11 => [(7,2)]
  | 12 => [(7,4)]
  | 13 => [(8,3)]
  | 14 => [(5,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(1,5)]
  | 18 => [(6,1)]
  | 19 => [(4,1)]
  | 20 => [(0,2)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(2,0)]
  | 27 => [(7,3)]
  | 28 => [(5,2)]
  | 29 => [(8,0)]
  | 30 => [(7,5)]
  | 31 => [(6,0)]
  | 32 => [(7,1)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(3,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(1,4),(6,4)]
  | 40 => [(1,3),(7,3)]
  | 41 => [(8,2)]
  | 42 => [(8,0)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(0,3),(6,0)]
  | 51 => [(0,4),(6,2)]
  | 52 => [(5,4),(8,4)]
  | 53 => [(6,4)]
  | 54 => [(1,2)]
  | 55 => [(8,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(4,0)]
  | 59 => [(7,3)]
  | 60 => [(4,2),(8,2)]
  | 61 => [(4,3),(7,1)]
  | 62 => [(7,5)]
  | 63 => [(0,3)]
  | 64 => [(8,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(5,1)]
  | 68 => [(0,1)]
  | 69 => [(6,2)]
  | 70 => [(1,3),(7,3)]
  | 71 => [(4,2)]
  | 72 => [(5,3)]
  | 73 => [(5,5),(8,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(5,5),(8,5)]
  | 77 => [(1,0)]
  | 78 => [(0,4),(1,2),(6,2)]
  | 79 => [(1,4),(3,4),(7,4)]
  | 80 => [(0,5),(6,3)]
  | 81 => [(4,4),(7,2)]
  | 82 => [(1,4),(7,4)]
  | 83 => [(0,5),(1,3),(6,3)]
  | 84 => [(4,4),(7,2),(8,2)]
  | 85 => [(2,1),(2,3),(2,5),(4,1)]
  | 86 => [(0,2),(6,0)]
  | 87 => [(1,1),(7,1)]
  | 88 => [(4,1),(7,5),(8,1)]
  | 89 => [(0,2),(6,0),(6,5)]
  | _ => [(0,4),(1,1),(7,1)]
def root5Node21Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(5,0)]
  | 4 => some [(4,5)]
  | 5 => some [(7,0)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(0,0)]
  | 11 => some [(7,2)]
  | 12 => some [(7,4)]
  | 13 => some [(8,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(1,5)]
  | 18 => some [(6,1)]
  | 19 => some [(4,1)]
  | 20 => some [(0,2)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(2,0)]
  | 27 => some [(7,3)]
  | 28 => some [(5,2)]
  | 29 => some [(8,0)]
  | 30 => some [(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(3,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(1,3),(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(0,3),(6,0)]
  | 51 => some [(0,4),(6,2)]
  | 52 => some [(5,4),(8,4)]
  | 53 => some [(6,4)]
  | 54 => some [(1,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(4,2),(8,2)]
  | 61 => some [(4,3),(7,1)]
  | 62 => some [(7,5)]
  | 63 => some [(0,3)]
  | 64 => some [(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(4,2)]
  | 72 => some [(5,3)]
  | 73 => some [(5,5),(8,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(1,0)]
  | 78 => some [(0,4),(1,2),(6,2)]
  | 79 => some [(1,4),(3,4),(7,4)]
  | 80 => some [(0,5),(6,3)]
  | 81 => some [(4,4),(7,2)]
  | 82 => some [(1,4),(7,4)]
  | 83 => some [(0,5),(1,3),(6,3)]
  | 84 => some [(4,4),(7,2),(8,2)]
  | 85 => some [(2,1),(2,3),(2,5),(4,1)]
  | 86 => some [(0,2),(6,0)]
  | 87 => some [(1,1),(7,1)]
  | 88 => some [(4,1),(7,5),(8,1)]
  | 89 => some [(0,2),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root5Node21Domains1_fast_eq : root5Node21Domains1 = expandDomains root5Node21Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node21Domains1 v = expandDomains root5Node21Domains1Fast v from by decide) v
theorem root5Node21Step1Chunk0_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_0⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk0_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_1⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk0_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_2⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk0_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_3⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk0_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_4⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk0_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_5⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk1_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_0⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk1_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_1⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk1_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_2⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk1_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_3⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk1_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_4⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk1_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_5⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk2_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_0⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk2_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_1⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk2_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_2⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk2_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_3⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk2_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_4⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk2_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_5⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk3_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_0⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk3_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_1⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk3_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_2⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk3_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_3⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk3_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_4⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk3_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_5⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk4_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_0⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk4_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_1⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk4_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_2⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk4_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_3⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk4_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_4⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk4_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_5⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk5_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_0⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk5_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_1⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk5_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_2⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk5_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_3⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk5_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_4⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk5_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_5⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk6_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_0⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk6_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_1⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk6_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_2⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk6_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_3⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk6_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_4⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk6_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_5⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk7_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_0⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk7_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_1⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk7_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_2⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk7_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_3⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk7_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_4⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk7_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_5⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk8_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_0⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk8_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_1⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk8_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_2⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk8_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_3⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk8_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_4⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Chunk8_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_5⟩
      root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq (by decide)
theorem root5Node21Step1Narrowing_checked :
    checkNarrowing table53 root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkNarrowing_flatten table53Scope [table53Rows0_0,table53Rows0_1,table53Rows0_2,table53Rows0_3,table53Rows0_4,table53Rows0_5,table53Rows1_0,table53Rows1_1,table53Rows1_2,table53Rows1_3,table53Rows1_4,table53Rows1_5,table53Rows2_0,table53Rows2_1,table53Rows2_2,table53Rows2_3,table53Rows2_4,table53Rows2_5,table53Rows3_0,table53Rows3_1,table53Rows3_2,table53Rows3_3,table53Rows3_4,table53Rows3_5,table53Rows4_0,table53Rows4_1,table53Rows4_2,table53Rows4_3,table53Rows4_4,table53Rows4_5,table53Rows5_0,table53Rows5_1,table53Rows5_2,table53Rows5_3,table53Rows5_4,table53Rows5_5,table53Rows6_0,table53Rows6_1,table53Rows6_2,table53Rows6_3,table53Rows6_4,table53Rows6_5,table53Rows7_0,table53Rows7_1,table53Rows7_2,table53Rows7_3,table53Rows7_4,table53Rows7_5,table53Rows8_0,table53Rows8_1,table53Rows8_2,table53Rows8_3,table53Rows8_4,table53Rows8_5]
    root5Node21Domains0 root5Node21Domains1 (by
      simp only [List.all_cons, List.all_nil, root5Node21Step1Chunk0_0_checked, root5Node21Step1Chunk0_1_checked, root5Node21Step1Chunk0_2_checked, root5Node21Step1Chunk0_3_checked, root5Node21Step1Chunk0_4_checked, root5Node21Step1Chunk0_5_checked, root5Node21Step1Chunk1_0_checked, root5Node21Step1Chunk1_1_checked, root5Node21Step1Chunk1_2_checked, root5Node21Step1Chunk1_3_checked, root5Node21Step1Chunk1_4_checked, root5Node21Step1Chunk1_5_checked, root5Node21Step1Chunk2_0_checked, root5Node21Step1Chunk2_1_checked, root5Node21Step1Chunk2_2_checked, root5Node21Step1Chunk2_3_checked, root5Node21Step1Chunk2_4_checked, root5Node21Step1Chunk2_5_checked, root5Node21Step1Chunk3_0_checked, root5Node21Step1Chunk3_1_checked, root5Node21Step1Chunk3_2_checked, root5Node21Step1Chunk3_3_checked, root5Node21Step1Chunk3_4_checked, root5Node21Step1Chunk3_5_checked, root5Node21Step1Chunk4_0_checked, root5Node21Step1Chunk4_1_checked, root5Node21Step1Chunk4_2_checked, root5Node21Step1Chunk4_3_checked, root5Node21Step1Chunk4_4_checked, root5Node21Step1Chunk4_5_checked, root5Node21Step1Chunk5_0_checked, root5Node21Step1Chunk5_1_checked, root5Node21Step1Chunk5_2_checked, root5Node21Step1Chunk5_3_checked, root5Node21Step1Chunk5_4_checked, root5Node21Step1Chunk5_5_checked, root5Node21Step1Chunk6_0_checked, root5Node21Step1Chunk6_1_checked, root5Node21Step1Chunk6_2_checked, root5Node21Step1Chunk6_3_checked, root5Node21Step1Chunk6_4_checked, root5Node21Step1Chunk6_5_checked, root5Node21Step1Chunk7_0_checked, root5Node21Step1Chunk7_1_checked, root5Node21Step1Chunk7_2_checked, root5Node21Step1Chunk7_3_checked, root5Node21Step1Chunk7_4_checked, root5Node21Step1Chunk7_5_checked, root5Node21Step1Chunk8_0_checked, root5Node21Step1Chunk8_1_checked, root5Node21Step1Chunk8_2_checked, root5Node21Step1Chunk8_3_checked, root5Node21Step1Chunk8_4_checked, root5Node21Step1Chunk8_5_checked, Bool.true_and])
theorem root5Node21Step1_checked :
    checkReplacement table53 root5Node21Domains0 root5Node21Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root5Node21Domains0 root5Node21Domains1
    root5Node21Domains0Fast root5Node21Domains1Fast
    root5Node21Domains0_fast_eq root5Node21Domains1_fast_eq
    root5Node21Step1Narrowing_checked (by decide)
def root5Node22Domains0 : Domains 91 State := restrict root5Node21Domains1 39 (1,4)
def root5Node22Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(5,0)]
  | 4 => some [(4,5)]
  | 5 => some [(7,0)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(0,0)]
  | 11 => some [(7,2)]
  | 12 => some [(7,4)]
  | 13 => some [(8,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(1,5)]
  | 18 => some [(6,1)]
  | 19 => some [(4,1)]
  | 20 => some [(0,2)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(2,0)]
  | 27 => some [(7,3)]
  | 28 => some [(5,2)]
  | 29 => some [(8,0)]
  | 30 => some [(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(3,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(1,4)]
  | 40 => some [(1,3),(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(0,3),(6,0)]
  | 51 => some [(0,4),(6,2)]
  | 52 => some [(5,4),(8,4)]
  | 53 => some [(6,4)]
  | 54 => some [(1,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(4,2),(8,2)]
  | 61 => some [(4,3),(7,1)]
  | 62 => some [(7,5)]
  | 63 => some [(0,3)]
  | 64 => some [(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(4,2)]
  | 72 => some [(5,3)]
  | 73 => some [(5,5),(8,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(1,0)]
  | 78 => some [(0,4),(1,2),(6,2)]
  | 79 => some [(1,4),(3,4),(7,4)]
  | 80 => some [(0,5),(6,3)]
  | 81 => some [(4,4),(7,2)]
  | 82 => some [(1,4),(7,4)]
  | 83 => some [(0,5),(1,3),(6,3)]
  | 84 => some [(4,4),(7,2),(8,2)]
  | 85 => some [(2,1),(2,3),(2,5),(4,1)]
  | 86 => some [(0,2),(6,0)]
  | 87 => some [(1,1),(7,1)]
  | 88 => some [(4,1),(7,5),(8,1)]
  | 89 => some [(0,2),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root5Node22Domains0_fast_eq : root5Node22Domains0 = expandDomains root5Node22Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node22Domains0 v = expandDomains root5Node22Domains0Fast v from by decide) v
def root5Node22Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(5,0)]
  | 4 => [(4,5)]
  | 5 => [(7,0)]
  | 6 => [(8,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(0,0)]
  | 11 => [(7,2)]
  | 12 => [(7,4)]
  | 13 => [(8,3)]
  | 14 => [(5,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(1,5)]
  | 18 => [(6,1)]
  | 19 => [(4,1)]
  | 20 => [(0,2)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(2,0)]
  | 27 => [(7,3)]
  | 28 => [(5,2)]
  | 29 => [(8,0)]
  | 30 => [(7,5)]
  | 31 => [(6,0)]
  | 32 => [(7,1)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(3,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(1,4)]
  | 40 => [(1,3),(7,3)]
  | 41 => [(8,2)]
  | 42 => [(8,0)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(6,0)]
  | 51 => [(0,4),(6,2)]
  | 52 => [(5,4),(8,4)]
  | 53 => [(6,4)]
  | 54 => [(1,2)]
  | 55 => [(8,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(4,0)]
  | 59 => [(7,3)]
  | 60 => [(8,2)]
  | 61 => [(4,3),(7,1)]
  | 62 => [(7,5)]
  | 63 => [(0,3)]
  | 64 => [(8,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(5,1)]
  | 68 => [(0,1)]
  | 69 => [(6,2)]
  | 70 => [(1,3),(7,3)]
  | 71 => [(4,2)]
  | 72 => [(5,3)]
  | 73 => [(8,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(8,5)]
  | 77 => [(1,0)]
  | 78 => [(0,4),(1,2),(6,2)]
  | 79 => [(1,4),(3,4),(7,4)]
  | 80 => [(6,3)]
  | 81 => [(7,2)]
  | 82 => [(7,4)]
  | 83 => [(1,3),(6,3)]
  | 84 => [(7,2),(8,2)]
  | 85 => [(2,1),(2,3),(2,5),(4,1)]
  | 86 => [(0,2),(6,0)]
  | 87 => [(1,1)]
  | 88 => [(4,1),(8,1)]
  | 89 => [(0,2),(6,5)]
  | _ => [(0,4),(1,1)]
def root5Node22Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(5,0)]
  | 4 => some [(4,5)]
  | 5 => some [(7,0)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(0,0)]
  | 11 => some [(7,2)]
  | 12 => some [(7,4)]
  | 13 => some [(8,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(1,5)]
  | 18 => some [(6,1)]
  | 19 => some [(4,1)]
  | 20 => some [(0,2)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(2,0)]
  | 27 => some [(7,3)]
  | 28 => some [(5,2)]
  | 29 => some [(8,0)]
  | 30 => some [(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(3,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(1,4)]
  | 40 => some [(1,3),(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(6,0)]
  | 51 => some [(0,4),(6,2)]
  | 52 => some [(5,4),(8,4)]
  | 53 => some [(6,4)]
  | 54 => some [(1,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(8,2)]
  | 61 => some [(4,3),(7,1)]
  | 62 => some [(7,5)]
  | 63 => some [(0,3)]
  | 64 => some [(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(4,2)]
  | 72 => some [(5,3)]
  | 73 => some [(8,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(8,5)]
  | 77 => some [(1,0)]
  | 78 => some [(0,4),(1,2),(6,2)]
  | 79 => some [(1,4),(3,4),(7,4)]
  | 80 => some [(6,3)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(1,3),(6,3)]
  | 84 => some [(7,2),(8,2)]
  | 85 => some [(2,1),(2,3),(2,5),(4,1)]
  | 86 => some [(0,2),(6,0)]
  | 87 => some [(1,1)]
  | 88 => some [(4,1),(8,1)]
  | 89 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root5Node22Domains1_fast_eq : root5Node22Domains1 = expandDomains root5Node22Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node22Domains1 v = expandDomains root5Node22Domains1Fast v from by decide) v
theorem root5Node22Step1Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq (by decide)
theorem root5Node22Step1Narrowing_checked :
    checkNarrowing table57 root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root5Node22Domains0 root5Node22Domains1 (by
      simp only [List.all_cons, List.all_nil, root5Node22Step1Chunk0_0_checked, root5Node22Step1Chunk0_1_checked, root5Node22Step1Chunk0_2_checked, root5Node22Step1Chunk0_3_checked, root5Node22Step1Chunk0_4_checked, root5Node22Step1Chunk0_5_checked, root5Node22Step1Chunk1_0_checked, root5Node22Step1Chunk1_1_checked, root5Node22Step1Chunk1_2_checked, root5Node22Step1Chunk1_3_checked, root5Node22Step1Chunk1_4_checked, root5Node22Step1Chunk1_5_checked, root5Node22Step1Chunk2_0_checked, root5Node22Step1Chunk2_1_checked, root5Node22Step1Chunk2_2_checked, root5Node22Step1Chunk2_3_checked, root5Node22Step1Chunk2_4_checked, root5Node22Step1Chunk2_5_checked, root5Node22Step1Chunk3_0_checked, root5Node22Step1Chunk3_1_checked, root5Node22Step1Chunk3_2_checked, root5Node22Step1Chunk3_3_checked, root5Node22Step1Chunk3_4_checked, root5Node22Step1Chunk3_5_checked, root5Node22Step1Chunk4_0_checked, root5Node22Step1Chunk4_1_checked, root5Node22Step1Chunk4_2_checked, root5Node22Step1Chunk4_3_checked, root5Node22Step1Chunk4_4_checked, root5Node22Step1Chunk4_5_checked, root5Node22Step1Chunk5_0_checked, root5Node22Step1Chunk5_1_checked, root5Node22Step1Chunk5_2_checked, root5Node22Step1Chunk5_3_checked, root5Node22Step1Chunk5_4_checked, root5Node22Step1Chunk5_5_checked, root5Node22Step1Chunk6_0_checked, root5Node22Step1Chunk6_1_checked, root5Node22Step1Chunk6_2_checked, root5Node22Step1Chunk6_3_checked, root5Node22Step1Chunk6_4_checked, root5Node22Step1Chunk6_5_checked, root5Node22Step1Chunk7_0_checked, root5Node22Step1Chunk7_1_checked, root5Node22Step1Chunk7_2_checked, root5Node22Step1Chunk7_3_checked, root5Node22Step1Chunk7_4_checked, root5Node22Step1Chunk7_5_checked, root5Node22Step1Chunk8_0_checked, root5Node22Step1Chunk8_1_checked, root5Node22Step1Chunk8_2_checked, root5Node22Step1Chunk8_3_checked, root5Node22Step1Chunk8_4_checked, root5Node22Step1Chunk8_5_checked, Bool.true_and])
theorem root5Node22Step1_checked :
    checkReplacement table57 root5Node22Domains0 root5Node22Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root5Node22Domains0 root5Node22Domains1
    root5Node22Domains0Fast root5Node22Domains1Fast
    root5Node22Domains0_fast_eq root5Node22Domains1_fast_eq
    root5Node22Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
