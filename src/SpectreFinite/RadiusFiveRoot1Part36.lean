module

public import SpectreFinite.RadiusFiveRoot1Part35
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable10
public import SpectreFinite.RadiusFiveTable21
public import SpectreFinite.RadiusFiveTable65

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node89Domains0 : Domains 91 State := restrict root1Node87Domains1 30 (8,1)
def root1Node89Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,2)]
  | 1 => some [(3,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(1,1)]
  | 7 => some [(0,1)]
  | 8 => some [(6,2)]
  | 9 => some [(8,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(8,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(0,0),(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(4,0),(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(1,1),(6,1)]
  | 62 => some [(4,1),(8,1)]
  | 63 => some [(0,2),(6,5)]
  | 64 => some [(0,4),(1,1)]
  | 65 => some [(5,1),(5,4)]
  | 66 => some [(0,1),(6,4)]
  | 67 => some [(1,2),(6,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(7,3),(8,3)]
  | 71 => some [(5,2),(5,5)]
  | 72 => some [(7,0),(8,0)]
  | 73 => some [(4,3),(8,3)]
  | 74 => some [(3,5),(5,5)]
  | 75 => some [(0,3),(1,0)]
  | 76 => some [(2,1),(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5),(6,2)]
  | 79 => some [(4,4),(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(2,4),(4,4)]
  | 83 => some [(0,0),(1,3)]
  | 84 => some [(3,2),(5,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5),(6,5)]
  | _ => some [(0,4),(6,1)]
theorem root1Node89Domains0_fast_eq : root1Node89Domains0 = expandDomains root1Node89Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node89Domains0 v = expandDomains root1Node89Domains0Fast v from by decide) v
def root1Node89Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,2)]
  | 1 => [(3,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(8,3)]
  | 5 => [(5,5)]
  | 6 => [(1,1)]
  | 7 => [(0,1)]
  | 8 => [(6,2)]
  | 9 => [(8,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(5,0)]
  | 14 => [(4,5)]
  | 15 => [(1,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(8,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(8,4)]
  | 40 => [(5,3)]
  | 41 => [(8,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(8,1)]
  | 50 => [(1,5)]
  | 51 => [(6,3)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3),(6,3)]
  | 55 => [(7,2),(8,2)]
  | 56 => [(4,0),(8,0)]
  | 57 => [(7,3)]
  | 58 => [(4,2)]
  | 59 => [(5,3)]
  | 60 => [(8,5)]
  | 61 => [(1,1)]
  | 62 => [(4,1),(8,1)]
  | 63 => [(0,2),(6,5)]
  | 64 => [(0,4),(1,1)]
  | 65 => [(5,1),(5,4)]
  | 66 => [(0,1),(6,4)]
  | 67 => [(1,2),(6,2)]
  | 68 => [(7,4)]
  | 69 => [(6,3)]
  | 70 => [(7,3),(8,3)]
  | 71 => [(5,2),(5,5)]
  | 72 => [(7,0),(8,0)]
  | 73 => [(4,3),(8,3)]
  | 74 => [(3,5),(5,5)]
  | 75 => [(0,3),(1,0)]
  | 76 => [(2,1),(4,1)]
  | 77 => [(0,2)]
  | 78 => [(0,5),(6,2)]
  | 79 => [(4,4),(8,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(2,4),(4,4)]
  | 83 => [(0,0),(1,3)]
  | 84 => [(3,2),(5,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(7,1)]
  | 89 => [(1,5),(6,5)]
  | _ => [(0,4),(6,1)]
def root1Node89Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,2)]
  | 1 => some [(3,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(1,1)]
  | 7 => some [(0,1)]
  | 8 => some [(6,2)]
  | 9 => some [(8,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(8,4)]
  | 40 => some [(5,3)]
  | 41 => some [(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(4,0),(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(1,1)]
  | 62 => some [(4,1),(8,1)]
  | 63 => some [(0,2),(6,5)]
  | 64 => some [(0,4),(1,1)]
  | 65 => some [(5,1),(5,4)]
  | 66 => some [(0,1),(6,4)]
  | 67 => some [(1,2),(6,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(7,3),(8,3)]
  | 71 => some [(5,2),(5,5)]
  | 72 => some [(7,0),(8,0)]
  | 73 => some [(4,3),(8,3)]
  | 74 => some [(3,5),(5,5)]
  | 75 => some [(0,3),(1,0)]
  | 76 => some [(2,1),(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5),(6,2)]
  | 79 => some [(4,4),(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(2,4),(4,4)]
  | 83 => some [(0,0),(1,3)]
  | 84 => some [(3,2),(5,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5),(6,5)]
  | _ => some [(0,4),(6,1)]
theorem root1Node89Domains1_fast_eq : root1Node89Domains1 = expandDomains root1Node89Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node89Domains1 v = expandDomains root1Node89Domains1Fast v from by decide) v
theorem root1Node89Step1Chunk0_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_0⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk0_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_1⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk0_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_2⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk0_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_3⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk0_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_4⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk0_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_5⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk1_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_0⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk1_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_1⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk1_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_2⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk1_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_3⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk1_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_4⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk1_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_5⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk2_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_0⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk2_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_1⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk2_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_2⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk2_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_3⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk2_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_4⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk2_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_5⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk3_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_0⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk3_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_1⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk3_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_2⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk3_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_3⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk3_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_4⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk3_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_5⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk4_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_0⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk4_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_1⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk4_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_2⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk4_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_3⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk4_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_4⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk4_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_5⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk5_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_0⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk5_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_1⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk5_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_2⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk5_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_3⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk5_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_4⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk5_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_5⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk6_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_0⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk6_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_1⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk6_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_2⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk6_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_3⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk6_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_4⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk6_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_5⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk7_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_0⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk7_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_1⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk7_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_2⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk7_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_3⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk7_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_4⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk7_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_5⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk8_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_0⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk8_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_1⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk8_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_2⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk8_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_3⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk8_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_4⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Chunk8_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_5⟩
      root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq (by decide)
theorem root1Node89Step1Narrowing_checked :
    checkNarrowing table21 root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkNarrowing_flatten table21Scope [table21Rows0_0,table21Rows0_1,table21Rows0_2,table21Rows0_3,table21Rows0_4,table21Rows0_5,table21Rows1_0,table21Rows1_1,table21Rows1_2,table21Rows1_3,table21Rows1_4,table21Rows1_5,table21Rows2_0,table21Rows2_1,table21Rows2_2,table21Rows2_3,table21Rows2_4,table21Rows2_5,table21Rows3_0,table21Rows3_1,table21Rows3_2,table21Rows3_3,table21Rows3_4,table21Rows3_5,table21Rows4_0,table21Rows4_1,table21Rows4_2,table21Rows4_3,table21Rows4_4,table21Rows4_5,table21Rows5_0,table21Rows5_1,table21Rows5_2,table21Rows5_3,table21Rows5_4,table21Rows5_5,table21Rows6_0,table21Rows6_1,table21Rows6_2,table21Rows6_3,table21Rows6_4,table21Rows6_5,table21Rows7_0,table21Rows7_1,table21Rows7_2,table21Rows7_3,table21Rows7_4,table21Rows7_5,table21Rows8_0,table21Rows8_1,table21Rows8_2,table21Rows8_3,table21Rows8_4,table21Rows8_5]
    root1Node89Domains0 root1Node89Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node89Step1Chunk0_0_checked, root1Node89Step1Chunk0_1_checked, root1Node89Step1Chunk0_2_checked, root1Node89Step1Chunk0_3_checked, root1Node89Step1Chunk0_4_checked, root1Node89Step1Chunk0_5_checked, root1Node89Step1Chunk1_0_checked, root1Node89Step1Chunk1_1_checked, root1Node89Step1Chunk1_2_checked, root1Node89Step1Chunk1_3_checked, root1Node89Step1Chunk1_4_checked, root1Node89Step1Chunk1_5_checked, root1Node89Step1Chunk2_0_checked, root1Node89Step1Chunk2_1_checked, root1Node89Step1Chunk2_2_checked, root1Node89Step1Chunk2_3_checked, root1Node89Step1Chunk2_4_checked, root1Node89Step1Chunk2_5_checked, root1Node89Step1Chunk3_0_checked, root1Node89Step1Chunk3_1_checked, root1Node89Step1Chunk3_2_checked, root1Node89Step1Chunk3_3_checked, root1Node89Step1Chunk3_4_checked, root1Node89Step1Chunk3_5_checked, root1Node89Step1Chunk4_0_checked, root1Node89Step1Chunk4_1_checked, root1Node89Step1Chunk4_2_checked, root1Node89Step1Chunk4_3_checked, root1Node89Step1Chunk4_4_checked, root1Node89Step1Chunk4_5_checked, root1Node89Step1Chunk5_0_checked, root1Node89Step1Chunk5_1_checked, root1Node89Step1Chunk5_2_checked, root1Node89Step1Chunk5_3_checked, root1Node89Step1Chunk5_4_checked, root1Node89Step1Chunk5_5_checked, root1Node89Step1Chunk6_0_checked, root1Node89Step1Chunk6_1_checked, root1Node89Step1Chunk6_2_checked, root1Node89Step1Chunk6_3_checked, root1Node89Step1Chunk6_4_checked, root1Node89Step1Chunk6_5_checked, root1Node89Step1Chunk7_0_checked, root1Node89Step1Chunk7_1_checked, root1Node89Step1Chunk7_2_checked, root1Node89Step1Chunk7_3_checked, root1Node89Step1Chunk7_4_checked, root1Node89Step1Chunk7_5_checked, root1Node89Step1Chunk8_0_checked, root1Node89Step1Chunk8_1_checked, root1Node89Step1Chunk8_2_checked, root1Node89Step1Chunk8_3_checked, root1Node89Step1Chunk8_4_checked, root1Node89Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node89Step1_checked :
    checkReplacement table21 root1Node89Domains0 root1Node89Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node89Domains0 root1Node89Domains1
    root1Node89Domains0Fast root1Node89Domains1Fast
    root1Node89Domains0_fast_eq root1Node89Domains1_fast_eq
    root1Node89Step1Narrowing_checked (by decide)
def root1Node90Domains0 : Domains 91 State := restrict root1Node89Domains1 54 (1,3)
def root1Node90Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,2)]
  | 1 => some [(3,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(1,1)]
  | 7 => some [(0,1)]
  | 8 => some [(6,2)]
  | 9 => some [(8,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(8,4)]
  | 40 => some [(5,3)]
  | 41 => some [(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(4,0),(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(1,1)]
  | 62 => some [(4,1),(8,1)]
  | 63 => some [(0,2),(6,5)]
  | 64 => some [(0,4),(1,1)]
  | 65 => some [(5,1),(5,4)]
  | 66 => some [(0,1),(6,4)]
  | 67 => some [(1,2),(6,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(7,3),(8,3)]
  | 71 => some [(5,2),(5,5)]
  | 72 => some [(7,0),(8,0)]
  | 73 => some [(4,3),(8,3)]
  | 74 => some [(3,5),(5,5)]
  | 75 => some [(0,3),(1,0)]
  | 76 => some [(2,1),(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5),(6,2)]
  | 79 => some [(4,4),(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(2,4),(4,4)]
  | 83 => some [(0,0),(1,3)]
  | 84 => some [(3,2),(5,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5),(6,5)]
  | _ => some [(0,4),(6,1)]
theorem root1Node90Domains0_fast_eq : root1Node90Domains0 = expandDomains root1Node90Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node90Domains0 v = expandDomains root1Node90Domains0Fast v from by decide) v
def root1Node90Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,2)]
  | 1 => [(3,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(8,3)]
  | 5 => [(5,5)]
  | 6 => [(1,1)]
  | 7 => [(0,1)]
  | 8 => [(6,2)]
  | 9 => [(8,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(5,0)]
  | 14 => [(4,5)]
  | 15 => [(1,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(8,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(8,4)]
  | 40 => [(5,3)]
  | 41 => [(8,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(8,1)]
  | 50 => [(1,5)]
  | 51 => [(6,3)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3)]
  | 55 => [(8,2)]
  | 56 => [(8,0)]
  | 57 => [(7,3)]
  | 58 => [(4,2)]
  | 59 => [(5,3)]
  | 60 => [(8,5)]
  | 61 => [(1,1)]
  | 62 => [(8,1)]
  | 63 => [(6,5)]
  | 64 => [(0,4)]
  | 65 => [(5,4)]
  | 66 => [(6,4)]
  | 67 => [(1,2)]
  | 68 => [(7,4)]
  | 69 => [(6,3)]
  | 70 => [(8,3)]
  | 71 => [(5,5)]
  | 72 => [(7,0)]
  | 73 => [(4,3)]
  | 74 => [(3,5)]
  | 75 => [(0,3)]
  | 76 => [(4,1)]
  | 77 => [(0,2)]
  | 78 => [(0,5)]
  | 79 => [(4,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(2,4)]
  | 83 => [(1,3)]
  | 84 => [(5,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(7,1)]
  | 89 => [(6,5)]
  | _ => [(0,4)]
def root1Node90Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,2)]
  | 1 => some [(3,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(1,1)]
  | 7 => some [(0,1)]
  | 8 => some [(6,2)]
  | 9 => some [(8,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(8,4)]
  | 40 => some [(5,3)]
  | 41 => some [(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(1,1)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(8,3)]
  | 71 => some [(5,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(3,5)]
  | 75 => some [(0,3)]
  | 76 => some [(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5)]
  | 79 => some [(4,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(2,4)]
  | 83 => some [(1,3)]
  | 84 => some [(5,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(6,5)]
  | _ => some [(0,4)]
theorem root1Node90Domains1_fast_eq : root1Node90Domains1 = expandDomains root1Node90Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node90Domains1 v = expandDomains root1Node90Domains1Fast v from by decide) v
theorem root1Node90Step1Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq (by decide)
theorem root1Node90Step1Narrowing_checked :
    checkNarrowing table65 root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root1Node90Domains0 root1Node90Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node90Step1Chunk0_0_checked, root1Node90Step1Chunk0_1_checked, root1Node90Step1Chunk0_2_checked, root1Node90Step1Chunk0_3_checked, root1Node90Step1Chunk0_4_checked, root1Node90Step1Chunk0_5_checked, root1Node90Step1Chunk1_0_checked, root1Node90Step1Chunk1_1_checked, root1Node90Step1Chunk1_2_checked, root1Node90Step1Chunk1_3_checked, root1Node90Step1Chunk1_4_checked, root1Node90Step1Chunk1_5_checked, root1Node90Step1Chunk2_0_checked, root1Node90Step1Chunk2_1_checked, root1Node90Step1Chunk2_2_checked, root1Node90Step1Chunk2_3_checked, root1Node90Step1Chunk2_4_checked, root1Node90Step1Chunk2_5_checked, root1Node90Step1Chunk3_0_checked, root1Node90Step1Chunk3_1_checked, root1Node90Step1Chunk3_2_checked, root1Node90Step1Chunk3_3_checked, root1Node90Step1Chunk3_4_checked, root1Node90Step1Chunk3_5_checked, root1Node90Step1Chunk4_0_checked, root1Node90Step1Chunk4_1_checked, root1Node90Step1Chunk4_2_checked, root1Node90Step1Chunk4_3_checked, root1Node90Step1Chunk4_4_checked, root1Node90Step1Chunk4_5_checked, root1Node90Step1Chunk5_0_checked, root1Node90Step1Chunk5_1_checked, root1Node90Step1Chunk5_2_checked, root1Node90Step1Chunk5_3_checked, root1Node90Step1Chunk5_4_checked, root1Node90Step1Chunk5_5_checked, root1Node90Step1Chunk6_0_checked, root1Node90Step1Chunk6_1_checked, root1Node90Step1Chunk6_2_checked, root1Node90Step1Chunk6_3_checked, root1Node90Step1Chunk6_4_checked, root1Node90Step1Chunk6_5_checked, root1Node90Step1Chunk7_0_checked, root1Node90Step1Chunk7_1_checked, root1Node90Step1Chunk7_2_checked, root1Node90Step1Chunk7_3_checked, root1Node90Step1Chunk7_4_checked, root1Node90Step1Chunk7_5_checked, root1Node90Step1Chunk8_0_checked, root1Node90Step1Chunk8_1_checked, root1Node90Step1Chunk8_2_checked, root1Node90Step1Chunk8_3_checked, root1Node90Step1Chunk8_4_checked, root1Node90Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node90Step1_checked :
    checkReplacement table65 root1Node90Domains0 root1Node90Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node90Domains0 root1Node90Domains1
    root1Node90Domains0Fast root1Node90Domains1Fast
    root1Node90Domains0_fast_eq root1Node90Domains1_fast_eq
    root1Node90Step1Narrowing_checked (by decide)
theorem root1Node90Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node90Domains1 (.output 44) = true := by decide
def root1Node91Domains0 : Domains 91 State := restrict root1Node89Domains1 54 (6,3)
def root1Node91Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,2)]
  | 1 => some [(3,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(1,1)]
  | 7 => some [(0,1)]
  | 8 => some [(6,2)]
  | 9 => some [(8,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(8,4)]
  | 40 => some [(5,3)]
  | 41 => some [(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(4,0),(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(1,1)]
  | 62 => some [(4,1),(8,1)]
  | 63 => some [(0,2),(6,5)]
  | 64 => some [(0,4),(1,1)]
  | 65 => some [(5,1),(5,4)]
  | 66 => some [(0,1),(6,4)]
  | 67 => some [(1,2),(6,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(7,3),(8,3)]
  | 71 => some [(5,2),(5,5)]
  | 72 => some [(7,0),(8,0)]
  | 73 => some [(4,3),(8,3)]
  | 74 => some [(3,5),(5,5)]
  | 75 => some [(0,3),(1,0)]
  | 76 => some [(2,1),(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5),(6,2)]
  | 79 => some [(4,4),(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(2,4),(4,4)]
  | 83 => some [(0,0),(1,3)]
  | 84 => some [(3,2),(5,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5),(6,5)]
  | _ => some [(0,4),(6,1)]
theorem root1Node91Domains0_fast_eq : root1Node91Domains0 = expandDomains root1Node91Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node91Domains0 v = expandDomains root1Node91Domains0Fast v from by decide) v
def root1Node91Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,2)]
  | 1 => [(3,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(8,3)]
  | 5 => [(5,5)]
  | 6 => [(1,1)]
  | 7 => [(0,1)]
  | 8 => [(6,2)]
  | 9 => [(8,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(5,0)]
  | 14 => [(4,5)]
  | 15 => [(1,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(8,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(8,4)]
  | 40 => [(5,3)]
  | 41 => [(8,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(8,1)]
  | 50 => [(1,5)]
  | 51 => [(6,3)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(4,0)]
  | 57 => [(7,3)]
  | 58 => [(4,2)]
  | 59 => [(5,3)]
  | 60 => [(8,5)]
  | 61 => [(1,1)]
  | 62 => [(4,1)]
  | 63 => [(0,2)]
  | 64 => [(1,1)]
  | 65 => [(5,1)]
  | 66 => [(0,1)]
  | 67 => [(6,2)]
  | 68 => [(7,4)]
  | 69 => [(6,3)]
  | 70 => [(7,3)]
  | 71 => [(5,2)]
  | 72 => [(8,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5)]
  | 75 => [(1,0)]
  | 76 => [(2,1)]
  | 77 => [(0,2)]
  | 78 => [(6,2)]
  | 79 => [(8,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(4,4)]
  | 83 => [(0,0)]
  | 84 => [(3,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(7,1)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root1Node91Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,2)]
  | 1 => some [(3,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(1,1)]
  | 7 => some [(0,1)]
  | 8 => some [(6,2)]
  | 9 => some [(8,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(8,4)]
  | 40 => some [(5,3)]
  | 41 => some [(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(4,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(1,1)]
  | 62 => some [(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(5,1)]
  | 66 => some [(0,1)]
  | 67 => some [(6,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2)]
  | 72 => some [(8,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(1,0)]
  | 76 => some [(2,1)]
  | 77 => some [(0,2)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(0,0)]
  | 84 => some [(3,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root1Node91Domains1_fast_eq : root1Node91Domains1 = expandDomains root1Node91Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node91Domains1 v = expandDomains root1Node91Domains1Fast v from by decide) v
theorem root1Node91Step1Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq (by decide)
theorem root1Node91Step1Narrowing_checked :
    checkNarrowing table65 root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root1Node91Domains0 root1Node91Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node91Step1Chunk0_0_checked, root1Node91Step1Chunk0_1_checked, root1Node91Step1Chunk0_2_checked, root1Node91Step1Chunk0_3_checked, root1Node91Step1Chunk0_4_checked, root1Node91Step1Chunk0_5_checked, root1Node91Step1Chunk1_0_checked, root1Node91Step1Chunk1_1_checked, root1Node91Step1Chunk1_2_checked, root1Node91Step1Chunk1_3_checked, root1Node91Step1Chunk1_4_checked, root1Node91Step1Chunk1_5_checked, root1Node91Step1Chunk2_0_checked, root1Node91Step1Chunk2_1_checked, root1Node91Step1Chunk2_2_checked, root1Node91Step1Chunk2_3_checked, root1Node91Step1Chunk2_4_checked, root1Node91Step1Chunk2_5_checked, root1Node91Step1Chunk3_0_checked, root1Node91Step1Chunk3_1_checked, root1Node91Step1Chunk3_2_checked, root1Node91Step1Chunk3_3_checked, root1Node91Step1Chunk3_4_checked, root1Node91Step1Chunk3_5_checked, root1Node91Step1Chunk4_0_checked, root1Node91Step1Chunk4_1_checked, root1Node91Step1Chunk4_2_checked, root1Node91Step1Chunk4_3_checked, root1Node91Step1Chunk4_4_checked, root1Node91Step1Chunk4_5_checked, root1Node91Step1Chunk5_0_checked, root1Node91Step1Chunk5_1_checked, root1Node91Step1Chunk5_2_checked, root1Node91Step1Chunk5_3_checked, root1Node91Step1Chunk5_4_checked, root1Node91Step1Chunk5_5_checked, root1Node91Step1Chunk6_0_checked, root1Node91Step1Chunk6_1_checked, root1Node91Step1Chunk6_2_checked, root1Node91Step1Chunk6_3_checked, root1Node91Step1Chunk6_4_checked, root1Node91Step1Chunk6_5_checked, root1Node91Step1Chunk7_0_checked, root1Node91Step1Chunk7_1_checked, root1Node91Step1Chunk7_2_checked, root1Node91Step1Chunk7_3_checked, root1Node91Step1Chunk7_4_checked, root1Node91Step1Chunk7_5_checked, root1Node91Step1Chunk8_0_checked, root1Node91Step1Chunk8_1_checked, root1Node91Step1Chunk8_2_checked, root1Node91Step1Chunk8_3_checked, root1Node91Step1Chunk8_4_checked, root1Node91Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node91Step1_checked :
    checkReplacement table65 root1Node91Domains0 root1Node91Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node91Domains0 root1Node91Domains1
    root1Node91Domains0Fast root1Node91Domains1Fast
    root1Node91Domains0_fast_eq root1Node91Domains1_fast_eq
    root1Node91Step1Narrowing_checked (by decide)
theorem root1Node91Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node91Domains1 (.output 45) = true := by decide
def root1Node92Domains0 : Domains 91 State := restrict root1Node76Domains3 1 (7,3)
def root1Node92Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,0),(2,2),(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2),(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3),(8,3)]
  | 5 => some [(4,2),(5,2),(5,5),(8,2)]
  | 6 => some [(1,1),(3,1),(5,1)]
  | 7 => some [(0,1)]
  | 8 => some [(6,2)]
  | 9 => some [(8,4)]
  | 10 => some [(1,4),(6,4)]
  | 11 => some [(0,5),(1,2)]
  | 12 => some [(4,4),(7,4),(8,4)]
  | 13 => some [(5,0),(5,3),(8,3)]
  | 14 => some [(4,5),(8,5)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3),(6,0)]
  | 19 => some [(7,1),(8,1)]
  | 20 => some [(1,5),(6,5),(7,5)]
  | 21 => some [(7,4),(8,4)]
  | 22 => some [(0,0),(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(4,2),(8,2)]
  | 27 => some [(5,0),(5,3),(8,0)]
  | 28 => some [(4,5),(7,3),(8,5)]
  | 29 => some [(4,2),(7,0),(8,2)]
  | 30 => some [(4,1),(7,1),(8,1)]
  | 31 => some [(0,2),(1,5)]
  | 32 => some [(1,1),(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(7,4),(8,4)]
  | 37 => some [(0,0),(6,3),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4),(8,4)]
  | 40 => some [(1,3),(3,3),(5,0),(5,3),(7,3)]
  | 41 => some [(4,5),(5,2),(5,5),(8,5)]
  | 42 => some [(7,0),(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(2,1),(7,1)]
  | 47 => some [(0,2),(1,5),(7,5)]
  | 48 => some [(0,3),(1,1),(6,1)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(1,5),(6,5)]
  | 51 => some [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 52 => some [(4,4),(5,4),(7,2),(8,4)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(1,3),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2)]
  | 56 => some [(0,0),(4,0),(5,0),(8,0)]
  | 57 => some [(3,2),(4,5),(7,3)]
  | 58 => some [(4,0),(4,2),(7,0)]
  | 59 => some [(5,3),(7,3),(8,3)]
  | 60 => some [(5,2),(8,5)]
  | 61 => some [(1,1),(4,3),(6,1),(7,1)]
  | 62 => some [(4,1),(7,5),(8,1)]
  | 63 => some [(0,2),(6,0),(6,5)]
  | 64 => some [(0,4),(1,1),(7,1)]
  | 65 => some [(1,5),(5,1),(5,4)]
  | 66 => some [(0,0),(0,1),(6,1),(6,4)]
  | 67 => some [(1,2),(5,1),(6,2),(7,2)]
  | 68 => some [(0,1),(7,4)]
  | 69 => some [(6,2),(6,3)]
  | 70 => some [(1,3),(7,3),(8,3)]
  | 71 => some [(5,2),(5,5),(8,2)]
  | 72 => some [(5,0),(7,0),(8,0)]
  | 73 => some [(4,3),(4,5),(8,3)]
  | 74 => some [(1,5),(3,5),(5,5),(7,0)]
  | 75 => some [(0,3),(1,0),(6,1),(8,3)]
  | 76 => some [(2,1),(4,1),(8,5)]
  | 77 => some [(0,2),(1,0)]
  | 78 => some [(0,4),(0,5),(1,2),(6,2)]
  | 79 => some [(4,4),(5,4),(8,4)]
  | 80 => some [(0,0),(1,4)]
  | 81 => some [(0,5),(7,2)]
  | 82 => some [(2,0),(2,4),(4,4),(7,4)]
  | 83 => some [(0,0),(1,3),(6,3),(7,3)]
  | 84 => some [(3,2),(5,2),(7,2),(8,2)]
  | 85 => some [(4,3),(7,1),(8,1)]
  | 86 => some [(1,5),(7,5)]
  | 87 => some [(6,0),(6,1)]
  | 88 => some [(3,1),(4,1),(7,1),(8,1)]
  | 89 => some [(0,1),(0,2),(1,5),(6,5)]
  | _ => some [(0,4),(1,1),(6,1),(6,2)]
theorem root1Node92Domains0_fast_eq : root1Node92Domains0 = expandDomains root1Node92Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node92Domains0 v = expandDomains root1Node92Domains0Fast v from by decide) v
def root1Node92Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,0),(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2),(8,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3),(8,3)]
  | 5 => [(4,2),(5,2),(5,5),(8,2)]
  | 6 => [(3,1),(5,1)]
  | 7 => [(0,1)]
  | 8 => [(6,2)]
  | 9 => [(8,4)]
  | 10 => [(1,4),(6,4)]
  | 11 => [(0,5),(1,2)]
  | 12 => [(4,4),(7,4),(8,4)]
  | 13 => [(5,0),(5,3),(8,3)]
  | 14 => [(4,5),(8,5)]
  | 15 => [(1,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(0,3),(6,0)]
  | 19 => [(7,1),(8,1)]
  | 20 => [(1,5),(6,5),(7,5)]
  | 21 => [(7,4),(8,4)]
  | 22 => [(0,0),(6,3)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(4,2),(8,2)]
  | 27 => [(5,0),(5,3),(8,0)]
  | 28 => [(4,5),(7,3),(8,5)]
  | 29 => [(4,2),(7,0)]
  | 30 => [(4,1),(7,1),(8,1)]
  | 31 => [(0,2),(1,5)]
  | 32 => [(1,1),(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(7,4),(8,4)]
  | 37 => [(0,0),(6,3),(6,4)]
  | 38 => [(1,2),(7,2)]
  | 39 => [(7,4),(8,4)]
  | 40 => [(1,3),(3,3),(5,0),(5,3),(7,3)]
  | 41 => [(4,5),(5,2),(5,5),(8,5)]
  | 42 => [(7,0),(8,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5),(8,5)]
  | 45 => [(1,0)]
  | 46 => [(2,1),(7,1)]
  | 47 => [(0,2),(1,5),(7,5)]
  | 48 => [(0,3),(1,1),(6,1)]
  | 49 => [(4,1),(8,1)]
  | 50 => [(0,2),(1,5),(6,5)]
  | 51 => [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 52 => [(4,4),(5,4),(7,2),(8,4)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(0,5),(1,3),(6,3)]
  | 55 => [(4,4),(7,2),(8,2)]
  | 56 => [(0,0),(4,0),(5,0),(8,0)]
  | 57 => [(3,2),(4,5),(7,3)]
  | 58 => [(4,0),(4,2),(7,0)]
  | 59 => [(5,3),(7,3),(8,3)]
  | 60 => [(5,2),(8,5)]
  | 61 => [(1,1),(4,3),(6,1),(7,1)]
  | 62 => [(4,1),(7,5),(8,1)]
  | 63 => [(0,2),(6,0),(6,5)]
  | 64 => [(0,4),(1,1),(7,1)]
  | 65 => [(1,5),(5,1),(5,4)]
  | 66 => [(0,0),(0,1),(6,1),(6,4)]
  | 67 => [(1,2),(5,1),(6,2),(7,2)]
  | 68 => [(0,1),(7,4)]
  | 69 => [(6,2),(6,3)]
  | 70 => [(1,3),(7,3),(8,3)]
  | 71 => [(5,2),(5,5),(8,2)]
  | 72 => [(5,0),(7,0),(8,0)]
  | 73 => [(4,3),(4,5),(8,3)]
  | 74 => [(1,5),(3,5),(5,5),(7,0)]
  | 75 => [(0,3),(1,0),(6,1),(8,3)]
  | 76 => [(2,1),(4,1),(8,5)]
  | 77 => [(0,2),(1,0)]
  | 78 => [(0,4),(0,5),(1,2),(6,2)]
  | 79 => [(4,4),(5,4),(8,4)]
  | 80 => [(0,0),(1,4)]
  | 81 => [(0,5),(7,2)]
  | 82 => [(2,0),(2,4),(4,4),(7,4)]
  | 83 => [(0,0),(1,3),(6,3),(7,3)]
  | 84 => [(3,2),(5,2),(7,2),(8,2)]
  | 85 => [(4,3),(7,1),(8,1)]
  | 86 => [(1,5),(7,5)]
  | 87 => [(6,0),(6,1)]
  | 88 => [(3,1),(4,1),(7,1),(8,1)]
  | 89 => [(0,1),(0,2),(1,5),(6,5)]
  | _ => [(0,4),(1,1),(6,1),(6,2)]
def root1Node92Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,0),(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2),(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3),(8,3)]
  | 5 => some [(4,2),(5,2),(5,5),(8,2)]
  | 6 => some [(3,1),(5,1)]
  | 7 => some [(0,1)]
  | 8 => some [(6,2)]
  | 9 => some [(8,4)]
  | 10 => some [(1,4),(6,4)]
  | 11 => some [(0,5),(1,2)]
  | 12 => some [(4,4),(7,4),(8,4)]
  | 13 => some [(5,0),(5,3),(8,3)]
  | 14 => some [(4,5),(8,5)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3),(6,0)]
  | 19 => some [(7,1),(8,1)]
  | 20 => some [(1,5),(6,5),(7,5)]
  | 21 => some [(7,4),(8,4)]
  | 22 => some [(0,0),(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(4,2),(8,2)]
  | 27 => some [(5,0),(5,3),(8,0)]
  | 28 => some [(4,5),(7,3),(8,5)]
  | 29 => some [(4,2),(7,0)]
  | 30 => some [(4,1),(7,1),(8,1)]
  | 31 => some [(0,2),(1,5)]
  | 32 => some [(1,1),(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(7,4),(8,4)]
  | 37 => some [(0,0),(6,3),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4),(8,4)]
  | 40 => some [(1,3),(3,3),(5,0),(5,3),(7,3)]
  | 41 => some [(4,5),(5,2),(5,5),(8,5)]
  | 42 => some [(7,0),(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(2,1),(7,1)]
  | 47 => some [(0,2),(1,5),(7,5)]
  | 48 => some [(0,3),(1,1),(6,1)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(1,5),(6,5)]
  | 51 => some [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 52 => some [(4,4),(5,4),(7,2),(8,4)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(1,3),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2)]
  | 56 => some [(0,0),(4,0),(5,0),(8,0)]
  | 57 => some [(3,2),(4,5),(7,3)]
  | 58 => some [(4,0),(4,2),(7,0)]
  | 59 => some [(5,3),(7,3),(8,3)]
  | 60 => some [(5,2),(8,5)]
  | 61 => some [(1,1),(4,3),(6,1),(7,1)]
  | 62 => some [(4,1),(7,5),(8,1)]
  | 63 => some [(0,2),(6,0),(6,5)]
  | 64 => some [(0,4),(1,1),(7,1)]
  | 65 => some [(1,5),(5,1),(5,4)]
  | 66 => some [(0,0),(0,1),(6,1),(6,4)]
  | 67 => some [(1,2),(5,1),(6,2),(7,2)]
  | 68 => some [(0,1),(7,4)]
  | 69 => some [(6,2),(6,3)]
  | 70 => some [(1,3),(7,3),(8,3)]
  | 71 => some [(5,2),(5,5),(8,2)]
  | 72 => some [(5,0),(7,0),(8,0)]
  | 73 => some [(4,3),(4,5),(8,3)]
  | 74 => some [(1,5),(3,5),(5,5),(7,0)]
  | 75 => some [(0,3),(1,0),(6,1),(8,3)]
  | 76 => some [(2,1),(4,1),(8,5)]
  | 77 => some [(0,2),(1,0)]
  | 78 => some [(0,4),(0,5),(1,2),(6,2)]
  | 79 => some [(4,4),(5,4),(8,4)]
  | 80 => some [(0,0),(1,4)]
  | 81 => some [(0,5),(7,2)]
  | 82 => some [(2,0),(2,4),(4,4),(7,4)]
  | 83 => some [(0,0),(1,3),(6,3),(7,3)]
  | 84 => some [(3,2),(5,2),(7,2),(8,2)]
  | 85 => some [(4,3),(7,1),(8,1)]
  | 86 => some [(1,5),(7,5)]
  | 87 => some [(6,0),(6,1)]
  | 88 => some [(3,1),(4,1),(7,1),(8,1)]
  | 89 => some [(0,1),(0,2),(1,5),(6,5)]
  | _ => some [(0,4),(1,1),(6,1),(6,2)]
theorem root1Node92Domains1_fast_eq : root1Node92Domains1 = expandDomains root1Node92Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node92Domains1 v = expandDomains root1Node92Domains1Fast v from by decide) v
theorem root1Node92Step1Chunk0_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_0⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk0_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_1⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk0_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_2⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk0_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_3⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk0_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_4⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk0_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_5⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk1_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_0⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk1_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_1⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk1_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_2⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk1_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_3⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk1_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_4⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk1_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_5⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk2_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_0⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk2_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_1⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk2_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_2⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk2_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_3⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk2_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_4⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk2_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_5⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk3_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_0⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk3_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_1⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk3_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_2⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk3_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_3⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk3_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_4⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk3_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_5⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk4_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_0⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk4_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_1⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk4_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_2⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk4_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_3⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk4_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_4⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk4_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_5⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk5_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_0⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk5_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_1⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk5_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_2⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk5_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_3⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk5_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_4⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk5_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_5⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk6_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_0⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk6_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_1⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk6_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_2⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk6_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_3⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk6_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_4⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk6_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_5⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk7_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_0⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk7_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_1⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk7_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_2⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk7_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_3⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk7_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_4⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk7_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_5⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk8_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_0⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk8_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_1⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk8_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_2⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk8_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_3⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk8_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_4⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Chunk8_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_5⟩
      root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq (by decide)
theorem root1Node92Step1Narrowing_checked :
    checkNarrowing table10 root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkNarrowing_flatten table10Scope [table10Rows0_0,table10Rows0_1,table10Rows0_2,table10Rows0_3,table10Rows0_4,table10Rows0_5,table10Rows1_0,table10Rows1_1,table10Rows1_2,table10Rows1_3,table10Rows1_4,table10Rows1_5,table10Rows2_0,table10Rows2_1,table10Rows2_2,table10Rows2_3,table10Rows2_4,table10Rows2_5,table10Rows3_0,table10Rows3_1,table10Rows3_2,table10Rows3_3,table10Rows3_4,table10Rows3_5,table10Rows4_0,table10Rows4_1,table10Rows4_2,table10Rows4_3,table10Rows4_4,table10Rows4_5,table10Rows5_0,table10Rows5_1,table10Rows5_2,table10Rows5_3,table10Rows5_4,table10Rows5_5,table10Rows6_0,table10Rows6_1,table10Rows6_2,table10Rows6_3,table10Rows6_4,table10Rows6_5,table10Rows7_0,table10Rows7_1,table10Rows7_2,table10Rows7_3,table10Rows7_4,table10Rows7_5,table10Rows8_0,table10Rows8_1,table10Rows8_2,table10Rows8_3,table10Rows8_4,table10Rows8_5]
    root1Node92Domains0 root1Node92Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node92Step1Chunk0_0_checked, root1Node92Step1Chunk0_1_checked, root1Node92Step1Chunk0_2_checked, root1Node92Step1Chunk0_3_checked, root1Node92Step1Chunk0_4_checked, root1Node92Step1Chunk0_5_checked, root1Node92Step1Chunk1_0_checked, root1Node92Step1Chunk1_1_checked, root1Node92Step1Chunk1_2_checked, root1Node92Step1Chunk1_3_checked, root1Node92Step1Chunk1_4_checked, root1Node92Step1Chunk1_5_checked, root1Node92Step1Chunk2_0_checked, root1Node92Step1Chunk2_1_checked, root1Node92Step1Chunk2_2_checked, root1Node92Step1Chunk2_3_checked, root1Node92Step1Chunk2_4_checked, root1Node92Step1Chunk2_5_checked, root1Node92Step1Chunk3_0_checked, root1Node92Step1Chunk3_1_checked, root1Node92Step1Chunk3_2_checked, root1Node92Step1Chunk3_3_checked, root1Node92Step1Chunk3_4_checked, root1Node92Step1Chunk3_5_checked, root1Node92Step1Chunk4_0_checked, root1Node92Step1Chunk4_1_checked, root1Node92Step1Chunk4_2_checked, root1Node92Step1Chunk4_3_checked, root1Node92Step1Chunk4_4_checked, root1Node92Step1Chunk4_5_checked, root1Node92Step1Chunk5_0_checked, root1Node92Step1Chunk5_1_checked, root1Node92Step1Chunk5_2_checked, root1Node92Step1Chunk5_3_checked, root1Node92Step1Chunk5_4_checked, root1Node92Step1Chunk5_5_checked, root1Node92Step1Chunk6_0_checked, root1Node92Step1Chunk6_1_checked, root1Node92Step1Chunk6_2_checked, root1Node92Step1Chunk6_3_checked, root1Node92Step1Chunk6_4_checked, root1Node92Step1Chunk6_5_checked, root1Node92Step1Chunk7_0_checked, root1Node92Step1Chunk7_1_checked, root1Node92Step1Chunk7_2_checked, root1Node92Step1Chunk7_3_checked, root1Node92Step1Chunk7_4_checked, root1Node92Step1Chunk7_5_checked, root1Node92Step1Chunk8_0_checked, root1Node92Step1Chunk8_1_checked, root1Node92Step1Chunk8_2_checked, root1Node92Step1Chunk8_3_checked, root1Node92Step1Chunk8_4_checked, root1Node92Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node92Step1_checked :
    checkReplacement table10 root1Node92Domains0 root1Node92Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node92Domains0 root1Node92Domains1
    root1Node92Domains0Fast root1Node92Domains1Fast
    root1Node92Domains0_fast_eq root1Node92Domains1_fast_eq
    root1Node92Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
