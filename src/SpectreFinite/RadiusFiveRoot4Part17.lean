module

public import SpectreFinite.RadiusFiveRoot4Part16
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable35
public import SpectreFinite.RadiusFiveTable52
public import SpectreFinite.RadiusFiveTable55
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node45Domains0 : Domains 91 State := restrict root4Node39Domains1 39 (8,1)
def root4Node45Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(7,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(8,1)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(5,1)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(1,0)]
  | 33 => some [(2,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(8,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(0,0)]
  | 44 => some [(3,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3),(8,3)]
  | 50 => some [(5,2),(5,5)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(1,4),(6,4)]
  | 60 => some [(0,5),(1,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3),(6,0)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3),(6,3)]
  | 74 => some [(7,2),(8,2)]
  | 75 => some [(4,0),(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2),(8,2)]
  | 78 => some [(6,1)]
  | 79 => some [(4,1),(8,1)]
  | 80 => some [(0,2),(6,5)]
  | 81 => some [(0,4),(1,1)]
  | 82 => some [(5,1),(5,4)]
  | 83 => some [(0,1),(6,4)]
  | 84 => some [(1,2),(6,2)]
  | 85 => some [(7,3),(8,3)]
  | 86 => some [(5,2),(5,5),(8,5)]
  | 87 => some [(7,0),(8,0)]
  | 88 => some [(4,3),(8,3)]
  | 89 => some [(3,5),(5,5),(7,5)]
  | _ => some [(0,3),(1,0)]
theorem root4Node45Domains0_fast_eq : root4Node45Domains0 = expandDomains root4Node45Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node45Domains0 v = expandDomains root4Node45Domains0Fast v from by decide) v
def root4Node45Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(8,4)]
  | 4 => [(0,0)]
  | 5 => [(7,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(1,5)]
  | 11 => [(6,1)]
  | 12 => [(8,1)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(5,1)]
  | 22 => [(0,1)]
  | 23 => [(6,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => [(7,2)]
  | 30 => [(8,3)]
  | 31 => [(5,5)]
  | 32 => [(1,0)]
  | 33 => [(2,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => [(8,1)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(0,0)]
  | 44 => [(3,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(8,0)]
  | 49 => [(8,3)]
  | 50 => [(5,5)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(1,4)]
  | 60 => [(0,5)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(7,0)]
  | 64 => [(8,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(6,0)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(8,2)]
  | 75 => [(8,0)]
  | 76 => [(7,3)]
  | 77 => [(8,2)]
  | 78 => [(6,1)]
  | 79 => [(4,1),(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(5,4)]
  | 83 => [(6,4)]
  | 84 => [(1,2)]
  | 85 => [(7,3),(8,3)]
  | 86 => [(5,2),(5,5),(8,5)]
  | 87 => [(7,0)]
  | 88 => [(4,3)]
  | 89 => [(7,5)]
  | _ => [(0,3)]
def root4Node45Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(7,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(8,1)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(5,1)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(1,0)]
  | 33 => some [(2,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(8,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(0,0)]
  | 44 => some [(3,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(8,0)]
  | 49 => some [(8,3)]
  | 50 => some [(5,5)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(1,4)]
  | 60 => some [(0,5)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(6,0)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(8,2)]
  | 78 => some [(6,1)]
  | 79 => some [(4,1),(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(7,3),(8,3)]
  | 86 => some [(5,2),(5,5),(8,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(7,5)]
  | _ => some [(0,3)]
theorem root4Node45Domains1_fast_eq : root4Node45Domains1 = expandDomains root4Node45Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node45Domains1 v = expandDomains root4Node45Domains1Fast v from by decide) v
theorem root4Node45Step1Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Narrowing_checked :
    checkNarrowing table57 root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root4Node45Domains0 root4Node45Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node45Step1Chunk0_0_checked, root4Node45Step1Chunk0_1_checked, root4Node45Step1Chunk0_2_checked, root4Node45Step1Chunk0_3_checked, root4Node45Step1Chunk0_4_checked, root4Node45Step1Chunk0_5_checked, root4Node45Step1Chunk1_0_checked, root4Node45Step1Chunk1_1_checked, root4Node45Step1Chunk1_2_checked, root4Node45Step1Chunk1_3_checked, root4Node45Step1Chunk1_4_checked, root4Node45Step1Chunk1_5_checked, root4Node45Step1Chunk2_0_checked, root4Node45Step1Chunk2_1_checked, root4Node45Step1Chunk2_2_checked, root4Node45Step1Chunk2_3_checked, root4Node45Step1Chunk2_4_checked, root4Node45Step1Chunk2_5_checked, root4Node45Step1Chunk3_0_checked, root4Node45Step1Chunk3_1_checked, root4Node45Step1Chunk3_2_checked, root4Node45Step1Chunk3_3_checked, root4Node45Step1Chunk3_4_checked, root4Node45Step1Chunk3_5_checked, root4Node45Step1Chunk4_0_checked, root4Node45Step1Chunk4_1_checked, root4Node45Step1Chunk4_2_checked, root4Node45Step1Chunk4_3_checked, root4Node45Step1Chunk4_4_checked, root4Node45Step1Chunk4_5_checked, root4Node45Step1Chunk5_0_checked, root4Node45Step1Chunk5_1_checked, root4Node45Step1Chunk5_2_checked, root4Node45Step1Chunk5_3_checked, root4Node45Step1Chunk5_4_checked, root4Node45Step1Chunk5_5_checked, root4Node45Step1Chunk6_0_checked, root4Node45Step1Chunk6_1_checked, root4Node45Step1Chunk6_2_checked, root4Node45Step1Chunk6_3_checked, root4Node45Step1Chunk6_4_checked, root4Node45Step1Chunk6_5_checked, root4Node45Step1Chunk7_0_checked, root4Node45Step1Chunk7_1_checked, root4Node45Step1Chunk7_2_checked, root4Node45Step1Chunk7_3_checked, root4Node45Step1Chunk7_4_checked, root4Node45Step1Chunk7_5_checked, root4Node45Step1Chunk8_0_checked, root4Node45Step1Chunk8_1_checked, root4Node45Step1Chunk8_2_checked, root4Node45Step1Chunk8_3_checked, root4Node45Step1Chunk8_4_checked, root4Node45Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node45Step1_checked :
    checkReplacement table57 root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq
    root4Node45Step1Narrowing_checked (by decide)
def root4Node45Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(8,4)]
  | 4 => [(0,0)]
  | 5 => [(7,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(1,5)]
  | 11 => [(6,1)]
  | 12 => [(8,1)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(5,1)]
  | 22 => [(0,1)]
  | 23 => [(6,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => [(7,2)]
  | 30 => [(8,3)]
  | 31 => [(5,5)]
  | 32 => [(1,0)]
  | 33 => [(2,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => [(8,1)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(0,0)]
  | 44 => [(3,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(8,0)]
  | 49 => [(8,3)]
  | 50 => [(5,5)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(1,4)]
  | 60 => [(0,5)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(7,0)]
  | 64 => [(8,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(6,0)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(8,2)]
  | 75 => [(8,0)]
  | 76 => [(7,3)]
  | 77 => [(8,2)]
  | 78 => [(6,1)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(5,4)]
  | 83 => [(6,4)]
  | 84 => [(1,2)]
  | 85 => [(8,3)]
  | 86 => [(8,5)]
  | 87 => [(7,0)]
  | 88 => [(4,3)]
  | 89 => [(7,5)]
  | _ => [(0,3)]
def root4Node45Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(7,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(8,1)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(5,1)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(1,0)]
  | 33 => some [(2,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(8,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(0,0)]
  | 44 => some [(3,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(8,0)]
  | 49 => some [(8,3)]
  | 50 => some [(5,5)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(1,4)]
  | 60 => some [(0,5)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(6,0)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(8,2)]
  | 78 => some [(6,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(8,3)]
  | 86 => some [(8,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(7,5)]
  | _ => some [(0,3)]
theorem root4Node45Domains2_fast_eq : root4Node45Domains2 = expandDomains root4Node45Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node45Domains2 v = expandDomains root4Node45Domains2Fast v from by decide) v
theorem root4Node45Step2Chunk0_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_0⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk0_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_1⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk0_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_2⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk0_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_3⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk0_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_4⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk0_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_5⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk1_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_0⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk1_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_1⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk1_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_2⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk1_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_3⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk1_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_4⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk1_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_5⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk2_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_0⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk2_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_1⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk2_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_2⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk2_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_3⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk2_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_4⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk2_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_5⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk3_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_0⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk3_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_1⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk3_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_2⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk3_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_3⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk3_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_4⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk3_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_5⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk4_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_0⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk4_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_1⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk4_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_2⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk4_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_3⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk4_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_4⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk4_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_5⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk5_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_0⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk5_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_1⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk5_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_2⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk5_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_3⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk5_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_4⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk5_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_5⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk6_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_0⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk6_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_1⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk6_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_2⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk6_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_3⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk6_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_4⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk6_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_5⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk7_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_0⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk7_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_1⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk7_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_2⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk7_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_3⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk7_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_4⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk7_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_5⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk8_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_0⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk8_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_1⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk8_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_2⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk8_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_3⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk8_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_4⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk8_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_5⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Narrowing_checked :
    checkNarrowing table55 root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_flatten table55Scope [table55Rows0_0,table55Rows0_1,table55Rows0_2,table55Rows0_3,table55Rows0_4,table55Rows0_5,table55Rows1_0,table55Rows1_1,table55Rows1_2,table55Rows1_3,table55Rows1_4,table55Rows1_5,table55Rows2_0,table55Rows2_1,table55Rows2_2,table55Rows2_3,table55Rows2_4,table55Rows2_5,table55Rows3_0,table55Rows3_1,table55Rows3_2,table55Rows3_3,table55Rows3_4,table55Rows3_5,table55Rows4_0,table55Rows4_1,table55Rows4_2,table55Rows4_3,table55Rows4_4,table55Rows4_5,table55Rows5_0,table55Rows5_1,table55Rows5_2,table55Rows5_3,table55Rows5_4,table55Rows5_5,table55Rows6_0,table55Rows6_1,table55Rows6_2,table55Rows6_3,table55Rows6_4,table55Rows6_5,table55Rows7_0,table55Rows7_1,table55Rows7_2,table55Rows7_3,table55Rows7_4,table55Rows7_5,table55Rows8_0,table55Rows8_1,table55Rows8_2,table55Rows8_3,table55Rows8_4,table55Rows8_5]
    root4Node45Domains1 root4Node45Domains2 (by
      simp only [List.all_cons, List.all_nil, root4Node45Step2Chunk0_0_checked, root4Node45Step2Chunk0_1_checked, root4Node45Step2Chunk0_2_checked, root4Node45Step2Chunk0_3_checked, root4Node45Step2Chunk0_4_checked, root4Node45Step2Chunk0_5_checked, root4Node45Step2Chunk1_0_checked, root4Node45Step2Chunk1_1_checked, root4Node45Step2Chunk1_2_checked, root4Node45Step2Chunk1_3_checked, root4Node45Step2Chunk1_4_checked, root4Node45Step2Chunk1_5_checked, root4Node45Step2Chunk2_0_checked, root4Node45Step2Chunk2_1_checked, root4Node45Step2Chunk2_2_checked, root4Node45Step2Chunk2_3_checked, root4Node45Step2Chunk2_4_checked, root4Node45Step2Chunk2_5_checked, root4Node45Step2Chunk3_0_checked, root4Node45Step2Chunk3_1_checked, root4Node45Step2Chunk3_2_checked, root4Node45Step2Chunk3_3_checked, root4Node45Step2Chunk3_4_checked, root4Node45Step2Chunk3_5_checked, root4Node45Step2Chunk4_0_checked, root4Node45Step2Chunk4_1_checked, root4Node45Step2Chunk4_2_checked, root4Node45Step2Chunk4_3_checked, root4Node45Step2Chunk4_4_checked, root4Node45Step2Chunk4_5_checked, root4Node45Step2Chunk5_0_checked, root4Node45Step2Chunk5_1_checked, root4Node45Step2Chunk5_2_checked, root4Node45Step2Chunk5_3_checked, root4Node45Step2Chunk5_4_checked, root4Node45Step2Chunk5_5_checked, root4Node45Step2Chunk6_0_checked, root4Node45Step2Chunk6_1_checked, root4Node45Step2Chunk6_2_checked, root4Node45Step2Chunk6_3_checked, root4Node45Step2Chunk6_4_checked, root4Node45Step2Chunk6_5_checked, root4Node45Step2Chunk7_0_checked, root4Node45Step2Chunk7_1_checked, root4Node45Step2Chunk7_2_checked, root4Node45Step2Chunk7_3_checked, root4Node45Step2Chunk7_4_checked, root4Node45Step2Chunk7_5_checked, root4Node45Step2Chunk8_0_checked, root4Node45Step2Chunk8_1_checked, root4Node45Step2Chunk8_2_checked, root4Node45Step2Chunk8_3_checked, root4Node45Step2Chunk8_4_checked, root4Node45Step2Chunk8_5_checked, Bool.true_and])
theorem root4Node45Step2_checked :
    checkReplacement table55 root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq
    root4Node45Step2Narrowing_checked (by decide)
theorem root4Node45Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node45Domains2 (.output 22) = true := by decide
def root4Node46Domains0 : Domains 91 State := restrict root4Node0Domains4 18 (8,0)
def root4Node46Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 1 => some [(0,0),(0,5),(6,2),(6,3),(6,4)]
  | 2 => some [(1,2),(4,4),(7,2),(8,4)]
  | 3 => some [(1,4),(7,4),(8,4)]
  | 4 => some [(0,0),(0,5),(1,3),(6,3)]
  | 5 => some [(4,4),(7,2),(8,2)]
  | 6 => some [(2,1),(2,3),(2,5),(4,3),(4,5),(7,1)]
  | 7 => some [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 8 => some [(0,3),(1,1),(6,1),(7,1)]
  | 9 => some [(4,1),(7,5),(8,1)]
  | 10 => some [(0,2),(1,5),(6,0),(6,5)]
  | 11 => some [(0,4),(1,1),(6,1),(7,1)]
  | 12 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 13 => some [(0,0),(1,4),(4,0),(6,4),(7,4)]
  | 14 => some [(0,5),(1,2),(1,3),(3,2),(6,3),(7,2),(7,3)]
  | 15 => some [(2,0),(2,2),(4,0),(4,2)]
  | 16 => some [(3,3),(5,3),(7,3)]
  | 17 => some [(5,2),(5,5),(8,2),(8,5)]
  | 18 => some [(8,0)]
  | 19 => some [(4,3),(7,3),(8,3)]
  | 20 => some [(1,5),(3,5),(4,2),(5,2),(5,5),(7,5),(8,2),(8,5)]
  | 21 => some [(1,5),(4,1),(5,1),(7,5),(8,1)]
  | 22 => some [(0,1),(0,2),(0,3),(6,0),(6,1),(6,5)]
  | 23 => some [(0,4),(1,1),(3,1),(5,1),(6,2)]
  | 24 => some [(0,1),(1,4),(3,4),(7,4)]
  | 25 => some [(0,5),(6,2),(6,3)]
  | 26 => some [(4,4),(7,2),(8,4)]
  | 27 => some [(1,4),(6,4),(7,4)]
  | 28 => some [(0,5),(1,2),(6,3)]
  | 29 => some [(2,0),(2,2),(2,4),(4,4),(7,2),(7,4),(8,4)]
  | 30 => some [(4,5),(7,3),(8,3),(8,5)]
  | 31 => some [(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 32 => some [(1,0),(3,0),(5,0),(5,3),(7,0),(8,3)]
  | 33 => some [(2,1),(2,3),(2,5),(4,5),(8,5)]
  | 34 => some [(0,2),(1,0),(6,0)]
  | 35 => some [(1,1),(7,1)]
  | 36 => some [(4,1),(7,5)]
  | 37 => some [(0,2),(0,3),(6,0)]
  | 38 => some [(1,1),(3,1),(7,1),(8,1)]
  | 39 => some [(0,1),(1,5),(4,1),(5,1),(6,5),(7,5),(8,1)]
  | 40 => some [(0,0),(0,1),(1,4),(6,3),(6,4)]
  | 41 => some [(0,5),(1,2),(6,2),(7,2)]
  | 42 => some [(4,4),(7,4),(8,4)]
  | 43 => some [(0,0),(6,3),(6,4)]
  | 44 => some [(1,2),(3,2),(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(5,2),(8,2)]
  | 48 => some [(5,0),(5,3),(8,0)]
  | 49 => some [(4,5),(7,3),(8,3),(8,5)]
  | 50 => some [(1,0),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 51 => some [(0,3),(1,0),(1,1),(6,0),(6,1)]
  | 52 => some [(4,1),(7,1),(8,1)]
  | 53 => some [(0,2),(1,5),(7,5)]
  | 54 => some [(0,3),(1,1),(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(1,4),(6,3),(6,4)]
  | 60 => some [(0,5),(1,2),(7,2)]
  | 61 => some [(1,3),(3,3),(5,0),(5,3),(7,3),(8,0)]
  | 62 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 63 => some [(4,2),(7,0),(8,0)]
  | 64 => some [(5,3),(8,3)]
  | 65 => some [(5,5),(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1),(7,1)]
  | 68 => some [(0,2),(1,5),(7,5)]
  | 69 => some [(0,3),(1,1),(6,0),(6,1)]
  | 70 => some [(0,0),(0,4),(0,5),(6,2),(6,3),(6,4)]
  | 71 => some [(1,2),(4,4),(5,4),(7,2),(8,4)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(1,3),(6,3)]
  | 74 => some [(4,4),(7,2),(8,2)]
  | 75 => some [(0,0),(4,0),(5,0),(8,0)]
  | 76 => some [(3,2),(4,5),(7,3)]
  | 77 => some [(4,0),(4,2),(7,0),(8,2)]
  | 78 => some [(0,3),(1,1),(4,3),(6,1),(7,1)]
  | 79 => some [(4,1),(7,5),(8,1)]
  | 80 => some [(0,2),(6,0),(6,5)]
  | 81 => some [(0,4),(1,1),(7,1)]
  | 82 => some [(1,5),(5,1),(5,4)]
  | 83 => some [(0,0),(0,1),(6,1),(6,4)]
  | 84 => some [(1,2),(5,1),(6,2),(7,2)]
  | 85 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 86 => some [(5,2),(5,5),(8,2),(8,5)]
  | 87 => some [(5,0),(7,0),(8,0)]
  | 88 => some [(4,3),(4,5),(8,3)]
  | 89 => some [(1,5),(3,5),(5,5),(7,0),(7,5)]
  | _ => some [(0,3),(1,0),(6,1),(8,3)]
theorem root4Node46Domains0_fast_eq : root4Node46Domains0 = expandDomains root4Node46Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node46Domains0 v = expandDomains root4Node46Domains0Fast v from by decide) v
def root4Node46Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 1 => [(0,0),(0,5),(6,2),(6,3),(6,4)]
  | 2 => [(1,2),(4,4),(7,2),(8,4)]
  | 3 => [(1,4),(7,4)]
  | 4 => [(0,5),(6,3)]
  | 5 => [(4,4),(7,2)]
  | 6 => [(2,1),(2,3),(2,5),(4,3),(4,5),(7,1)]
  | 7 => [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 8 => [(0,3),(1,1),(6,1),(7,1)]
  | 9 => [(4,1),(7,5)]
  | 10 => [(0,2),(6,0)]
  | 11 => [(1,1),(7,1)]
  | 12 => [(4,1),(5,1),(7,5),(8,1)]
  | 13 => [(0,0),(1,4),(4,0),(6,4),(7,4)]
  | 14 => [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 15 => [(2,0),(2,2),(4,0)]
  | 16 => [(3,3),(7,3)]
  | 17 => [(5,2),(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(4,2),(5,2),(5,5),(8,2)]
  | 21 => [(1,5),(4,1),(5,1),(7,5),(8,1)]
  | 22 => [(0,2),(0,3),(6,0),(6,1)]
  | 23 => [(1,1),(3,1),(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(1,4),(6,4)]
  | 28 => [(0,5),(1,2)]
  | 29 => [(4,4),(7,4),(8,4)]
  | 30 => [(4,5),(7,3),(8,3),(8,5)]
  | 31 => [(4,2),(5,2),(7,0),(8,2)]
  | 32 => [(5,0),(5,3),(8,3)]
  | 33 => [(4,5),(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3),(6,0)]
  | 38 => [(7,1),(8,1)]
  | 39 => [(1,5),(6,5),(7,5)]
  | 40 => [(0,0),(0,1),(1,4),(6,3),(6,4)]
  | 41 => [(0,5),(1,2),(6,2),(7,2)]
  | 42 => [(7,4),(8,4)]
  | 43 => [(0,0),(6,3)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2),(8,2)]
  | 48 => [(5,0),(5,3),(8,0)]
  | 49 => [(4,5),(7,3),(8,5)]
  | 50 => [(1,0),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 51 => [(0,3),(1,0),(1,1),(6,0),(6,1)]
  | 52 => [(4,1),(7,1),(8,1)]
  | 53 => [(0,2),(1,5)]
  | 54 => [(1,1),(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(7,4),(8,4)]
  | 59 => [(0,0),(6,3),(6,4)]
  | 60 => [(0,5),(1,2),(7,2)]
  | 61 => [(1,3),(3,3),(5,0),(5,3),(7,3),(8,0)]
  | 62 => [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 63 => [(7,0),(8,0)]
  | 64 => [(8,3)]
  | 65 => [(5,5),(8,5)]
  | 66 => [(1,0)]
  | 67 => [(2,1),(7,1)]
  | 68 => [(0,2),(1,5),(7,5)]
  | 69 => [(0,3),(1,1),(6,0),(6,1)]
  | 70 => [(0,0),(0,4),(0,5),(6,2),(6,3),(6,4)]
  | 71 => [(1,2),(4,4),(5,4),(7,2),(8,4)]
  | 72 => [(1,4),(7,4)]
  | 73 => [(0,5),(1,3),(6,3)]
  | 74 => [(4,4),(7,2),(8,2)]
  | 75 => [(0,0),(4,0),(5,0),(8,0)]
  | 76 => [(3,2),(4,5),(7,3)]
  | 77 => [(4,0),(4,2),(7,0),(8,2)]
  | 78 => [(0,3),(1,1),(4,3),(6,1),(7,1)]
  | 79 => [(4,1),(7,5),(8,1)]
  | 80 => [(0,2),(6,0),(6,5)]
  | 81 => [(0,4),(1,1),(7,1)]
  | 82 => [(1,5),(5,1),(5,4)]
  | 83 => [(0,0),(0,1),(6,1),(6,4)]
  | 84 => [(1,2),(5,1),(6,2),(7,2)]
  | 85 => [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 86 => [(5,2),(5,5),(8,2),(8,5)]
  | 87 => [(5,0),(7,0),(8,0)]
  | 88 => [(4,3),(4,5),(8,3)]
  | 89 => [(1,5),(3,5),(5,5),(7,0),(7,5)]
  | _ => [(0,3),(1,0),(6,1),(8,3)]
def root4Node46Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 1 => some [(0,0),(0,5),(6,2),(6,3),(6,4)]
  | 2 => some [(1,2),(4,4),(7,2),(8,4)]
  | 3 => some [(1,4),(7,4)]
  | 4 => some [(0,5),(6,3)]
  | 5 => some [(4,4),(7,2)]
  | 6 => some [(2,1),(2,3),(2,5),(4,3),(4,5),(7,1)]
  | 7 => some [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 8 => some [(0,3),(1,1),(6,1),(7,1)]
  | 9 => some [(4,1),(7,5)]
  | 10 => some [(0,2),(6,0)]
  | 11 => some [(1,1),(7,1)]
  | 12 => some [(4,1),(5,1),(7,5),(8,1)]
  | 13 => some [(0,0),(1,4),(4,0),(6,4),(7,4)]
  | 14 => some [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 15 => some [(2,0),(2,2),(4,0)]
  | 16 => some [(3,3),(7,3)]
  | 17 => some [(5,2),(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(4,2),(5,2),(5,5),(8,2)]
  | 21 => some [(1,5),(4,1),(5,1),(7,5),(8,1)]
  | 22 => some [(0,2),(0,3),(6,0),(6,1)]
  | 23 => some [(1,1),(3,1),(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(4,4),(7,4),(8,4)]
  | 30 => some [(4,5),(7,3),(8,3),(8,5)]
  | 31 => some [(4,2),(5,2),(7,0),(8,2)]
  | 32 => some [(5,0),(5,3),(8,3)]
  | 33 => some [(4,5),(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(7,1),(8,1)]
  | 39 => some [(1,5),(6,5),(7,5)]
  | 40 => some [(0,0),(0,1),(1,4),(6,3),(6,4)]
  | 41 => some [(0,5),(1,2),(6,2),(7,2)]
  | 42 => some [(7,4),(8,4)]
  | 43 => some [(0,0),(6,3)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3),(8,0)]
  | 49 => some [(4,5),(7,3),(8,5)]
  | 50 => some [(1,0),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 51 => some [(0,3),(1,0),(1,1),(6,0),(6,1)]
  | 52 => some [(4,1),(7,1),(8,1)]
  | 53 => some [(0,2),(1,5)]
  | 54 => some [(1,1),(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(6,3),(6,4)]
  | 60 => some [(0,5),(1,2),(7,2)]
  | 61 => some [(1,3),(3,3),(5,0),(5,3),(7,3),(8,0)]
  | 62 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 63 => some [(7,0),(8,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5),(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1),(7,1)]
  | 68 => some [(0,2),(1,5),(7,5)]
  | 69 => some [(0,3),(1,1),(6,0),(6,1)]
  | 70 => some [(0,0),(0,4),(0,5),(6,2),(6,3),(6,4)]
  | 71 => some [(1,2),(4,4),(5,4),(7,2),(8,4)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(1,3),(6,3)]
  | 74 => some [(4,4),(7,2),(8,2)]
  | 75 => some [(0,0),(4,0),(5,0),(8,0)]
  | 76 => some [(3,2),(4,5),(7,3)]
  | 77 => some [(4,0),(4,2),(7,0),(8,2)]
  | 78 => some [(0,3),(1,1),(4,3),(6,1),(7,1)]
  | 79 => some [(4,1),(7,5),(8,1)]
  | 80 => some [(0,2),(6,0),(6,5)]
  | 81 => some [(0,4),(1,1),(7,1)]
  | 82 => some [(1,5),(5,1),(5,4)]
  | 83 => some [(0,0),(0,1),(6,1),(6,4)]
  | 84 => some [(1,2),(5,1),(6,2),(7,2)]
  | 85 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 86 => some [(5,2),(5,5),(8,2),(8,5)]
  | 87 => some [(5,0),(7,0),(8,0)]
  | 88 => some [(4,3),(4,5),(8,3)]
  | 89 => some [(1,5),(3,5),(5,5),(7,0),(7,5)]
  | _ => some [(0,3),(1,0),(6,1),(8,3)]
theorem root4Node46Domains1_fast_eq : root4Node46Domains1 = expandDomains root4Node46Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node46Domains1 v = expandDomains root4Node46Domains1Fast v from by decide) v
theorem root4Node46Step1Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Narrowing_checked :
    checkNarrowing table35 root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_flatten table35Scope [table35Rows0_0,table35Rows0_1,table35Rows0_2,table35Rows0_3,table35Rows0_4,table35Rows0_5,table35Rows1_0,table35Rows1_1,table35Rows1_2,table35Rows1_3,table35Rows1_4,table35Rows1_5,table35Rows2_0,table35Rows2_1,table35Rows2_2,table35Rows2_3,table35Rows2_4,table35Rows2_5,table35Rows3_0,table35Rows3_1,table35Rows3_2,table35Rows3_3,table35Rows3_4,table35Rows3_5,table35Rows4_0,table35Rows4_1,table35Rows4_2,table35Rows4_3,table35Rows4_4,table35Rows4_5,table35Rows5_0,table35Rows5_1,table35Rows5_2,table35Rows5_3,table35Rows5_4,table35Rows5_5,table35Rows6_0,table35Rows6_1,table35Rows6_2,table35Rows6_3,table35Rows6_4,table35Rows6_5,table35Rows7_0,table35Rows7_1,table35Rows7_2,table35Rows7_3,table35Rows7_4,table35Rows7_5,table35Rows8_0,table35Rows8_1,table35Rows8_2,table35Rows8_3,table35Rows8_4,table35Rows8_5]
    root4Node46Domains0 root4Node46Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node46Step1Chunk0_0_checked, root4Node46Step1Chunk0_1_checked, root4Node46Step1Chunk0_2_checked, root4Node46Step1Chunk0_3_checked, root4Node46Step1Chunk0_4_checked, root4Node46Step1Chunk0_5_checked, root4Node46Step1Chunk1_0_checked, root4Node46Step1Chunk1_1_checked, root4Node46Step1Chunk1_2_checked, root4Node46Step1Chunk1_3_checked, root4Node46Step1Chunk1_4_checked, root4Node46Step1Chunk1_5_checked, root4Node46Step1Chunk2_0_checked, root4Node46Step1Chunk2_1_checked, root4Node46Step1Chunk2_2_checked, root4Node46Step1Chunk2_3_checked, root4Node46Step1Chunk2_4_checked, root4Node46Step1Chunk2_5_checked, root4Node46Step1Chunk3_0_checked, root4Node46Step1Chunk3_1_checked, root4Node46Step1Chunk3_2_checked, root4Node46Step1Chunk3_3_checked, root4Node46Step1Chunk3_4_checked, root4Node46Step1Chunk3_5_checked, root4Node46Step1Chunk4_0_checked, root4Node46Step1Chunk4_1_checked, root4Node46Step1Chunk4_2_checked, root4Node46Step1Chunk4_3_checked, root4Node46Step1Chunk4_4_checked, root4Node46Step1Chunk4_5_checked, root4Node46Step1Chunk5_0_checked, root4Node46Step1Chunk5_1_checked, root4Node46Step1Chunk5_2_checked, root4Node46Step1Chunk5_3_checked, root4Node46Step1Chunk5_4_checked, root4Node46Step1Chunk5_5_checked, root4Node46Step1Chunk6_0_checked, root4Node46Step1Chunk6_1_checked, root4Node46Step1Chunk6_2_checked, root4Node46Step1Chunk6_3_checked, root4Node46Step1Chunk6_4_checked, root4Node46Step1Chunk6_5_checked, root4Node46Step1Chunk7_0_checked, root4Node46Step1Chunk7_1_checked, root4Node46Step1Chunk7_2_checked, root4Node46Step1Chunk7_3_checked, root4Node46Step1Chunk7_4_checked, root4Node46Step1Chunk7_5_checked, root4Node46Step1Chunk8_0_checked, root4Node46Step1Chunk8_1_checked, root4Node46Step1Chunk8_2_checked, root4Node46Step1Chunk8_3_checked, root4Node46Step1Chunk8_4_checked, root4Node46Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node46Step1_checked :
    checkReplacement table35 root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq
    root4Node46Step1Narrowing_checked (by decide)
def root4Node46Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 1 => [(0,0),(0,5),(6,2),(6,3),(6,4)]
  | 2 => [(1,2),(4,4),(7,2),(8,4)]
  | 3 => [(1,4),(7,4)]
  | 4 => [(0,5),(6,3)]
  | 5 => [(4,4),(7,2)]
  | 6 => [(2,1),(2,3),(2,5),(4,3),(4,5),(7,1)]
  | 7 => [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 8 => [(0,3),(1,1),(6,1),(7,1)]
  | 9 => [(4,1),(7,5)]
  | 10 => [(0,2),(6,0)]
  | 11 => [(1,1),(7,1)]
  | 12 => [(4,1),(5,1),(7,5),(8,1)]
  | 13 => [(0,0),(1,4),(6,4),(7,4)]
  | 14 => [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 15 => [(2,0),(2,2),(4,0)]
  | 16 => [(3,3),(7,3)]
  | 17 => [(5,2),(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(4,2),(5,2),(5,5),(8,2)]
  | 21 => [(1,5),(4,1),(7,5)]
  | 22 => [(0,2),(0,3),(6,0),(6,1)]
  | 23 => [(1,1),(3,1),(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(1,4),(6,4)]
  | 28 => [(0,5),(1,2)]
  | 29 => [(4,4),(7,4),(8,4)]
  | 30 => [(4,5),(7,3),(8,5)]
  | 31 => [(4,2),(5,2),(7,0),(8,2)]
  | 32 => [(5,0),(5,3),(8,3)]
  | 33 => [(4,5),(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3),(6,0)]
  | 38 => [(7,1),(8,1)]
  | 39 => [(1,5),(6,5),(7,5)]
  | 40 => [(0,0),(0,1),(6,3),(6,4)]
  | 41 => [(1,2),(6,2),(7,2)]
  | 42 => [(7,4),(8,4)]
  | 43 => [(0,0),(6,3)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2),(8,2)]
  | 48 => [(5,0),(5,3),(8,0)]
  | 49 => [(4,5),(7,3),(8,5)]
  | 50 => [(1,0),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 51 => [(0,3),(1,0),(1,1),(6,1)]
  | 52 => [(4,1),(7,1),(8,1)]
  | 53 => [(0,2),(1,5)]
  | 54 => [(1,1),(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(7,4),(8,4)]
  | 59 => [(0,0),(6,3),(6,4)]
  | 60 => [(0,5),(1,2),(7,2)]
  | 61 => [(1,3),(3,3),(5,0),(5,3),(7,3)]
  | 62 => [(4,5),(5,2),(5,5),(8,5)]
  | 63 => [(7,0),(8,0)]
  | 64 => [(8,3)]
  | 65 => [(5,5),(8,5)]
  | 66 => [(1,0)]
  | 67 => [(2,1),(7,1)]
  | 68 => [(0,2),(1,5),(7,5)]
  | 69 => [(0,3),(1,1),(6,0),(6,1)]
  | 70 => [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 71 => [(4,4),(5,4),(7,2),(8,4)]
  | 72 => [(1,4),(7,4)]
  | 73 => [(0,5),(1,3),(6,3)]
  | 74 => [(4,4),(7,2),(8,2)]
  | 75 => [(0,0),(4,0),(5,0),(8,0)]
  | 76 => [(3,2),(4,5),(7,3)]
  | 77 => [(4,0),(4,2),(7,0),(8,2)]
  | 78 => [(1,1),(4,3),(6,1),(7,1)]
  | 79 => [(4,1),(7,5),(8,1)]
  | 80 => [(0,2),(6,0),(6,5)]
  | 81 => [(0,4),(1,1),(7,1)]
  | 82 => [(1,5),(5,1),(5,4)]
  | 83 => [(0,0),(0,1),(6,1),(6,4)]
  | 84 => [(1,2),(5,1),(6,2),(7,2)]
  | 85 => [(1,3),(7,3),(8,3)]
  | 86 => [(5,2),(5,5),(8,2)]
  | 87 => [(5,0),(7,0),(8,0)]
  | 88 => [(4,3),(4,5),(8,3)]
  | 89 => [(1,5),(3,5),(5,5),(7,0),(7,5)]
  | _ => [(0,3),(1,0),(6,1),(8,3)]
def root4Node46Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 1 => some [(0,0),(0,5),(6,2),(6,3),(6,4)]
  | 2 => some [(1,2),(4,4),(7,2),(8,4)]
  | 3 => some [(1,4),(7,4)]
  | 4 => some [(0,5),(6,3)]
  | 5 => some [(4,4),(7,2)]
  | 6 => some [(2,1),(2,3),(2,5),(4,3),(4,5),(7,1)]
  | 7 => some [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 8 => some [(0,3),(1,1),(6,1),(7,1)]
  | 9 => some [(4,1),(7,5)]
  | 10 => some [(0,2),(6,0)]
  | 11 => some [(1,1),(7,1)]
  | 12 => some [(4,1),(5,1),(7,5),(8,1)]
  | 13 => some [(0,0),(1,4),(6,4),(7,4)]
  | 14 => some [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 15 => some [(2,0),(2,2),(4,0)]
  | 16 => some [(3,3),(7,3)]
  | 17 => some [(5,2),(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(4,2),(5,2),(5,5),(8,2)]
  | 21 => some [(1,5),(4,1),(7,5)]
  | 22 => some [(0,2),(0,3),(6,0),(6,1)]
  | 23 => some [(1,1),(3,1),(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(4,4),(7,4),(8,4)]
  | 30 => some [(4,5),(7,3),(8,5)]
  | 31 => some [(4,2),(5,2),(7,0),(8,2)]
  | 32 => some [(5,0),(5,3),(8,3)]
  | 33 => some [(4,5),(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(7,1),(8,1)]
  | 39 => some [(1,5),(6,5),(7,5)]
  | 40 => some [(0,0),(0,1),(6,3),(6,4)]
  | 41 => some [(1,2),(6,2),(7,2)]
  | 42 => some [(7,4),(8,4)]
  | 43 => some [(0,0),(6,3)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3),(8,0)]
  | 49 => some [(4,5),(7,3),(8,5)]
  | 50 => some [(1,0),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 51 => some [(0,3),(1,0),(1,1),(6,1)]
  | 52 => some [(4,1),(7,1),(8,1)]
  | 53 => some [(0,2),(1,5)]
  | 54 => some [(1,1),(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(6,3),(6,4)]
  | 60 => some [(0,5),(1,2),(7,2)]
  | 61 => some [(1,3),(3,3),(5,0),(5,3),(7,3)]
  | 62 => some [(4,5),(5,2),(5,5),(8,5)]
  | 63 => some [(7,0),(8,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5),(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1),(7,1)]
  | 68 => some [(0,2),(1,5),(7,5)]
  | 69 => some [(0,3),(1,1),(6,0),(6,1)]
  | 70 => some [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 71 => some [(4,4),(5,4),(7,2),(8,4)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(1,3),(6,3)]
  | 74 => some [(4,4),(7,2),(8,2)]
  | 75 => some [(0,0),(4,0),(5,0),(8,0)]
  | 76 => some [(3,2),(4,5),(7,3)]
  | 77 => some [(4,0),(4,2),(7,0),(8,2)]
  | 78 => some [(1,1),(4,3),(6,1),(7,1)]
  | 79 => some [(4,1),(7,5),(8,1)]
  | 80 => some [(0,2),(6,0),(6,5)]
  | 81 => some [(0,4),(1,1),(7,1)]
  | 82 => some [(1,5),(5,1),(5,4)]
  | 83 => some [(0,0),(0,1),(6,1),(6,4)]
  | 84 => some [(1,2),(5,1),(6,2),(7,2)]
  | 85 => some [(1,3),(7,3),(8,3)]
  | 86 => some [(5,2),(5,5),(8,2)]
  | 87 => some [(5,0),(7,0),(8,0)]
  | 88 => some [(4,3),(4,5),(8,3)]
  | 89 => some [(1,5),(3,5),(5,5),(7,0),(7,5)]
  | _ => some [(0,3),(1,0),(6,1),(8,3)]
theorem root4Node46Domains2_fast_eq : root4Node46Domains2 = expandDomains root4Node46Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node46Domains2 v = expandDomains root4Node46Domains2Fast v from by decide) v
theorem root4Node46Step2Chunk0_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_0⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk0_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_1⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk0_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_2⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk0_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_3⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk0_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_4⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk0_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_5⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk1_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_0⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk1_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_1⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk1_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_2⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk1_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_3⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk1_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_4⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk1_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_5⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk2_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_0⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk2_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_1⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk2_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_2⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk2_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_3⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk2_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_4⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk2_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_5⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk3_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_0⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk3_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_1⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk3_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_2⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk3_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_3⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk3_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_4⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk3_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_5⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk4_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_0⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk4_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_1⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk4_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_2⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk4_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_3⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk4_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_4⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk4_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_5⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk5_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_0⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk5_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_1⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk5_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_2⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk5_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_3⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk5_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_4⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk5_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_5⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk6_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_0⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk6_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_1⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk6_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_2⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk6_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_3⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk6_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_4⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk6_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_5⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk7_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_0⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk7_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_1⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk7_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_2⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk7_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_3⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk7_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_4⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk7_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_5⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk8_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_0⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk8_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_1⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk8_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_2⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk8_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_3⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk8_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_4⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Chunk8_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_5⟩
      root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq (by decide)
theorem root4Node46Step2Narrowing_checked :
    checkNarrowing table52 root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkNarrowing_flatten table52Scope [table52Rows0_0,table52Rows0_1,table52Rows0_2,table52Rows0_3,table52Rows0_4,table52Rows0_5,table52Rows1_0,table52Rows1_1,table52Rows1_2,table52Rows1_3,table52Rows1_4,table52Rows1_5,table52Rows2_0,table52Rows2_1,table52Rows2_2,table52Rows2_3,table52Rows2_4,table52Rows2_5,table52Rows3_0,table52Rows3_1,table52Rows3_2,table52Rows3_3,table52Rows3_4,table52Rows3_5,table52Rows4_0,table52Rows4_1,table52Rows4_2,table52Rows4_3,table52Rows4_4,table52Rows4_5,table52Rows5_0,table52Rows5_1,table52Rows5_2,table52Rows5_3,table52Rows5_4,table52Rows5_5,table52Rows6_0,table52Rows6_1,table52Rows6_2,table52Rows6_3,table52Rows6_4,table52Rows6_5,table52Rows7_0,table52Rows7_1,table52Rows7_2,table52Rows7_3,table52Rows7_4,table52Rows7_5,table52Rows8_0,table52Rows8_1,table52Rows8_2,table52Rows8_3,table52Rows8_4,table52Rows8_5]
    root4Node46Domains1 root4Node46Domains2 (by
      simp only [List.all_cons, List.all_nil, root4Node46Step2Chunk0_0_checked, root4Node46Step2Chunk0_1_checked, root4Node46Step2Chunk0_2_checked, root4Node46Step2Chunk0_3_checked, root4Node46Step2Chunk0_4_checked, root4Node46Step2Chunk0_5_checked, root4Node46Step2Chunk1_0_checked, root4Node46Step2Chunk1_1_checked, root4Node46Step2Chunk1_2_checked, root4Node46Step2Chunk1_3_checked, root4Node46Step2Chunk1_4_checked, root4Node46Step2Chunk1_5_checked, root4Node46Step2Chunk2_0_checked, root4Node46Step2Chunk2_1_checked, root4Node46Step2Chunk2_2_checked, root4Node46Step2Chunk2_3_checked, root4Node46Step2Chunk2_4_checked, root4Node46Step2Chunk2_5_checked, root4Node46Step2Chunk3_0_checked, root4Node46Step2Chunk3_1_checked, root4Node46Step2Chunk3_2_checked, root4Node46Step2Chunk3_3_checked, root4Node46Step2Chunk3_4_checked, root4Node46Step2Chunk3_5_checked, root4Node46Step2Chunk4_0_checked, root4Node46Step2Chunk4_1_checked, root4Node46Step2Chunk4_2_checked, root4Node46Step2Chunk4_3_checked, root4Node46Step2Chunk4_4_checked, root4Node46Step2Chunk4_5_checked, root4Node46Step2Chunk5_0_checked, root4Node46Step2Chunk5_1_checked, root4Node46Step2Chunk5_2_checked, root4Node46Step2Chunk5_3_checked, root4Node46Step2Chunk5_4_checked, root4Node46Step2Chunk5_5_checked, root4Node46Step2Chunk6_0_checked, root4Node46Step2Chunk6_1_checked, root4Node46Step2Chunk6_2_checked, root4Node46Step2Chunk6_3_checked, root4Node46Step2Chunk6_4_checked, root4Node46Step2Chunk6_5_checked, root4Node46Step2Chunk7_0_checked, root4Node46Step2Chunk7_1_checked, root4Node46Step2Chunk7_2_checked, root4Node46Step2Chunk7_3_checked, root4Node46Step2Chunk7_4_checked, root4Node46Step2Chunk7_5_checked, root4Node46Step2Chunk8_0_checked, root4Node46Step2Chunk8_1_checked, root4Node46Step2Chunk8_2_checked, root4Node46Step2Chunk8_3_checked, root4Node46Step2Chunk8_4_checked, root4Node46Step2Chunk8_5_checked, Bool.true_and])
theorem root4Node46Step2_checked :
    checkReplacement table52 root4Node46Domains1 root4Node46Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root4Node46Domains1 root4Node46Domains2
    root4Node46Domains1Fast root4Node46Domains2Fast
    root4Node46Domains1_fast_eq root4Node46Domains2_fast_eq
    root4Node46Step2Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
