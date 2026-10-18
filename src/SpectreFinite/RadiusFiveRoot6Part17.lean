module

public import SpectreFinite.RadiusFiveRoot6Part16
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable19
public import SpectreFinite.RadiusFiveTable35
public import SpectreFinite.RadiusFiveTable6
public import SpectreFinite.RadiusFiveTable65

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node39Domains0 : Domains 91 State := restrict root6Node38Domains2 5 (1,5)
def root6Node39Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(1,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3),(6,3)]
  | 9 => some [(7,2),(8,2)]
  | 10 => some [(4,0),(5,0),(8,0)]
  | 11 => some [(4,5),(7,3)]
  | 12 => some [(4,2),(7,0)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1),(8,1)]
  | 15 => some [(0,2),(6,5)]
  | 16 => some [(0,4),(1,1)]
  | 17 => some [(5,1),(5,4)]
  | 18 => some [(0,0),(0,1),(6,4)]
  | 19 => some [(1,2),(6,2),(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(2,2),(2,4),(4,2)]
  | 22 => some [(1,3),(3,3),(5,3)]
  | 23 => some [(5,2),(5,5)]
  | 24 => some [(7,0),(8,0)]
  | 25 => some [(4,3),(8,3)]
  | 26 => some [(1,5),(3,5),(5,5)]
  | 27 => some [(0,3),(1,0),(6,1)]
  | 28 => some [(2,1),(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(0,4),(1,1),(7,1)]
  | 31 => some [(0,1),(1,4),(6,5)]
  | 32 => some [(0,4),(0,5),(6,2)]
  | 33 => some [(4,4),(5,4),(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0),(2,4),(4,4)]
  | 37 => some [(0,0),(1,3),(7,3)]
  | 38 => some [(3,2),(5,2)]
  | 39 => some [(4,0),(8,0)]
  | 40 => some [(3,0),(5,0)]
  | 41 => some [(2,5),(4,5)]
  | 42 => some [(1,0),(6,0),(7,0)]
  | 43 => some [(4,3),(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1),(7,1)]
  | 47 => some [(0,1),(1,5),(6,5)]
  | 48 => some [(0,4),(6,1),(6,2)]
  | 49 => some [(5,1),(5,4),(8,4)]
  | 50 => some [(0,1),(1,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0),(7,4)]
  | 54 => some [(1,3),(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(1,0),(7,0)]
  | 59 => some [(4,3),(7,1),(8,3)]
  | 60 => some [(7,5),(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1),(8,1)]
  | 63 => some [(0,1),(6,5)]
  | 64 => some [(0,4),(6,2)]
  | 65 => some [(5,4),(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(4,0),(7,4)]
  | 69 => some [(1,3),(6,3),(7,3)]
  | 70 => some [(8,3)]
  | 71 => some [(5,5),(8,5)]
  | 72 => some [(1,0),(7,0)]
  | 73 => some [(4,3),(7,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(4,1),(5,1),(8,1)]
  | 77 => some [(0,1),(0,2),(6,5)]
  | 78 => some [(0,5),(1,3)]
  | 79 => some [(4,4),(8,2)]
  | 80 => some [(1,4),(5,0)]
  | 81 => some [(0,5),(4,5)]
  | 82 => some [(2,0),(7,0)]
  | 83 => some [(7,3),(8,3)]
  | 84 => some [(5,2),(8,5)]
  | 85 => some [(0,4),(7,1)]
  | 86 => some [(5,4),(7,5)]
  | 87 => some [(0,0),(6,0)]
  | 88 => some [(3,1),(7,2)]
  | 89 => some [(0,1),(7,4)]
  | _ => some [(6,2),(6,3)]
theorem root6Node39Domains0_fast_eq : root6Node39Domains0 = expandDomains root6Node39Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node39Domains0 v = expandDomains root6Node39Domains0Fast v from by decide) v
def root6Node39Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,1)]
  | 5 => [(1,5)]
  | 6 => [(1,2)]
  | 7 => [(7,4)]
  | 8 => [(1,3)]
  | 9 => [(8,2)]
  | 10 => [(5,0)]
  | 11 => [(4,5)]
  | 12 => [(7,0)]
  | 13 => [(0,3)]
  | 14 => [(8,1)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(7,4)]
  | 21 => [(2,2),(2,4),(4,2)]
  | 22 => [(5,3)]
  | 23 => [(5,5)]
  | 24 => [(7,0)]
  | 25 => [(4,3)]
  | 26 => [(1,5)]
  | 27 => [(6,1)]
  | 28 => [(4,1)]
  | 29 => [(0,2)]
  | 30 => [(0,4),(1,1),(7,1)]
  | 31 => [(1,4)]
  | 32 => [(0,5)]
  | 33 => [(4,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,0)]
  | 37 => [(7,3)]
  | 38 => [(5,2)]
  | 39 => [(8,0)]
  | 40 => [(3,0),(5,0)]
  | 41 => [(2,5),(4,5)]
  | 42 => [(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(3,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(0,1),(1,4)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(1,0)]
  | 59 => [(7,1)]
  | 60 => [(7,5),(8,5)]
  | 61 => [(6,1)]
  | 62 => [(5,1),(8,1)]
  | 63 => [(0,1)]
  | 64 => [(6,2)]
  | 65 => [(8,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(4,0)]
  | 69 => [(1,3),(6,3),(7,3)]
  | 70 => [(8,3)]
  | 71 => [(5,5),(8,5)]
  | 72 => [(1,0)]
  | 73 => [(7,1)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(5,1)]
  | 77 => [(0,1),(0,2),(6,5)]
  | 78 => [(0,5),(1,3)]
  | 79 => [(4,4),(8,2)]
  | 80 => [(1,4),(5,0)]
  | 81 => [(0,5),(4,5)]
  | 82 => [(2,0),(7,0)]
  | 83 => [(7,3),(8,3)]
  | 84 => [(5,2),(8,5)]
  | 85 => [(0,4),(7,1)]
  | 86 => [(5,4),(7,5)]
  | 87 => [(0,0),(6,0)]
  | 88 => [(3,1),(7,2)]
  | 89 => [(0,1),(7,4)]
  | _ => [(6,2),(6,3)]
def root6Node39Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(1,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3)]
  | 9 => some [(8,2)]
  | 10 => some [(5,0)]
  | 11 => some [(4,5)]
  | 12 => some [(7,0)]
  | 13 => some [(0,3)]
  | 14 => some [(8,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(2,2),(2,4),(4,2)]
  | 22 => some [(5,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(4,3)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(0,4),(1,1),(7,1)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0)]
  | 37 => some [(7,3)]
  | 38 => some [(5,2)]
  | 39 => some [(8,0)]
  | 40 => some [(3,0),(5,0)]
  | 41 => some [(2,5),(4,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(0,1),(1,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(1,0)]
  | 59 => some [(7,1)]
  | 60 => some [(7,5),(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1),(8,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(4,0)]
  | 69 => some [(1,3),(6,3),(7,3)]
  | 70 => some [(8,3)]
  | 71 => some [(5,5),(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(5,1)]
  | 77 => some [(0,1),(0,2),(6,5)]
  | 78 => some [(0,5),(1,3)]
  | 79 => some [(4,4),(8,2)]
  | 80 => some [(1,4),(5,0)]
  | 81 => some [(0,5),(4,5)]
  | 82 => some [(2,0),(7,0)]
  | 83 => some [(7,3),(8,3)]
  | 84 => some [(5,2),(8,5)]
  | 85 => some [(0,4),(7,1)]
  | 86 => some [(5,4),(7,5)]
  | 87 => some [(0,0),(6,0)]
  | 88 => some [(3,1),(7,2)]
  | 89 => some [(0,1),(7,4)]
  | _ => some [(6,2),(6,3)]
theorem root6Node39Domains1_fast_eq : root6Node39Domains1 = expandDomains root6Node39Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node39Domains1 v = expandDomains root6Node39Domains1Fast v from by decide) v
theorem root6Node39Step1Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Narrowing_checked :
    checkNarrowing table35 root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_flatten table35Scope [table35Rows0_0,table35Rows0_1,table35Rows0_2,table35Rows0_3,table35Rows0_4,table35Rows0_5,table35Rows1_0,table35Rows1_1,table35Rows1_2,table35Rows1_3,table35Rows1_4,table35Rows1_5,table35Rows2_0,table35Rows2_1,table35Rows2_2,table35Rows2_3,table35Rows2_4,table35Rows2_5,table35Rows3_0,table35Rows3_1,table35Rows3_2,table35Rows3_3,table35Rows3_4,table35Rows3_5,table35Rows4_0,table35Rows4_1,table35Rows4_2,table35Rows4_3,table35Rows4_4,table35Rows4_5,table35Rows5_0,table35Rows5_1,table35Rows5_2,table35Rows5_3,table35Rows5_4,table35Rows5_5,table35Rows6_0,table35Rows6_1,table35Rows6_2,table35Rows6_3,table35Rows6_4,table35Rows6_5,table35Rows7_0,table35Rows7_1,table35Rows7_2,table35Rows7_3,table35Rows7_4,table35Rows7_5,table35Rows8_0,table35Rows8_1,table35Rows8_2,table35Rows8_3,table35Rows8_4,table35Rows8_5]
    root6Node39Domains0 root6Node39Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node39Step1Chunk0_0_checked, root6Node39Step1Chunk0_1_checked, root6Node39Step1Chunk0_2_checked, root6Node39Step1Chunk0_3_checked, root6Node39Step1Chunk0_4_checked, root6Node39Step1Chunk0_5_checked, root6Node39Step1Chunk1_0_checked, root6Node39Step1Chunk1_1_checked, root6Node39Step1Chunk1_2_checked, root6Node39Step1Chunk1_3_checked, root6Node39Step1Chunk1_4_checked, root6Node39Step1Chunk1_5_checked, root6Node39Step1Chunk2_0_checked, root6Node39Step1Chunk2_1_checked, root6Node39Step1Chunk2_2_checked, root6Node39Step1Chunk2_3_checked, root6Node39Step1Chunk2_4_checked, root6Node39Step1Chunk2_5_checked, root6Node39Step1Chunk3_0_checked, root6Node39Step1Chunk3_1_checked, root6Node39Step1Chunk3_2_checked, root6Node39Step1Chunk3_3_checked, root6Node39Step1Chunk3_4_checked, root6Node39Step1Chunk3_5_checked, root6Node39Step1Chunk4_0_checked, root6Node39Step1Chunk4_1_checked, root6Node39Step1Chunk4_2_checked, root6Node39Step1Chunk4_3_checked, root6Node39Step1Chunk4_4_checked, root6Node39Step1Chunk4_5_checked, root6Node39Step1Chunk5_0_checked, root6Node39Step1Chunk5_1_checked, root6Node39Step1Chunk5_2_checked, root6Node39Step1Chunk5_3_checked, root6Node39Step1Chunk5_4_checked, root6Node39Step1Chunk5_5_checked, root6Node39Step1Chunk6_0_checked, root6Node39Step1Chunk6_1_checked, root6Node39Step1Chunk6_2_checked, root6Node39Step1Chunk6_3_checked, root6Node39Step1Chunk6_4_checked, root6Node39Step1Chunk6_5_checked, root6Node39Step1Chunk7_0_checked, root6Node39Step1Chunk7_1_checked, root6Node39Step1Chunk7_2_checked, root6Node39Step1Chunk7_3_checked, root6Node39Step1Chunk7_4_checked, root6Node39Step1Chunk7_5_checked, root6Node39Step1Chunk8_0_checked, root6Node39Step1Chunk8_1_checked, root6Node39Step1Chunk8_2_checked, root6Node39Step1Chunk8_3_checked, root6Node39Step1Chunk8_4_checked, root6Node39Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node39Step1_checked :
    checkReplacement table35 root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq
    root6Node39Step1Narrowing_checked (by decide)
def root6Node39Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,1)]
  | 5 => [(1,5)]
  | 6 => [(1,2)]
  | 7 => [(7,4)]
  | 8 => [(1,3)]
  | 9 => [(8,2)]
  | 10 => [(5,0)]
  | 11 => [(4,5)]
  | 12 => [(7,0)]
  | 13 => [(0,3)]
  | 14 => [(8,1)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(7,4)]
  | 21 => [(2,2),(2,4),(4,2)]
  | 22 => [(5,3)]
  | 23 => [(5,5)]
  | 24 => [(7,0)]
  | 25 => [(4,3)]
  | 26 => [(1,5)]
  | 27 => [(6,1)]
  | 28 => [(4,1)]
  | 29 => [(0,2)]
  | 30 => [(0,4),(1,1),(7,1)]
  | 31 => [(1,4)]
  | 32 => [(0,5)]
  | 33 => [(4,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,0)]
  | 37 => [(7,3)]
  | 38 => [(5,2)]
  | 39 => [(8,0)]
  | 40 => [(3,0),(5,0)]
  | 41 => [(2,5),(4,5)]
  | 42 => [(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(3,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(0,1),(1,4)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(1,0)]
  | 59 => [(7,1)]
  | 60 => [(7,5),(8,5)]
  | 61 => [(6,1)]
  | 62 => [(5,1)]
  | 63 => [(0,1)]
  | 64 => [(6,2)]
  | 65 => [(8,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(4,0)]
  | 69 => [(7,3)]
  | 70 => [(8,3)]
  | 71 => [(8,5)]
  | 72 => [(1,0)]
  | 73 => [(7,1)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(5,1)]
  | 77 => [(0,1)]
  | 78 => [(1,3)]
  | 79 => [(8,2)]
  | 80 => [(5,0)]
  | 81 => [(4,5)]
  | 82 => [(7,0)]
  | 83 => [(8,3)]
  | 84 => [(8,5)]
  | 85 => [(0,4)]
  | 86 => [(5,4)]
  | 87 => [(0,0)]
  | 88 => [(7,2)]
  | 89 => [(7,4)]
  | _ => [(6,3)]
def root6Node39Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(1,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3)]
  | 9 => some [(8,2)]
  | 10 => some [(5,0)]
  | 11 => some [(4,5)]
  | 12 => some [(7,0)]
  | 13 => some [(0,3)]
  | 14 => some [(8,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(2,2),(2,4),(4,2)]
  | 22 => some [(5,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(4,3)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(0,4),(1,1),(7,1)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0)]
  | 37 => some [(7,3)]
  | 38 => some [(5,2)]
  | 39 => some [(8,0)]
  | 40 => some [(3,0),(5,0)]
  | 41 => some [(2,5),(4,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(0,1),(1,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(1,0)]
  | 59 => some [(7,1)]
  | 60 => some [(7,5),(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(4,0)]
  | 69 => some [(7,3)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(5,1)]
  | 77 => some [(0,1)]
  | 78 => some [(1,3)]
  | 79 => some [(8,2)]
  | 80 => some [(5,0)]
  | 81 => some [(4,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(8,5)]
  | 85 => some [(0,4)]
  | 86 => some [(5,4)]
  | 87 => some [(0,0)]
  | 88 => some [(7,2)]
  | 89 => some [(7,4)]
  | _ => some [(6,3)]
theorem root6Node39Domains2_fast_eq : root6Node39Domains2 = expandDomains root6Node39Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node39Domains2 v = expandDomains root6Node39Domains2Fast v from by decide) v
theorem root6Node39Step2Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Narrowing_checked :
    checkNarrowing table65 root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root6Node39Domains1 root6Node39Domains2 (by
      simp only [List.all_cons, List.all_nil, root6Node39Step2Chunk0_0_checked, root6Node39Step2Chunk0_1_checked, root6Node39Step2Chunk0_2_checked, root6Node39Step2Chunk0_3_checked, root6Node39Step2Chunk0_4_checked, root6Node39Step2Chunk0_5_checked, root6Node39Step2Chunk1_0_checked, root6Node39Step2Chunk1_1_checked, root6Node39Step2Chunk1_2_checked, root6Node39Step2Chunk1_3_checked, root6Node39Step2Chunk1_4_checked, root6Node39Step2Chunk1_5_checked, root6Node39Step2Chunk2_0_checked, root6Node39Step2Chunk2_1_checked, root6Node39Step2Chunk2_2_checked, root6Node39Step2Chunk2_3_checked, root6Node39Step2Chunk2_4_checked, root6Node39Step2Chunk2_5_checked, root6Node39Step2Chunk3_0_checked, root6Node39Step2Chunk3_1_checked, root6Node39Step2Chunk3_2_checked, root6Node39Step2Chunk3_3_checked, root6Node39Step2Chunk3_4_checked, root6Node39Step2Chunk3_5_checked, root6Node39Step2Chunk4_0_checked, root6Node39Step2Chunk4_1_checked, root6Node39Step2Chunk4_2_checked, root6Node39Step2Chunk4_3_checked, root6Node39Step2Chunk4_4_checked, root6Node39Step2Chunk4_5_checked, root6Node39Step2Chunk5_0_checked, root6Node39Step2Chunk5_1_checked, root6Node39Step2Chunk5_2_checked, root6Node39Step2Chunk5_3_checked, root6Node39Step2Chunk5_4_checked, root6Node39Step2Chunk5_5_checked, root6Node39Step2Chunk6_0_checked, root6Node39Step2Chunk6_1_checked, root6Node39Step2Chunk6_2_checked, root6Node39Step2Chunk6_3_checked, root6Node39Step2Chunk6_4_checked, root6Node39Step2Chunk6_5_checked, root6Node39Step2Chunk7_0_checked, root6Node39Step2Chunk7_1_checked, root6Node39Step2Chunk7_2_checked, root6Node39Step2Chunk7_3_checked, root6Node39Step2Chunk7_4_checked, root6Node39Step2Chunk7_5_checked, root6Node39Step2Chunk8_0_checked, root6Node39Step2Chunk8_1_checked, root6Node39Step2Chunk8_2_checked, root6Node39Step2Chunk8_3_checked, root6Node39Step2Chunk8_4_checked, root6Node39Step2Chunk8_5_checked, Bool.true_and])
theorem root6Node39Step2_checked :
    checkReplacement table65 root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq
    root6Node39Step2Narrowing_checked (by decide)
def root6Node39Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,1)]
  | 5 => [(1,5)]
  | 6 => [(1,2)]
  | 7 => [(7,4)]
  | 8 => [(1,3)]
  | 9 => [(8,2)]
  | 10 => [(5,0)]
  | 11 => [(4,5)]
  | 12 => [(7,0)]
  | 13 => [(0,3)]
  | 14 => [(8,1)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(7,4)]
  | 21 => [(4,2)]
  | 22 => [(5,3)]
  | 23 => [(5,5)]
  | 24 => [(7,0)]
  | 25 => [(4,3)]
  | 26 => [(1,5)]
  | 27 => [(6,1)]
  | 28 => [(4,1)]
  | 29 => [(0,2)]
  | 30 => [(0,4)]
  | 31 => [(1,4)]
  | 32 => [(0,5)]
  | 33 => [(4,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,0)]
  | 37 => [(7,3)]
  | 38 => [(5,2)]
  | 39 => [(8,0)]
  | 40 => [(3,0)]
  | 41 => [(2,5)]
  | 42 => [(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(3,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(0,1),(1,4)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(1,0)]
  | 59 => [(7,1)]
  | 60 => [(7,5),(8,5)]
  | 61 => [(6,1)]
  | 62 => [(5,1)]
  | 63 => [(0,1)]
  | 64 => [(6,2)]
  | 65 => [(8,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(4,0)]
  | 69 => [(7,3)]
  | 70 => [(8,3)]
  | 71 => [(8,5)]
  | 72 => [(1,0)]
  | 73 => [(7,1)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(5,1)]
  | 77 => [(0,1)]
  | 78 => [(1,3)]
  | 79 => [(8,2)]
  | 80 => [(5,0)]
  | 81 => [(4,5)]
  | 82 => [(7,0)]
  | 83 => [(8,3)]
  | 84 => [(8,5)]
  | 85 => [(0,4)]
  | 86 => [(5,4)]
  | 87 => [(0,0)]
  | 88 => [(7,2)]
  | 89 => [(7,4)]
  | _ => [(6,3)]
def root6Node39Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(1,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3)]
  | 9 => some [(8,2)]
  | 10 => some [(5,0)]
  | 11 => some [(4,5)]
  | 12 => some [(7,0)]
  | 13 => some [(0,3)]
  | 14 => some [(8,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(4,2)]
  | 22 => some [(5,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(4,3)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(0,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0)]
  | 37 => some [(7,3)]
  | 38 => some [(5,2)]
  | 39 => some [(8,0)]
  | 40 => some [(3,0)]
  | 41 => some [(2,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(0,1),(1,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(1,0)]
  | 59 => some [(7,1)]
  | 60 => some [(7,5),(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(4,0)]
  | 69 => some [(7,3)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(5,1)]
  | 77 => some [(0,1)]
  | 78 => some [(1,3)]
  | 79 => some [(8,2)]
  | 80 => some [(5,0)]
  | 81 => some [(4,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(8,5)]
  | 85 => some [(0,4)]
  | 86 => some [(5,4)]
  | 87 => some [(0,0)]
  | 88 => some [(7,2)]
  | 89 => some [(7,4)]
  | _ => some [(6,3)]
theorem root6Node39Domains3_fast_eq : root6Node39Domains3 = expandDomains root6Node39Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node39Domains3 v = expandDomains root6Node39Domains3Fast v from by decide) v
theorem root6Node39Step3Chunk0_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_0⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk0_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_1⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk0_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_2⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk0_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_3⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk0_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_4⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk0_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_5⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk1_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_0⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk1_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_1⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk1_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_2⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk1_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_3⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk1_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_4⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk1_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_5⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk2_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_0⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk2_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_1⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk2_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_2⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk2_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_3⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk2_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_4⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk2_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_5⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk3_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_0⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk3_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_1⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk3_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_2⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk3_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_3⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk3_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_4⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk3_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_5⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk4_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_0⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk4_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_1⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk4_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_2⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk4_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_3⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk4_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_4⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk4_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_5⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk5_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_0⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk5_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_1⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk5_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_2⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk5_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_3⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk5_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_4⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk5_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_5⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk6_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_0⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk6_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_1⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk6_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_2⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk6_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_3⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk6_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_4⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk6_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_5⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk7_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_0⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk7_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_1⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk7_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_2⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk7_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_3⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk7_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_4⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk7_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_5⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk8_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_0⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk8_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_1⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk8_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_2⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk8_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_3⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk8_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_4⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Chunk8_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_5⟩
      root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq (by decide)
theorem root6Node39Step3Narrowing_checked :
    checkNarrowing table6 root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkNarrowing_flatten table6Scope [table6Rows0_0,table6Rows0_1,table6Rows0_2,table6Rows0_3,table6Rows0_4,table6Rows0_5,table6Rows1_0,table6Rows1_1,table6Rows1_2,table6Rows1_3,table6Rows1_4,table6Rows1_5,table6Rows2_0,table6Rows2_1,table6Rows2_2,table6Rows2_3,table6Rows2_4,table6Rows2_5,table6Rows3_0,table6Rows3_1,table6Rows3_2,table6Rows3_3,table6Rows3_4,table6Rows3_5,table6Rows4_0,table6Rows4_1,table6Rows4_2,table6Rows4_3,table6Rows4_4,table6Rows4_5,table6Rows5_0,table6Rows5_1,table6Rows5_2,table6Rows5_3,table6Rows5_4,table6Rows5_5,table6Rows6_0,table6Rows6_1,table6Rows6_2,table6Rows6_3,table6Rows6_4,table6Rows6_5,table6Rows7_0,table6Rows7_1,table6Rows7_2,table6Rows7_3,table6Rows7_4,table6Rows7_5,table6Rows8_0,table6Rows8_1,table6Rows8_2,table6Rows8_3,table6Rows8_4,table6Rows8_5]
    root6Node39Domains2 root6Node39Domains3 (by
      simp only [List.all_cons, List.all_nil, root6Node39Step3Chunk0_0_checked, root6Node39Step3Chunk0_1_checked, root6Node39Step3Chunk0_2_checked, root6Node39Step3Chunk0_3_checked, root6Node39Step3Chunk0_4_checked, root6Node39Step3Chunk0_5_checked, root6Node39Step3Chunk1_0_checked, root6Node39Step3Chunk1_1_checked, root6Node39Step3Chunk1_2_checked, root6Node39Step3Chunk1_3_checked, root6Node39Step3Chunk1_4_checked, root6Node39Step3Chunk1_5_checked, root6Node39Step3Chunk2_0_checked, root6Node39Step3Chunk2_1_checked, root6Node39Step3Chunk2_2_checked, root6Node39Step3Chunk2_3_checked, root6Node39Step3Chunk2_4_checked, root6Node39Step3Chunk2_5_checked, root6Node39Step3Chunk3_0_checked, root6Node39Step3Chunk3_1_checked, root6Node39Step3Chunk3_2_checked, root6Node39Step3Chunk3_3_checked, root6Node39Step3Chunk3_4_checked, root6Node39Step3Chunk3_5_checked, root6Node39Step3Chunk4_0_checked, root6Node39Step3Chunk4_1_checked, root6Node39Step3Chunk4_2_checked, root6Node39Step3Chunk4_3_checked, root6Node39Step3Chunk4_4_checked, root6Node39Step3Chunk4_5_checked, root6Node39Step3Chunk5_0_checked, root6Node39Step3Chunk5_1_checked, root6Node39Step3Chunk5_2_checked, root6Node39Step3Chunk5_3_checked, root6Node39Step3Chunk5_4_checked, root6Node39Step3Chunk5_5_checked, root6Node39Step3Chunk6_0_checked, root6Node39Step3Chunk6_1_checked, root6Node39Step3Chunk6_2_checked, root6Node39Step3Chunk6_3_checked, root6Node39Step3Chunk6_4_checked, root6Node39Step3Chunk6_5_checked, root6Node39Step3Chunk7_0_checked, root6Node39Step3Chunk7_1_checked, root6Node39Step3Chunk7_2_checked, root6Node39Step3Chunk7_3_checked, root6Node39Step3Chunk7_4_checked, root6Node39Step3Chunk7_5_checked, root6Node39Step3Chunk8_0_checked, root6Node39Step3Chunk8_1_checked, root6Node39Step3Chunk8_2_checked, root6Node39Step3Chunk8_3_checked, root6Node39Step3Chunk8_4_checked, root6Node39Step3Chunk8_5_checked, Bool.true_and])
theorem root6Node39Step3_checked :
    checkReplacement table6 root6Node39Domains2 root6Node39Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root6Node39Domains2 root6Node39Domains3
    root6Node39Domains2Fast root6Node39Domains3Fast
    root6Node39Domains2_fast_eq root6Node39Domains3_fast_eq
    root6Node39Step3Narrowing_checked (by decide)
def root6Node39Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,1)]
  | 5 => [(1,5)]
  | 6 => [(1,2)]
  | 7 => [(7,4)]
  | 8 => [(1,3)]
  | 9 => [(8,2)]
  | 10 => [(5,0)]
  | 11 => [(4,5)]
  | 12 => [(7,0)]
  | 13 => [(0,3)]
  | 14 => [(8,1)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(7,4)]
  | 21 => [(4,2)]
  | 22 => [(5,3)]
  | 23 => [(5,5)]
  | 24 => [(7,0)]
  | 25 => [(4,3)]
  | 26 => [(1,5)]
  | 27 => [(6,1)]
  | 28 => [(4,1)]
  | 29 => [(0,2)]
  | 30 => [(0,4)]
  | 31 => [(1,4)]
  | 32 => [(0,5)]
  | 33 => [(4,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,0)]
  | 37 => [(7,3)]
  | 38 => [(5,2)]
  | 39 => [(8,0)]
  | 40 => [(3,0)]
  | 41 => [(2,5)]
  | 42 => [(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(3,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(1,4)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(1,0)]
  | 59 => [(7,1)]
  | 60 => [(7,5)]
  | 61 => [(6,1)]
  | 62 => [(5,1)]
  | 63 => [(0,1)]
  | 64 => [(6,2)]
  | 65 => [(8,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(4,0)]
  | 69 => [(7,3)]
  | 70 => [(8,3)]
  | 71 => [(8,5)]
  | 72 => [(1,0)]
  | 73 => [(7,1)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(5,1)]
  | 77 => [(0,1)]
  | 78 => [(1,3)]
  | 79 => [(8,2)]
  | 80 => [(5,0)]
  | 81 => [(4,5)]
  | 82 => [(7,0)]
  | 83 => [(8,3)]
  | 84 => [(8,5)]
  | 85 => [(0,4)]
  | 86 => [(5,4)]
  | 87 => [(0,0)]
  | 88 => [(7,2)]
  | 89 => [(7,4)]
  | _ => [(6,3)]
def root6Node39Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(1,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3)]
  | 9 => some [(8,2)]
  | 10 => some [(5,0)]
  | 11 => some [(4,5)]
  | 12 => some [(7,0)]
  | 13 => some [(0,3)]
  | 14 => some [(8,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(4,2)]
  | 22 => some [(5,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(4,3)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(0,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0)]
  | 37 => some [(7,3)]
  | 38 => some [(5,2)]
  | 39 => some [(8,0)]
  | 40 => some [(3,0)]
  | 41 => some [(2,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(1,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(1,0)]
  | 59 => some [(7,1)]
  | 60 => some [(7,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(4,0)]
  | 69 => some [(7,3)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(5,1)]
  | 77 => some [(0,1)]
  | 78 => some [(1,3)]
  | 79 => some [(8,2)]
  | 80 => some [(5,0)]
  | 81 => some [(4,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(8,5)]
  | 85 => some [(0,4)]
  | 86 => some [(5,4)]
  | 87 => some [(0,0)]
  | 88 => some [(7,2)]
  | 89 => some [(7,4)]
  | _ => some [(6,3)]
theorem root6Node39Domains4_fast_eq : root6Node39Domains4 = expandDomains root6Node39Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node39Domains4 v = expandDomains root6Node39Domains4Fast v from by decide) v
theorem root6Node39Step4Chunk0_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_0⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk0_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_1⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk0_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_2⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk0_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_3⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk0_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_4⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk0_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_5⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk1_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_0⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk1_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_1⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk1_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_2⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk1_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_3⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk1_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_4⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk1_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_5⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk2_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_0⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk2_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_1⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk2_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_2⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk2_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_3⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk2_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_4⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk2_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_5⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk3_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_0⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk3_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_1⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk3_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_2⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk3_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_3⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk3_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_4⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk3_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_5⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk4_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_0⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk4_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_1⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk4_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_2⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk4_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_3⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk4_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_4⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk4_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_5⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk5_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_0⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk5_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_1⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk5_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_2⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk5_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_3⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk5_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_4⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk5_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_5⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk6_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_0⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk6_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_1⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk6_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_2⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk6_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_3⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk6_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_4⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk6_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_5⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk7_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_0⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk7_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_1⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk7_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_2⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk7_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_3⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk7_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_4⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk7_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_5⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk8_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_0⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk8_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_1⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk8_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_2⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk8_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_3⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk8_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_4⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Chunk8_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_5⟩
      root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq (by decide)
theorem root6Node39Step4Narrowing_checked :
    checkNarrowing table19 root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkNarrowing_flatten table19Scope [table19Rows0_0,table19Rows0_1,table19Rows0_2,table19Rows0_3,table19Rows0_4,table19Rows0_5,table19Rows1_0,table19Rows1_1,table19Rows1_2,table19Rows1_3,table19Rows1_4,table19Rows1_5,table19Rows2_0,table19Rows2_1,table19Rows2_2,table19Rows2_3,table19Rows2_4,table19Rows2_5,table19Rows3_0,table19Rows3_1,table19Rows3_2,table19Rows3_3,table19Rows3_4,table19Rows3_5,table19Rows4_0,table19Rows4_1,table19Rows4_2,table19Rows4_3,table19Rows4_4,table19Rows4_5,table19Rows5_0,table19Rows5_1,table19Rows5_2,table19Rows5_3,table19Rows5_4,table19Rows5_5,table19Rows6_0,table19Rows6_1,table19Rows6_2,table19Rows6_3,table19Rows6_4,table19Rows6_5,table19Rows7_0,table19Rows7_1,table19Rows7_2,table19Rows7_3,table19Rows7_4,table19Rows7_5,table19Rows8_0,table19Rows8_1,table19Rows8_2,table19Rows8_3,table19Rows8_4,table19Rows8_5]
    root6Node39Domains3 root6Node39Domains4 (by
      simp only [List.all_cons, List.all_nil, root6Node39Step4Chunk0_0_checked, root6Node39Step4Chunk0_1_checked, root6Node39Step4Chunk0_2_checked, root6Node39Step4Chunk0_3_checked, root6Node39Step4Chunk0_4_checked, root6Node39Step4Chunk0_5_checked, root6Node39Step4Chunk1_0_checked, root6Node39Step4Chunk1_1_checked, root6Node39Step4Chunk1_2_checked, root6Node39Step4Chunk1_3_checked, root6Node39Step4Chunk1_4_checked, root6Node39Step4Chunk1_5_checked, root6Node39Step4Chunk2_0_checked, root6Node39Step4Chunk2_1_checked, root6Node39Step4Chunk2_2_checked, root6Node39Step4Chunk2_3_checked, root6Node39Step4Chunk2_4_checked, root6Node39Step4Chunk2_5_checked, root6Node39Step4Chunk3_0_checked, root6Node39Step4Chunk3_1_checked, root6Node39Step4Chunk3_2_checked, root6Node39Step4Chunk3_3_checked, root6Node39Step4Chunk3_4_checked, root6Node39Step4Chunk3_5_checked, root6Node39Step4Chunk4_0_checked, root6Node39Step4Chunk4_1_checked, root6Node39Step4Chunk4_2_checked, root6Node39Step4Chunk4_3_checked, root6Node39Step4Chunk4_4_checked, root6Node39Step4Chunk4_5_checked, root6Node39Step4Chunk5_0_checked, root6Node39Step4Chunk5_1_checked, root6Node39Step4Chunk5_2_checked, root6Node39Step4Chunk5_3_checked, root6Node39Step4Chunk5_4_checked, root6Node39Step4Chunk5_5_checked, root6Node39Step4Chunk6_0_checked, root6Node39Step4Chunk6_1_checked, root6Node39Step4Chunk6_2_checked, root6Node39Step4Chunk6_3_checked, root6Node39Step4Chunk6_4_checked, root6Node39Step4Chunk6_5_checked, root6Node39Step4Chunk7_0_checked, root6Node39Step4Chunk7_1_checked, root6Node39Step4Chunk7_2_checked, root6Node39Step4Chunk7_3_checked, root6Node39Step4Chunk7_4_checked, root6Node39Step4Chunk7_5_checked, root6Node39Step4Chunk8_0_checked, root6Node39Step4Chunk8_1_checked, root6Node39Step4Chunk8_2_checked, root6Node39Step4Chunk8_3_checked, root6Node39Step4Chunk8_4_checked, root6Node39Step4Chunk8_5_checked, Bool.true_and])
theorem root6Node39Step4_checked :
    checkReplacement table19 root6Node39Domains3 root6Node39Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root6Node39Domains3 root6Node39Domains4
    root6Node39Domains3Fast root6Node39Domains4Fast
    root6Node39Domains3_fast_eq root6Node39Domains4_fast_eq
    root6Node39Step4Narrowing_checked (by decide)
theorem root6Node39Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node39Domains4 (.output 18) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
