module

public import SpectreFinite.RadiusFiveRoot6Part18
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable19
public import SpectreFinite.RadiusFiveTable34
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable6

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node42Domains0 : Domains 91 State := restrict root6Node40Domains1 8 (6,3)
def root6Node42Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2),(8,2)]
  | 10 => some [(4,0),(8,0)]
  | 11 => some [(7,3)]
  | 12 => some [(4,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1),(8,1)]
  | 15 => some [(0,2),(6,5)]
  | 16 => some [(0,4),(1,1)]
  | 17 => some [(5,1),(5,4)]
  | 18 => some [(0,1),(6,4)]
  | 19 => some [(1,2),(6,2)]
  | 20 => some [(7,4)]
  | 21 => some [(2,2),(2,4),(4,2)]
  | 22 => some [(1,3),(3,3),(5,3)]
  | 23 => some [(5,2),(5,5)]
  | 24 => some [(7,0),(8,0)]
  | 25 => some [(4,3),(8,3)]
  | 26 => some [(3,5),(5,5)]
  | 27 => some [(0,3),(1,0)]
  | 28 => some [(2,1),(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(0,4),(1,1),(7,1)]
  | 31 => some [(0,1),(1,4),(6,5)]
  | 32 => some [(0,4),(0,5),(6,2)]
  | 33 => some [(4,4),(5,4),(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,4),(4,4)]
  | 37 => some [(0,0),(1,3)]
  | 38 => some [(3,2),(5,2)]
  | 39 => some [(4,0),(8,0)]
  | 40 => some [(3,0),(5,0)]
  | 41 => some [(2,5),(4,5)]
  | 42 => some [(1,0),(6,0),(7,0)]
  | 43 => some [(4,3),(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5),(6,5)]
  | 48 => some [(0,4),(6,1)]
  | 49 => some [(5,1),(5,4)]
  | 50 => some [(0,1),(1,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0),(7,4)]
  | 54 => some [(1,3),(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(4,3),(8,3)]
  | 60 => some [(7,5),(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1),(8,1)]
  | 63 => some [(0,1),(6,5)]
  | 64 => some [(0,4),(6,2)]
  | 65 => some [(5,4),(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3),(6,3)]
  | 70 => some [(8,3)]
  | 71 => some [(5,5),(8,5)]
  | 72 => some [(1,0),(7,0)]
  | 73 => some [(4,3),(7,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(4,1),(8,1)]
  | 77 => some [(0,2),(6,5)]
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
theorem root6Node42Domains0_fast_eq : root6Node42Domains0 = expandDomains root6Node42Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node42Domains0 v = expandDomains root6Node42Domains0Fast v from by decide) v
def root6Node42Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,1)]
  | 5 => [(7,5)]
  | 6 => [(1,2)]
  | 7 => [(7,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(4,0)]
  | 11 => [(7,3)]
  | 12 => [(4,2)]
  | 13 => [(0,3)]
  | 14 => [(4,1)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(5,1)]
  | 18 => [(0,1)]
  | 19 => [(6,2)]
  | 20 => [(7,4)]
  | 21 => [(2,2),(2,4)]
  | 22 => [(1,3),(3,3)]
  | 23 => [(5,2)]
  | 24 => [(8,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(1,0)]
  | 28 => [(2,1)]
  | 29 => [(0,2)]
  | 30 => [(1,1),(7,1)]
  | 31 => [(0,1),(6,5)]
  | 32 => [(0,4),(6,2)]
  | 33 => [(5,4),(8,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(0,0)]
  | 38 => [(3,2)]
  | 39 => [(4,0),(8,0)]
  | 40 => [(3,0),(5,0)]
  | 41 => [(4,5)]
  | 42 => [(1,0),(7,0)]
  | 43 => [(4,3),(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(1,5)]
  | 48 => [(6,1)]
  | 49 => [(5,1),(5,4)]
  | 50 => [(0,1),(1,4)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0),(7,4)]
  | 54 => [(1,3),(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(7,0)]
  | 59 => [(4,3),(8,3)]
  | 60 => [(7,5),(8,5)]
  | 61 => [(6,1)]
  | 62 => [(5,1),(8,1)]
  | 63 => [(0,1),(6,5)]
  | 64 => [(0,4),(6,2)]
  | 65 => [(5,4),(8,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(7,4)]
  | 69 => [(1,3),(6,3)]
  | 70 => [(8,3)]
  | 71 => [(5,5),(8,5)]
  | 72 => [(1,0),(7,0)]
  | 73 => [(4,3),(7,1)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(4,1),(8,1)]
  | 77 => [(0,2),(6,5)]
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
def root6Node42Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(4,0)]
  | 11 => some [(7,3)]
  | 12 => some [(4,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(5,1)]
  | 18 => some [(0,1)]
  | 19 => some [(6,2)]
  | 20 => some [(7,4)]
  | 21 => some [(2,2),(2,4)]
  | 22 => some [(1,3),(3,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(1,0)]
  | 28 => some [(2,1)]
  | 29 => some [(0,2)]
  | 30 => some [(1,1),(7,1)]
  | 31 => some [(0,1),(6,5)]
  | 32 => some [(0,4),(6,2)]
  | 33 => some [(5,4),(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(3,2)]
  | 39 => some [(4,0),(8,0)]
  | 40 => some [(3,0),(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(1,0),(7,0)]
  | 43 => some [(4,3),(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(5,1),(5,4)]
  | 50 => some [(0,1),(1,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0),(7,4)]
  | 54 => some [(1,3),(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(4,3),(8,3)]
  | 60 => some [(7,5),(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1),(8,1)]
  | 63 => some [(0,1),(6,5)]
  | 64 => some [(0,4),(6,2)]
  | 65 => some [(5,4),(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3),(6,3)]
  | 70 => some [(8,3)]
  | 71 => some [(5,5),(8,5)]
  | 72 => some [(1,0),(7,0)]
  | 73 => some [(4,3),(7,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(4,1),(8,1)]
  | 77 => some [(0,2),(6,5)]
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
theorem root6Node42Domains1_fast_eq : root6Node42Domains1 = expandDomains root6Node42Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node42Domains1 v = expandDomains root6Node42Domains1Fast v from by decide) v
theorem root6Node42Step1Chunk0_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_0⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk0_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_1⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk0_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_2⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk0_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_3⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk0_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_4⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk0_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_5⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk1_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_0⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk1_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_1⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk1_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_2⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk1_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_3⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk1_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_4⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk1_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_5⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk2_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_0⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk2_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_1⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk2_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_2⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk2_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_3⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk2_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_4⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk2_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_5⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk3_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_0⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk3_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_1⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk3_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_2⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk3_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_3⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk3_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_4⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk3_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_5⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk4_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_0⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk4_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_1⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk4_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_2⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk4_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_3⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk4_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_4⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk4_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_5⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk5_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_0⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk5_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_1⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk5_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_2⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk5_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_3⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk5_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_4⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk5_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_5⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk6_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows6_0⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk6_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows6_1⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk6_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows6_2⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk6_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows6_3⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk6_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows6_4⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk6_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows6_5⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk7_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows7_0⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk7_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows7_1⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk7_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows7_2⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk7_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows7_3⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk7_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows7_4⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk7_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows7_5⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk8_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_0⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk8_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_1⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk8_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_2⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk8_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_3⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk8_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_4⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk8_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_5⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Narrowing_checked :
    checkNarrowing table34 root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_flatten table34Scope [table34Rows0_0,table34Rows0_1,table34Rows0_2,table34Rows0_3,table34Rows0_4,table34Rows0_5,table34Rows1_0,table34Rows1_1,table34Rows1_2,table34Rows1_3,table34Rows1_4,table34Rows1_5,table34Rows2_0,table34Rows2_1,table34Rows2_2,table34Rows2_3,table34Rows2_4,table34Rows2_5,table34Rows3_0,table34Rows3_1,table34Rows3_2,table34Rows3_3,table34Rows3_4,table34Rows3_5,table34Rows4_0,table34Rows4_1,table34Rows4_2,table34Rows4_3,table34Rows4_4,table34Rows4_5,table34Rows5_0,table34Rows5_1,table34Rows5_2,table34Rows5_3,table34Rows5_4,table34Rows5_5,table34Rows6_0,table34Rows6_1,table34Rows6_2,table34Rows6_3,table34Rows6_4,table34Rows6_5,table34Rows7_0,table34Rows7_1,table34Rows7_2,table34Rows7_3,table34Rows7_4,table34Rows7_5,table34Rows8_0,table34Rows8_1,table34Rows8_2,table34Rows8_3,table34Rows8_4,table34Rows8_5]
    root6Node42Domains0 root6Node42Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node42Step1Chunk0_0_checked, root6Node42Step1Chunk0_1_checked, root6Node42Step1Chunk0_2_checked, root6Node42Step1Chunk0_3_checked, root6Node42Step1Chunk0_4_checked, root6Node42Step1Chunk0_5_checked, root6Node42Step1Chunk1_0_checked, root6Node42Step1Chunk1_1_checked, root6Node42Step1Chunk1_2_checked, root6Node42Step1Chunk1_3_checked, root6Node42Step1Chunk1_4_checked, root6Node42Step1Chunk1_5_checked, root6Node42Step1Chunk2_0_checked, root6Node42Step1Chunk2_1_checked, root6Node42Step1Chunk2_2_checked, root6Node42Step1Chunk2_3_checked, root6Node42Step1Chunk2_4_checked, root6Node42Step1Chunk2_5_checked, root6Node42Step1Chunk3_0_checked, root6Node42Step1Chunk3_1_checked, root6Node42Step1Chunk3_2_checked, root6Node42Step1Chunk3_3_checked, root6Node42Step1Chunk3_4_checked, root6Node42Step1Chunk3_5_checked, root6Node42Step1Chunk4_0_checked, root6Node42Step1Chunk4_1_checked, root6Node42Step1Chunk4_2_checked, root6Node42Step1Chunk4_3_checked, root6Node42Step1Chunk4_4_checked, root6Node42Step1Chunk4_5_checked, root6Node42Step1Chunk5_0_checked, root6Node42Step1Chunk5_1_checked, root6Node42Step1Chunk5_2_checked, root6Node42Step1Chunk5_3_checked, root6Node42Step1Chunk5_4_checked, root6Node42Step1Chunk5_5_checked, root6Node42Step1Chunk6_0_checked, root6Node42Step1Chunk6_1_checked, root6Node42Step1Chunk6_2_checked, root6Node42Step1Chunk6_3_checked, root6Node42Step1Chunk6_4_checked, root6Node42Step1Chunk6_5_checked, root6Node42Step1Chunk7_0_checked, root6Node42Step1Chunk7_1_checked, root6Node42Step1Chunk7_2_checked, root6Node42Step1Chunk7_3_checked, root6Node42Step1Chunk7_4_checked, root6Node42Step1Chunk7_5_checked, root6Node42Step1Chunk8_0_checked, root6Node42Step1Chunk8_1_checked, root6Node42Step1Chunk8_2_checked, root6Node42Step1Chunk8_3_checked, root6Node42Step1Chunk8_4_checked, root6Node42Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node42Step1_checked :
    checkReplacement table34 root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq
    root6Node42Step1Narrowing_checked (by decide)
def root6Node42Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,1)]
  | 5 => [(7,5)]
  | 6 => [(1,2)]
  | 7 => [(7,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(4,0)]
  | 11 => [(7,3)]
  | 12 => [(4,2)]
  | 13 => [(0,3)]
  | 14 => [(4,1)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(5,1)]
  | 18 => [(0,1)]
  | 19 => [(6,2)]
  | 20 => [(7,4)]
  | 21 => [(2,2),(2,4)]
  | 22 => [(1,3),(3,3)]
  | 23 => [(5,2)]
  | 24 => [(8,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(1,0)]
  | 28 => [(2,1)]
  | 29 => [(0,2)]
  | 30 => [(1,1),(7,1)]
  | 31 => [(0,1),(6,5)]
  | 32 => [(0,4),(6,2)]
  | 33 => [(5,4),(8,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(0,0)]
  | 38 => [(3,2)]
  | 39 => [(4,0)]
  | 40 => [(3,0),(5,0)]
  | 41 => [(4,5)]
  | 42 => [(1,0),(7,0)]
  | 43 => [(4,3),(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(1,5)]
  | 48 => [(6,1)]
  | 49 => [(5,1)]
  | 50 => [(0,1)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0),(7,4)]
  | 54 => [(1,3),(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(7,0)]
  | 59 => [(8,3)]
  | 60 => [(8,5)]
  | 61 => [(6,1)]
  | 62 => [(5,1),(8,1)]
  | 63 => [(0,1),(6,5)]
  | 64 => [(0,4),(6,2)]
  | 65 => [(5,4),(8,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(7,4)]
  | 69 => [(1,3),(6,3)]
  | 70 => [(8,3)]
  | 71 => [(5,5),(8,5)]
  | 72 => [(1,0),(7,0)]
  | 73 => [(4,3),(7,1)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(4,1),(8,1)]
  | 77 => [(0,2),(6,5)]
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
def root6Node42Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(4,0)]
  | 11 => some [(7,3)]
  | 12 => some [(4,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(5,1)]
  | 18 => some [(0,1)]
  | 19 => some [(6,2)]
  | 20 => some [(7,4)]
  | 21 => some [(2,2),(2,4)]
  | 22 => some [(1,3),(3,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(1,0)]
  | 28 => some [(2,1)]
  | 29 => some [(0,2)]
  | 30 => some [(1,1),(7,1)]
  | 31 => some [(0,1),(6,5)]
  | 32 => some [(0,4),(6,2)]
  | 33 => some [(5,4),(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(3,2)]
  | 39 => some [(4,0)]
  | 40 => some [(3,0),(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(1,0),(7,0)]
  | 43 => some [(4,3),(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(5,1)]
  | 50 => some [(0,1)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0),(7,4)]
  | 54 => some [(1,3),(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1),(8,1)]
  | 63 => some [(0,1),(6,5)]
  | 64 => some [(0,4),(6,2)]
  | 65 => some [(5,4),(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3),(6,3)]
  | 70 => some [(8,3)]
  | 71 => some [(5,5),(8,5)]
  | 72 => some [(1,0),(7,0)]
  | 73 => some [(4,3),(7,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(4,1),(8,1)]
  | 77 => some [(0,2),(6,5)]
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
theorem root6Node42Domains2_fast_eq : root6Node42Domains2 = expandDomains root6Node42Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node42Domains2 v = expandDomains root6Node42Domains2Fast v from by decide) v
theorem root6Node42Step2Chunk0_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_0⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk0_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_1⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk0_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_2⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk0_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_3⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk0_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_4⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk0_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_5⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk1_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_0⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk1_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_1⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk1_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_2⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk1_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_3⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk1_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_4⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk1_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_5⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk2_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_0⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk2_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_1⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk2_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_2⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk2_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_3⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk2_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_4⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk2_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_5⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk3_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_0⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk3_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_1⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk3_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_2⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk3_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_3⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk3_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_4⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk3_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_5⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk4_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_0⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk4_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_1⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk4_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_2⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk4_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_3⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk4_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_4⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk4_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_5⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk5_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_0⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk5_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_1⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk5_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_2⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk5_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_3⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk5_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_4⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk5_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_5⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk6_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_0⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk6_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_1⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk6_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_2⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk6_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_3⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk6_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_4⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk6_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_5⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk7_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_0⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk7_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_1⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk7_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_2⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk7_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_3⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk7_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_4⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk7_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_5⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk8_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_0⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk8_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_1⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk8_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_2⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk8_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_3⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk8_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_4⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Chunk8_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_5⟩
      root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq (by decide)
theorem root6Node42Step2Narrowing_checked :
    checkNarrowing table19 root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkNarrowing_flatten table19Scope [table19Rows0_0,table19Rows0_1,table19Rows0_2,table19Rows0_3,table19Rows0_4,table19Rows0_5,table19Rows1_0,table19Rows1_1,table19Rows1_2,table19Rows1_3,table19Rows1_4,table19Rows1_5,table19Rows2_0,table19Rows2_1,table19Rows2_2,table19Rows2_3,table19Rows2_4,table19Rows2_5,table19Rows3_0,table19Rows3_1,table19Rows3_2,table19Rows3_3,table19Rows3_4,table19Rows3_5,table19Rows4_0,table19Rows4_1,table19Rows4_2,table19Rows4_3,table19Rows4_4,table19Rows4_5,table19Rows5_0,table19Rows5_1,table19Rows5_2,table19Rows5_3,table19Rows5_4,table19Rows5_5,table19Rows6_0,table19Rows6_1,table19Rows6_2,table19Rows6_3,table19Rows6_4,table19Rows6_5,table19Rows7_0,table19Rows7_1,table19Rows7_2,table19Rows7_3,table19Rows7_4,table19Rows7_5,table19Rows8_0,table19Rows8_1,table19Rows8_2,table19Rows8_3,table19Rows8_4,table19Rows8_5]
    root6Node42Domains1 root6Node42Domains2 (by
      simp only [List.all_cons, List.all_nil, root6Node42Step2Chunk0_0_checked, root6Node42Step2Chunk0_1_checked, root6Node42Step2Chunk0_2_checked, root6Node42Step2Chunk0_3_checked, root6Node42Step2Chunk0_4_checked, root6Node42Step2Chunk0_5_checked, root6Node42Step2Chunk1_0_checked, root6Node42Step2Chunk1_1_checked, root6Node42Step2Chunk1_2_checked, root6Node42Step2Chunk1_3_checked, root6Node42Step2Chunk1_4_checked, root6Node42Step2Chunk1_5_checked, root6Node42Step2Chunk2_0_checked, root6Node42Step2Chunk2_1_checked, root6Node42Step2Chunk2_2_checked, root6Node42Step2Chunk2_3_checked, root6Node42Step2Chunk2_4_checked, root6Node42Step2Chunk2_5_checked, root6Node42Step2Chunk3_0_checked, root6Node42Step2Chunk3_1_checked, root6Node42Step2Chunk3_2_checked, root6Node42Step2Chunk3_3_checked, root6Node42Step2Chunk3_4_checked, root6Node42Step2Chunk3_5_checked, root6Node42Step2Chunk4_0_checked, root6Node42Step2Chunk4_1_checked, root6Node42Step2Chunk4_2_checked, root6Node42Step2Chunk4_3_checked, root6Node42Step2Chunk4_4_checked, root6Node42Step2Chunk4_5_checked, root6Node42Step2Chunk5_0_checked, root6Node42Step2Chunk5_1_checked, root6Node42Step2Chunk5_2_checked, root6Node42Step2Chunk5_3_checked, root6Node42Step2Chunk5_4_checked, root6Node42Step2Chunk5_5_checked, root6Node42Step2Chunk6_0_checked, root6Node42Step2Chunk6_1_checked, root6Node42Step2Chunk6_2_checked, root6Node42Step2Chunk6_3_checked, root6Node42Step2Chunk6_4_checked, root6Node42Step2Chunk6_5_checked, root6Node42Step2Chunk7_0_checked, root6Node42Step2Chunk7_1_checked, root6Node42Step2Chunk7_2_checked, root6Node42Step2Chunk7_3_checked, root6Node42Step2Chunk7_4_checked, root6Node42Step2Chunk7_5_checked, root6Node42Step2Chunk8_0_checked, root6Node42Step2Chunk8_1_checked, root6Node42Step2Chunk8_2_checked, root6Node42Step2Chunk8_3_checked, root6Node42Step2Chunk8_4_checked, root6Node42Step2Chunk8_5_checked, Bool.true_and])
theorem root6Node42Step2_checked :
    checkReplacement table19 root6Node42Domains1 root6Node42Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root6Node42Domains1 root6Node42Domains2
    root6Node42Domains1Fast root6Node42Domains2Fast
    root6Node42Domains1_fast_eq root6Node42Domains2_fast_eq
    root6Node42Step2Narrowing_checked (by decide)
def root6Node42Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,1)]
  | 5 => [(7,5)]
  | 6 => [(1,2)]
  | 7 => [(7,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(4,0)]
  | 11 => [(7,3)]
  | 12 => [(4,2)]
  | 13 => [(0,3)]
  | 14 => [(4,1)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(5,1)]
  | 18 => [(0,1)]
  | 19 => [(6,2)]
  | 20 => [(7,4)]
  | 21 => [(2,2),(2,4)]
  | 22 => [(1,3),(3,3)]
  | 23 => [(5,2)]
  | 24 => [(8,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(1,0)]
  | 28 => [(2,1)]
  | 29 => [(0,2)]
  | 30 => [(1,1),(7,1)]
  | 31 => [(0,1),(6,5)]
  | 32 => [(0,4),(6,2)]
  | 33 => [(5,4),(8,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(0,0)]
  | 38 => [(3,2)]
  | 39 => [(4,0)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(1,0),(7,0)]
  | 43 => [(4,3),(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(1,5)]
  | 48 => [(6,1)]
  | 49 => [(5,1)]
  | 50 => [(0,1)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0),(7,4)]
  | 54 => [(1,3),(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(7,0)]
  | 59 => [(8,3)]
  | 60 => [(8,5)]
  | 61 => [(6,1)]
  | 62 => [(5,1),(8,1)]
  | 63 => [(0,1),(6,5)]
  | 64 => [(0,4),(6,2)]
  | 65 => [(5,4),(8,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(7,4)]
  | 69 => [(1,3),(6,3)]
  | 70 => [(8,3)]
  | 71 => [(5,5),(8,5)]
  | 72 => [(1,0),(7,0)]
  | 73 => [(4,3),(7,1)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(4,1),(8,1)]
  | 77 => [(0,2),(6,5)]
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
def root6Node42Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(4,0)]
  | 11 => some [(7,3)]
  | 12 => some [(4,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(5,1)]
  | 18 => some [(0,1)]
  | 19 => some [(6,2)]
  | 20 => some [(7,4)]
  | 21 => some [(2,2),(2,4)]
  | 22 => some [(1,3),(3,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(1,0)]
  | 28 => some [(2,1)]
  | 29 => some [(0,2)]
  | 30 => some [(1,1),(7,1)]
  | 31 => some [(0,1),(6,5)]
  | 32 => some [(0,4),(6,2)]
  | 33 => some [(5,4),(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(3,2)]
  | 39 => some [(4,0)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(1,0),(7,0)]
  | 43 => some [(4,3),(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(5,1)]
  | 50 => some [(0,1)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0),(7,4)]
  | 54 => some [(1,3),(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1),(8,1)]
  | 63 => some [(0,1),(6,5)]
  | 64 => some [(0,4),(6,2)]
  | 65 => some [(5,4),(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3),(6,3)]
  | 70 => some [(8,3)]
  | 71 => some [(5,5),(8,5)]
  | 72 => some [(1,0),(7,0)]
  | 73 => some [(4,3),(7,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(4,1),(8,1)]
  | 77 => some [(0,2),(6,5)]
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
theorem root6Node42Domains3_fast_eq : root6Node42Domains3 = expandDomains root6Node42Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node42Domains3 v = expandDomains root6Node42Domains3Fast v from by decide) v
theorem root6Node42Step3Chunk0_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_0⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk0_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_1⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk0_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_2⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk0_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_3⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk0_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_4⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk0_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_5⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk1_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_0⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk1_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_1⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk1_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_2⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk1_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_3⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk1_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_4⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk1_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_5⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk2_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_0⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk2_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_1⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk2_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_2⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk2_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_3⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk2_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_4⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk2_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_5⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk3_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_0⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk3_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_1⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk3_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_2⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk3_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_3⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk3_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_4⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk3_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_5⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk4_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_0⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk4_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_1⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk4_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_2⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk4_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_3⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk4_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_4⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk4_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_5⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk5_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_0⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk5_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_1⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk5_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_2⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk5_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_3⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk5_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_4⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk5_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_5⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk6_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_0⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk6_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_1⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk6_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_2⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk6_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_3⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk6_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_4⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk6_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_5⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk7_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_0⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk7_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_1⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk7_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_2⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk7_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_3⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk7_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_4⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk7_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_5⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk8_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_0⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk8_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_1⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk8_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_2⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk8_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_3⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk8_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_4⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Chunk8_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_5⟩
      root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq (by decide)
theorem root6Node42Step3Narrowing_checked :
    checkNarrowing table6 root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkNarrowing_flatten table6Scope [table6Rows0_0,table6Rows0_1,table6Rows0_2,table6Rows0_3,table6Rows0_4,table6Rows0_5,table6Rows1_0,table6Rows1_1,table6Rows1_2,table6Rows1_3,table6Rows1_4,table6Rows1_5,table6Rows2_0,table6Rows2_1,table6Rows2_2,table6Rows2_3,table6Rows2_4,table6Rows2_5,table6Rows3_0,table6Rows3_1,table6Rows3_2,table6Rows3_3,table6Rows3_4,table6Rows3_5,table6Rows4_0,table6Rows4_1,table6Rows4_2,table6Rows4_3,table6Rows4_4,table6Rows4_5,table6Rows5_0,table6Rows5_1,table6Rows5_2,table6Rows5_3,table6Rows5_4,table6Rows5_5,table6Rows6_0,table6Rows6_1,table6Rows6_2,table6Rows6_3,table6Rows6_4,table6Rows6_5,table6Rows7_0,table6Rows7_1,table6Rows7_2,table6Rows7_3,table6Rows7_4,table6Rows7_5,table6Rows8_0,table6Rows8_1,table6Rows8_2,table6Rows8_3,table6Rows8_4,table6Rows8_5]
    root6Node42Domains2 root6Node42Domains3 (by
      simp only [List.all_cons, List.all_nil, root6Node42Step3Chunk0_0_checked, root6Node42Step3Chunk0_1_checked, root6Node42Step3Chunk0_2_checked, root6Node42Step3Chunk0_3_checked, root6Node42Step3Chunk0_4_checked, root6Node42Step3Chunk0_5_checked, root6Node42Step3Chunk1_0_checked, root6Node42Step3Chunk1_1_checked, root6Node42Step3Chunk1_2_checked, root6Node42Step3Chunk1_3_checked, root6Node42Step3Chunk1_4_checked, root6Node42Step3Chunk1_5_checked, root6Node42Step3Chunk2_0_checked, root6Node42Step3Chunk2_1_checked, root6Node42Step3Chunk2_2_checked, root6Node42Step3Chunk2_3_checked, root6Node42Step3Chunk2_4_checked, root6Node42Step3Chunk2_5_checked, root6Node42Step3Chunk3_0_checked, root6Node42Step3Chunk3_1_checked, root6Node42Step3Chunk3_2_checked, root6Node42Step3Chunk3_3_checked, root6Node42Step3Chunk3_4_checked, root6Node42Step3Chunk3_5_checked, root6Node42Step3Chunk4_0_checked, root6Node42Step3Chunk4_1_checked, root6Node42Step3Chunk4_2_checked, root6Node42Step3Chunk4_3_checked, root6Node42Step3Chunk4_4_checked, root6Node42Step3Chunk4_5_checked, root6Node42Step3Chunk5_0_checked, root6Node42Step3Chunk5_1_checked, root6Node42Step3Chunk5_2_checked, root6Node42Step3Chunk5_3_checked, root6Node42Step3Chunk5_4_checked, root6Node42Step3Chunk5_5_checked, root6Node42Step3Chunk6_0_checked, root6Node42Step3Chunk6_1_checked, root6Node42Step3Chunk6_2_checked, root6Node42Step3Chunk6_3_checked, root6Node42Step3Chunk6_4_checked, root6Node42Step3Chunk6_5_checked, root6Node42Step3Chunk7_0_checked, root6Node42Step3Chunk7_1_checked, root6Node42Step3Chunk7_2_checked, root6Node42Step3Chunk7_3_checked, root6Node42Step3Chunk7_4_checked, root6Node42Step3Chunk7_5_checked, root6Node42Step3Chunk8_0_checked, root6Node42Step3Chunk8_1_checked, root6Node42Step3Chunk8_2_checked, root6Node42Step3Chunk8_3_checked, root6Node42Step3Chunk8_4_checked, root6Node42Step3Chunk8_5_checked, Bool.true_and])
theorem root6Node42Step3_checked :
    checkReplacement table6 root6Node42Domains2 root6Node42Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root6Node42Domains2 root6Node42Domains3
    root6Node42Domains2Fast root6Node42Domains3Fast
    root6Node42Domains2_fast_eq root6Node42Domains3_fast_eq
    root6Node42Step3Narrowing_checked (by decide)
def root6Node43Domains0 : Domains 91 State := restrict root6Node42Domains3 21 (2,2)
def root6Node43Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(4,0)]
  | 11 => some [(7,3)]
  | 12 => some [(4,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(5,1)]
  | 18 => some [(0,1)]
  | 19 => some [(6,2)]
  | 20 => some [(7,4)]
  | 21 => some [(2,2)]
  | 22 => some [(1,3),(3,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(1,0)]
  | 28 => some [(2,1)]
  | 29 => some [(0,2)]
  | 30 => some [(1,1),(7,1)]
  | 31 => some [(0,1),(6,5)]
  | 32 => some [(0,4),(6,2)]
  | 33 => some [(5,4),(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(3,2)]
  | 39 => some [(4,0)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(1,0),(7,0)]
  | 43 => some [(4,3),(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(5,1)]
  | 50 => some [(0,1)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0),(7,4)]
  | 54 => some [(1,3),(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1),(8,1)]
  | 63 => some [(0,1),(6,5)]
  | 64 => some [(0,4),(6,2)]
  | 65 => some [(5,4),(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3),(6,3)]
  | 70 => some [(8,3)]
  | 71 => some [(5,5),(8,5)]
  | 72 => some [(1,0),(7,0)]
  | 73 => some [(4,3),(7,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(4,1),(8,1)]
  | 77 => some [(0,2),(6,5)]
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
theorem root6Node43Domains0_fast_eq : root6Node43Domains0 = expandDomains root6Node43Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node43Domains0 v = expandDomains root6Node43Domains0Fast v from by decide) v
def root6Node43Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,1)]
  | 5 => [(7,5)]
  | 6 => [(1,2)]
  | 7 => [(7,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(4,0)]
  | 11 => [(7,3)]
  | 12 => [(4,2)]
  | 13 => [(0,3)]
  | 14 => [(4,1)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(5,1)]
  | 18 => [(0,1)]
  | 19 => [(6,2)]
  | 20 => [(7,4)]
  | 21 => [(2,2)]
  | 22 => [(3,3)]
  | 23 => [(5,2)]
  | 24 => [(8,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(1,0)]
  | 28 => [(2,1)]
  | 29 => [(0,2)]
  | 30 => [(1,1)]
  | 31 => [(0,1)]
  | 32 => [(6,2)]
  | 33 => [(8,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(0,0)]
  | 38 => [(3,2)]
  | 39 => [(4,0)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(1,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(1,5)]
  | 48 => [(6,1)]
  | 49 => [(5,1)]
  | 50 => [(0,1)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(7,0)]
  | 59 => [(8,3)]
  | 60 => [(8,5)]
  | 61 => [(6,1)]
  | 62 => [(5,1)]
  | 63 => [(0,1)]
  | 64 => [(6,2)]
  | 65 => [(8,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(7,4)]
  | 69 => [(1,3),(6,3)]
  | 70 => [(8,3)]
  | 71 => [(8,5)]
  | 72 => [(1,0)]
  | 73 => [(7,1)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(4,1),(8,1)]
  | 77 => [(0,2),(6,5)]
  | 78 => [(1,3)]
  | 79 => [(8,2)]
  | 80 => [(5,0)]
  | 81 => [(4,5)]
  | 82 => [(7,0)]
  | 83 => [(7,3),(8,3)]
  | 84 => [(5,2),(8,5)]
  | 85 => [(0,4)]
  | 86 => [(5,4)]
  | 87 => [(0,0)]
  | 88 => [(7,2)]
  | 89 => [(0,1),(7,4)]
  | _ => [(6,2),(6,3)]
def root6Node43Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(4,0)]
  | 11 => some [(7,3)]
  | 12 => some [(4,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(5,1)]
  | 18 => some [(0,1)]
  | 19 => some [(6,2)]
  | 20 => some [(7,4)]
  | 21 => some [(2,2)]
  | 22 => some [(3,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(1,0)]
  | 28 => some [(2,1)]
  | 29 => some [(0,2)]
  | 30 => some [(1,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(3,2)]
  | 39 => some [(4,0)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(1,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(5,1)]
  | 50 => some [(0,1)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3),(6,3)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(4,1),(8,1)]
  | 77 => some [(0,2),(6,5)]
  | 78 => some [(1,3)]
  | 79 => some [(8,2)]
  | 80 => some [(5,0)]
  | 81 => some [(4,5)]
  | 82 => some [(7,0)]
  | 83 => some [(7,3),(8,3)]
  | 84 => some [(5,2),(8,5)]
  | 85 => some [(0,4)]
  | 86 => some [(5,4)]
  | 87 => some [(0,0)]
  | 88 => some [(7,2)]
  | 89 => some [(0,1),(7,4)]
  | _ => some [(6,2),(6,3)]
theorem root6Node43Domains1_fast_eq : root6Node43Domains1 = expandDomains root6Node43Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node43Domains1 v = expandDomains root6Node43Domains1Fast v from by decide) v
theorem root6Node43Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Narrowing_checked :
    checkNarrowing table54 root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root6Node43Domains0 root6Node43Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node43Step1Chunk0_0_checked, root6Node43Step1Chunk0_1_checked, root6Node43Step1Chunk0_2_checked, root6Node43Step1Chunk0_3_checked, root6Node43Step1Chunk0_4_checked, root6Node43Step1Chunk0_5_checked, root6Node43Step1Chunk1_0_checked, root6Node43Step1Chunk1_1_checked, root6Node43Step1Chunk1_2_checked, root6Node43Step1Chunk1_3_checked, root6Node43Step1Chunk1_4_checked, root6Node43Step1Chunk1_5_checked, root6Node43Step1Chunk2_0_checked, root6Node43Step1Chunk2_1_checked, root6Node43Step1Chunk2_2_checked, root6Node43Step1Chunk2_3_checked, root6Node43Step1Chunk2_4_checked, root6Node43Step1Chunk2_5_checked, root6Node43Step1Chunk3_0_checked, root6Node43Step1Chunk3_1_checked, root6Node43Step1Chunk3_2_checked, root6Node43Step1Chunk3_3_checked, root6Node43Step1Chunk3_4_checked, root6Node43Step1Chunk3_5_checked, root6Node43Step1Chunk4_0_checked, root6Node43Step1Chunk4_1_checked, root6Node43Step1Chunk4_2_checked, root6Node43Step1Chunk4_3_checked, root6Node43Step1Chunk4_4_checked, root6Node43Step1Chunk4_5_checked, root6Node43Step1Chunk5_0_checked, root6Node43Step1Chunk5_1_checked, root6Node43Step1Chunk5_2_checked, root6Node43Step1Chunk5_3_checked, root6Node43Step1Chunk5_4_checked, root6Node43Step1Chunk5_5_checked, root6Node43Step1Chunk6_0_checked, root6Node43Step1Chunk6_1_checked, root6Node43Step1Chunk6_2_checked, root6Node43Step1Chunk6_3_checked, root6Node43Step1Chunk6_4_checked, root6Node43Step1Chunk6_5_checked, root6Node43Step1Chunk7_0_checked, root6Node43Step1Chunk7_1_checked, root6Node43Step1Chunk7_2_checked, root6Node43Step1Chunk7_3_checked, root6Node43Step1Chunk7_4_checked, root6Node43Step1Chunk7_5_checked, root6Node43Step1Chunk8_0_checked, root6Node43Step1Chunk8_1_checked, root6Node43Step1Chunk8_2_checked, root6Node43Step1Chunk8_3_checked, root6Node43Step1Chunk8_4_checked, root6Node43Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node43Step1_checked :
    checkReplacement table54 root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq
    root6Node43Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
