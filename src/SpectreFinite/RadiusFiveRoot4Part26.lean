module

public import SpectreFinite.RadiusFiveRoot4Part25
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
def root4Node64Domains0 : Domains 91 State := restrict root4Node63Domains0 39 (1,5)
def root4Node64Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(8,1)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(2,2)]
  | 16 => some [(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(4,1)]
  | 22 => some [(0,2)]
  | 23 => some [(1,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(7,3)]
  | 31 => some [(5,2)]
  | 32 => some [(5,0)]
  | 33 => some [(4,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(7,1)]
  | 39 => some [(1,5)]
  | 40 => some [(0,1),(6,4)]
  | 41 => some [(1,2),(6,2)]
  | 42 => some [(8,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0),(8,0)]
  | 49 => some [(4,5),(7,3)]
  | 50 => some [(4,2),(7,0),(8,2)]
  | 51 => some [(0,3),(1,0)]
  | 52 => some [(7,1),(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0),(6,4)]
  | 60 => some [(1,2),(7,2)]
  | 61 => some [(5,0),(5,3)]
  | 62 => some [(4,5),(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,1)]
  | 70 => some [(0,0),(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3),(6,3)]
  | 74 => some [(7,2),(8,2)]
  | 75 => some [(4,0),(5,0),(8,0)]
  | 76 => some [(4,5),(7,3)]
  | 77 => some [(4,2),(7,0)]
  | 78 => some [(1,1),(6,1)]
  | 79 => some [(4,1),(8,1)]
  | 80 => some [(0,2),(6,5)]
  | 81 => some [(0,4),(1,1)]
  | 82 => some [(5,1),(5,4)]
  | 83 => some [(0,0),(0,1),(6,4)]
  | 84 => some [(1,2),(6,2),(7,2)]
  | 85 => some [(7,3),(8,3)]
  | 86 => some [(5,2),(5,5)]
  | 87 => some [(7,0),(8,0)]
  | 88 => some [(4,3),(8,3)]
  | 89 => some [(1,5),(3,5),(5,5)]
  | _ => some [(0,3),(1,0),(6,1)]
theorem root4Node64Domains0_fast_eq : root4Node64Domains0 = expandDomains root4Node64Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node64Domains0 v = expandDomains root4Node64Domains0Fast v from by decide) v
def root4Node64Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(7,2)]
  | 6 => [(4,3)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(4,1)]
  | 10 => [(0,2)]
  | 11 => [(1,1)]
  | 12 => [(8,1)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(2,2)]
  | 16 => [(3,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(4,1)]
  | 22 => [(0,2)]
  | 23 => [(1,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4)]
  | 30 => [(7,3)]
  | 31 => [(5,2)]
  | 32 => [(5,0)]
  | 33 => [(4,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(7,1)]
  | 39 => [(1,5)]
  | 40 => [(0,1),(6,4)]
  | 41 => [(1,2),(6,2)]
  | 42 => [(8,4)]
  | 43 => [(0,0)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(7,0)]
  | 51 => [(0,3),(1,0)]
  | 52 => [(7,1),(8,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(5,0),(5,3)]
  | 62 => [(4,5),(8,5)]
  | 63 => [(7,0)]
  | 64 => [(8,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(0,0),(6,3)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(7,0)]
  | 78 => [(1,1),(6,1)]
  | 79 => [(4,1),(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(5,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(7,3),(8,3)]
  | 86 => [(5,2),(5,5)]
  | 87 => [(7,0)]
  | 88 => [(4,3)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root4Node64Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(8,1)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(2,2)]
  | 16 => some [(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(4,1)]
  | 22 => some [(0,2)]
  | 23 => some [(1,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(7,3)]
  | 31 => some [(5,2)]
  | 32 => some [(5,0)]
  | 33 => some [(4,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(7,1)]
  | 39 => some [(1,5)]
  | 40 => some [(0,1),(6,4)]
  | 41 => some [(1,2),(6,2)]
  | 42 => some [(8,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(7,0)]
  | 51 => some [(0,3),(1,0)]
  | 52 => some [(7,1),(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,0),(5,3)]
  | 62 => some [(4,5),(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(0,0),(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(7,0)]
  | 78 => some [(1,1),(6,1)]
  | 79 => some [(4,1),(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(7,3),(8,3)]
  | 86 => some [(5,2),(5,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root4Node64Domains1_fast_eq : root4Node64Domains1 = expandDomains root4Node64Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node64Domains1 v = expandDomains root4Node64Domains1Fast v from by decide) v
theorem root4Node64Step1Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq (by decide)
theorem root4Node64Step1Narrowing_checked :
    checkNarrowing table57 root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root4Node64Domains0 root4Node64Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node64Step1Chunk0_0_checked, root4Node64Step1Chunk0_1_checked, root4Node64Step1Chunk0_2_checked, root4Node64Step1Chunk0_3_checked, root4Node64Step1Chunk0_4_checked, root4Node64Step1Chunk0_5_checked, root4Node64Step1Chunk1_0_checked, root4Node64Step1Chunk1_1_checked, root4Node64Step1Chunk1_2_checked, root4Node64Step1Chunk1_3_checked, root4Node64Step1Chunk1_4_checked, root4Node64Step1Chunk1_5_checked, root4Node64Step1Chunk2_0_checked, root4Node64Step1Chunk2_1_checked, root4Node64Step1Chunk2_2_checked, root4Node64Step1Chunk2_3_checked, root4Node64Step1Chunk2_4_checked, root4Node64Step1Chunk2_5_checked, root4Node64Step1Chunk3_0_checked, root4Node64Step1Chunk3_1_checked, root4Node64Step1Chunk3_2_checked, root4Node64Step1Chunk3_3_checked, root4Node64Step1Chunk3_4_checked, root4Node64Step1Chunk3_5_checked, root4Node64Step1Chunk4_0_checked, root4Node64Step1Chunk4_1_checked, root4Node64Step1Chunk4_2_checked, root4Node64Step1Chunk4_3_checked, root4Node64Step1Chunk4_4_checked, root4Node64Step1Chunk4_5_checked, root4Node64Step1Chunk5_0_checked, root4Node64Step1Chunk5_1_checked, root4Node64Step1Chunk5_2_checked, root4Node64Step1Chunk5_3_checked, root4Node64Step1Chunk5_4_checked, root4Node64Step1Chunk5_5_checked, root4Node64Step1Chunk6_0_checked, root4Node64Step1Chunk6_1_checked, root4Node64Step1Chunk6_2_checked, root4Node64Step1Chunk6_3_checked, root4Node64Step1Chunk6_4_checked, root4Node64Step1Chunk6_5_checked, root4Node64Step1Chunk7_0_checked, root4Node64Step1Chunk7_1_checked, root4Node64Step1Chunk7_2_checked, root4Node64Step1Chunk7_3_checked, root4Node64Step1Chunk7_4_checked, root4Node64Step1Chunk7_5_checked, root4Node64Step1Chunk8_0_checked, root4Node64Step1Chunk8_1_checked, root4Node64Step1Chunk8_2_checked, root4Node64Step1Chunk8_3_checked, root4Node64Step1Chunk8_4_checked, root4Node64Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node64Step1_checked :
    checkReplacement table57 root4Node64Domains0 root4Node64Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node64Domains0 root4Node64Domains1
    root4Node64Domains0Fast root4Node64Domains1Fast
    root4Node64Domains0_fast_eq root4Node64Domains1_fast_eq
    root4Node64Step1Narrowing_checked (by decide)
def root4Node64Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(7,2)]
  | 6 => [(4,3)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(4,1)]
  | 10 => [(0,2)]
  | 11 => [(1,1)]
  | 12 => [(8,1)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(2,2)]
  | 16 => [(3,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(4,1)]
  | 22 => [(0,2)]
  | 23 => [(1,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4)]
  | 30 => [(7,3)]
  | 31 => [(5,2)]
  | 32 => [(5,0)]
  | 33 => [(4,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(7,1)]
  | 39 => [(1,5)]
  | 40 => [(6,4)]
  | 41 => [(1,2)]
  | 42 => [(8,4)]
  | 43 => [(0,0)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(7,0)]
  | 51 => [(0,3)]
  | 52 => [(8,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(5,3)]
  | 62 => [(8,5)]
  | 63 => [(7,0)]
  | 64 => [(8,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(6,3)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(7,0)]
  | 78 => [(1,1)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(5,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5)]
  | 87 => [(7,0)]
  | 88 => [(4,3)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root4Node64Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(8,1)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(2,2)]
  | 16 => some [(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(4,1)]
  | 22 => some [(0,2)]
  | 23 => some [(1,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(7,3)]
  | 31 => some [(5,2)]
  | 32 => some [(5,0)]
  | 33 => some [(4,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(7,1)]
  | 39 => some [(1,5)]
  | 40 => some [(6,4)]
  | 41 => some [(1,2)]
  | 42 => some [(8,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(7,0)]
  | 51 => some [(0,3)]
  | 52 => some [(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,3)]
  | 62 => some [(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(7,0)]
  | 78 => some [(1,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root4Node64Domains2_fast_eq : root4Node64Domains2 = expandDomains root4Node64Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node64Domains2 v = expandDomains root4Node64Domains2Fast v from by decide) v
theorem root4Node64Step2Chunk0_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_0⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk0_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_1⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk0_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_2⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk0_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_3⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk0_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_4⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk0_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_5⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk1_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_0⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk1_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_1⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk1_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_2⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk1_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_3⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk1_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_4⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk1_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_5⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk2_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_0⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk2_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_1⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk2_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_2⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk2_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_3⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk2_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_4⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk2_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_5⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk3_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_0⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk3_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_1⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk3_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_2⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk3_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_3⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk3_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_4⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk3_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_5⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk4_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_0⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk4_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_1⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk4_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_2⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk4_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_3⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk4_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_4⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk4_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_5⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk5_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_0⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk5_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_1⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk5_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_2⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk5_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_3⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk5_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_4⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk5_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_5⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk6_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_0⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk6_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_1⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk6_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_2⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk6_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_3⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk6_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_4⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk6_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_5⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk7_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_0⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk7_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_1⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk7_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_2⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk7_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_3⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk7_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_4⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk7_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_5⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk8_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_0⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk8_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_1⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk8_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_2⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk8_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_3⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk8_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_4⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Chunk8_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_5⟩
      root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq (by decide)
theorem root4Node64Step2Narrowing_checked :
    checkNarrowing table52 root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkNarrowing_flatten table52Scope [table52Rows0_0,table52Rows0_1,table52Rows0_2,table52Rows0_3,table52Rows0_4,table52Rows0_5,table52Rows1_0,table52Rows1_1,table52Rows1_2,table52Rows1_3,table52Rows1_4,table52Rows1_5,table52Rows2_0,table52Rows2_1,table52Rows2_2,table52Rows2_3,table52Rows2_4,table52Rows2_5,table52Rows3_0,table52Rows3_1,table52Rows3_2,table52Rows3_3,table52Rows3_4,table52Rows3_5,table52Rows4_0,table52Rows4_1,table52Rows4_2,table52Rows4_3,table52Rows4_4,table52Rows4_5,table52Rows5_0,table52Rows5_1,table52Rows5_2,table52Rows5_3,table52Rows5_4,table52Rows5_5,table52Rows6_0,table52Rows6_1,table52Rows6_2,table52Rows6_3,table52Rows6_4,table52Rows6_5,table52Rows7_0,table52Rows7_1,table52Rows7_2,table52Rows7_3,table52Rows7_4,table52Rows7_5,table52Rows8_0,table52Rows8_1,table52Rows8_2,table52Rows8_3,table52Rows8_4,table52Rows8_5]
    root4Node64Domains1 root4Node64Domains2 (by
      simp only [List.all_cons, List.all_nil, root4Node64Step2Chunk0_0_checked, root4Node64Step2Chunk0_1_checked, root4Node64Step2Chunk0_2_checked, root4Node64Step2Chunk0_3_checked, root4Node64Step2Chunk0_4_checked, root4Node64Step2Chunk0_5_checked, root4Node64Step2Chunk1_0_checked, root4Node64Step2Chunk1_1_checked, root4Node64Step2Chunk1_2_checked, root4Node64Step2Chunk1_3_checked, root4Node64Step2Chunk1_4_checked, root4Node64Step2Chunk1_5_checked, root4Node64Step2Chunk2_0_checked, root4Node64Step2Chunk2_1_checked, root4Node64Step2Chunk2_2_checked, root4Node64Step2Chunk2_3_checked, root4Node64Step2Chunk2_4_checked, root4Node64Step2Chunk2_5_checked, root4Node64Step2Chunk3_0_checked, root4Node64Step2Chunk3_1_checked, root4Node64Step2Chunk3_2_checked, root4Node64Step2Chunk3_3_checked, root4Node64Step2Chunk3_4_checked, root4Node64Step2Chunk3_5_checked, root4Node64Step2Chunk4_0_checked, root4Node64Step2Chunk4_1_checked, root4Node64Step2Chunk4_2_checked, root4Node64Step2Chunk4_3_checked, root4Node64Step2Chunk4_4_checked, root4Node64Step2Chunk4_5_checked, root4Node64Step2Chunk5_0_checked, root4Node64Step2Chunk5_1_checked, root4Node64Step2Chunk5_2_checked, root4Node64Step2Chunk5_3_checked, root4Node64Step2Chunk5_4_checked, root4Node64Step2Chunk5_5_checked, root4Node64Step2Chunk6_0_checked, root4Node64Step2Chunk6_1_checked, root4Node64Step2Chunk6_2_checked, root4Node64Step2Chunk6_3_checked, root4Node64Step2Chunk6_4_checked, root4Node64Step2Chunk6_5_checked, root4Node64Step2Chunk7_0_checked, root4Node64Step2Chunk7_1_checked, root4Node64Step2Chunk7_2_checked, root4Node64Step2Chunk7_3_checked, root4Node64Step2Chunk7_4_checked, root4Node64Step2Chunk7_5_checked, root4Node64Step2Chunk8_0_checked, root4Node64Step2Chunk8_1_checked, root4Node64Step2Chunk8_2_checked, root4Node64Step2Chunk8_3_checked, root4Node64Step2Chunk8_4_checked, root4Node64Step2Chunk8_5_checked, Bool.true_and])
theorem root4Node64Step2_checked :
    checkReplacement table52 root4Node64Domains1 root4Node64Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root4Node64Domains1 root4Node64Domains2
    root4Node64Domains1Fast root4Node64Domains2Fast
    root4Node64Domains1_fast_eq root4Node64Domains2_fast_eq
    root4Node64Step2Narrowing_checked (by decide)
theorem root4Node64Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node64Domains2 (.output 31) = true := by decide
def root4Node65Domains0 : Domains 91 State := restrict root4Node63Domains0 39 (7,5)
def root4Node65Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(8,1)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(2,2)]
  | 16 => some [(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(4,1)]
  | 22 => some [(0,2)]
  | 23 => some [(1,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(7,3)]
  | 31 => some [(5,2)]
  | 32 => some [(5,0)]
  | 33 => some [(4,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(7,1)]
  | 39 => some [(7,5)]
  | 40 => some [(0,1),(6,4)]
  | 41 => some [(1,2),(6,2)]
  | 42 => some [(8,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0),(8,0)]
  | 49 => some [(4,5),(7,3)]
  | 50 => some [(4,2),(7,0),(8,2)]
  | 51 => some [(0,3),(1,0)]
  | 52 => some [(7,1),(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0),(6,4)]
  | 60 => some [(1,2),(7,2)]
  | 61 => some [(5,0),(5,3)]
  | 62 => some [(4,5),(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,1)]
  | 70 => some [(0,0),(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3),(6,3)]
  | 74 => some [(7,2),(8,2)]
  | 75 => some [(4,0),(5,0),(8,0)]
  | 76 => some [(4,5),(7,3)]
  | 77 => some [(4,2),(7,0)]
  | 78 => some [(1,1),(6,1)]
  | 79 => some [(4,1),(8,1)]
  | 80 => some [(0,2),(6,5)]
  | 81 => some [(0,4),(1,1)]
  | 82 => some [(5,1),(5,4)]
  | 83 => some [(0,0),(0,1),(6,4)]
  | 84 => some [(1,2),(6,2),(7,2)]
  | 85 => some [(7,3),(8,3)]
  | 86 => some [(5,2),(5,5)]
  | 87 => some [(7,0),(8,0)]
  | 88 => some [(4,3),(8,3)]
  | 89 => some [(1,5),(3,5),(5,5)]
  | _ => some [(0,3),(1,0),(6,1)]
theorem root4Node65Domains0_fast_eq : root4Node65Domains0 = expandDomains root4Node65Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node65Domains0 v = expandDomains root4Node65Domains0Fast v from by decide) v
def root4Node65Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(7,2)]
  | 6 => [(4,3)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(4,1)]
  | 10 => [(0,2)]
  | 11 => [(1,1)]
  | 12 => [(8,1)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(2,2)]
  | 16 => [(3,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(4,1)]
  | 22 => [(0,2)]
  | 23 => [(1,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4)]
  | 30 => [(7,3)]
  | 31 => [(5,2)]
  | 32 => [(5,0)]
  | 33 => [(4,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(7,1)]
  | 39 => [(7,5)]
  | 40 => [(0,1),(6,4)]
  | 41 => [(1,2),(6,2)]
  | 42 => [(8,4)]
  | 43 => [(0,0)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(8,0)]
  | 49 => [(7,3)]
  | 50 => [(4,2),(8,2)]
  | 51 => [(0,3),(1,0)]
  | 52 => [(7,1),(8,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(6,4)]
  | 60 => [(1,2)]
  | 61 => [(5,0),(5,3)]
  | 62 => [(4,5),(8,5)]
  | 63 => [(7,0)]
  | 64 => [(8,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(0,3)]
  | 70 => [(0,0),(6,3)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3),(6,3)]
  | 74 => [(7,2),(8,2)]
  | 75 => [(4,0),(8,0)]
  | 76 => [(7,3)]
  | 77 => [(4,2)]
  | 78 => [(1,1),(6,1)]
  | 79 => [(4,1),(8,1)]
  | 80 => [(0,2),(6,5)]
  | 81 => [(0,4),(1,1)]
  | 82 => [(5,1),(5,4)]
  | 83 => [(0,1),(6,4)]
  | 84 => [(1,2),(6,2)]
  | 85 => [(7,3),(8,3)]
  | 86 => [(5,2),(5,5)]
  | 87 => [(7,0),(8,0)]
  | 88 => [(4,3),(8,3)]
  | 89 => [(3,5),(5,5)]
  | _ => [(0,3),(1,0)]
def root4Node65Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(8,1)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(2,2)]
  | 16 => some [(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(4,1)]
  | 22 => some [(0,2)]
  | 23 => some [(1,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(7,3)]
  | 31 => some [(5,2)]
  | 32 => some [(5,0)]
  | 33 => some [(4,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(7,1)]
  | 39 => some [(7,5)]
  | 40 => some [(0,1),(6,4)]
  | 41 => some [(1,2),(6,2)]
  | 42 => some [(8,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3)]
  | 50 => some [(4,2),(8,2)]
  | 51 => some [(0,3),(1,0)]
  | 52 => some [(7,1),(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(5,0),(5,3)]
  | 62 => some [(4,5),(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(0,0),(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3),(6,3)]
  | 74 => some [(7,2),(8,2)]
  | 75 => some [(4,0),(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(1,1),(6,1)]
  | 79 => some [(4,1),(8,1)]
  | 80 => some [(0,2),(6,5)]
  | 81 => some [(0,4),(1,1)]
  | 82 => some [(5,1),(5,4)]
  | 83 => some [(0,1),(6,4)]
  | 84 => some [(1,2),(6,2)]
  | 85 => some [(7,3),(8,3)]
  | 86 => some [(5,2),(5,5)]
  | 87 => some [(7,0),(8,0)]
  | 88 => some [(4,3),(8,3)]
  | 89 => some [(3,5),(5,5)]
  | _ => some [(0,3),(1,0)]
theorem root4Node65Domains1_fast_eq : root4Node65Domains1 = expandDomains root4Node65Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node65Domains1 v = expandDomains root4Node65Domains1Fast v from by decide) v
theorem root4Node65Step1Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq (by decide)
theorem root4Node65Step1Narrowing_checked :
    checkNarrowing table57 root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root4Node65Domains0 root4Node65Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node65Step1Chunk0_0_checked, root4Node65Step1Chunk0_1_checked, root4Node65Step1Chunk0_2_checked, root4Node65Step1Chunk0_3_checked, root4Node65Step1Chunk0_4_checked, root4Node65Step1Chunk0_5_checked, root4Node65Step1Chunk1_0_checked, root4Node65Step1Chunk1_1_checked, root4Node65Step1Chunk1_2_checked, root4Node65Step1Chunk1_3_checked, root4Node65Step1Chunk1_4_checked, root4Node65Step1Chunk1_5_checked, root4Node65Step1Chunk2_0_checked, root4Node65Step1Chunk2_1_checked, root4Node65Step1Chunk2_2_checked, root4Node65Step1Chunk2_3_checked, root4Node65Step1Chunk2_4_checked, root4Node65Step1Chunk2_5_checked, root4Node65Step1Chunk3_0_checked, root4Node65Step1Chunk3_1_checked, root4Node65Step1Chunk3_2_checked, root4Node65Step1Chunk3_3_checked, root4Node65Step1Chunk3_4_checked, root4Node65Step1Chunk3_5_checked, root4Node65Step1Chunk4_0_checked, root4Node65Step1Chunk4_1_checked, root4Node65Step1Chunk4_2_checked, root4Node65Step1Chunk4_3_checked, root4Node65Step1Chunk4_4_checked, root4Node65Step1Chunk4_5_checked, root4Node65Step1Chunk5_0_checked, root4Node65Step1Chunk5_1_checked, root4Node65Step1Chunk5_2_checked, root4Node65Step1Chunk5_3_checked, root4Node65Step1Chunk5_4_checked, root4Node65Step1Chunk5_5_checked, root4Node65Step1Chunk6_0_checked, root4Node65Step1Chunk6_1_checked, root4Node65Step1Chunk6_2_checked, root4Node65Step1Chunk6_3_checked, root4Node65Step1Chunk6_4_checked, root4Node65Step1Chunk6_5_checked, root4Node65Step1Chunk7_0_checked, root4Node65Step1Chunk7_1_checked, root4Node65Step1Chunk7_2_checked, root4Node65Step1Chunk7_3_checked, root4Node65Step1Chunk7_4_checked, root4Node65Step1Chunk7_5_checked, root4Node65Step1Chunk8_0_checked, root4Node65Step1Chunk8_1_checked, root4Node65Step1Chunk8_2_checked, root4Node65Step1Chunk8_3_checked, root4Node65Step1Chunk8_4_checked, root4Node65Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node65Step1_checked :
    checkReplacement table57 root4Node65Domains0 root4Node65Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node65Domains0 root4Node65Domains1
    root4Node65Domains0Fast root4Node65Domains1Fast
    root4Node65Domains0_fast_eq root4Node65Domains1_fast_eq
    root4Node65Step1Narrowing_checked (by decide)
def root4Node66Domains0 : Domains 91 State := restrict root4Node65Domains1 40 (0,1)
def root4Node66Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(8,1)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(2,2)]
  | 16 => some [(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(4,1)]
  | 22 => some [(0,2)]
  | 23 => some [(1,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(7,3)]
  | 31 => some [(5,2)]
  | 32 => some [(5,0)]
  | 33 => some [(4,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(7,1)]
  | 39 => some [(7,5)]
  | 40 => some [(0,1)]
  | 41 => some [(1,2),(6,2)]
  | 42 => some [(8,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3)]
  | 50 => some [(4,2),(8,2)]
  | 51 => some [(0,3),(1,0)]
  | 52 => some [(7,1),(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(5,0),(5,3)]
  | 62 => some [(4,5),(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(0,0),(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3),(6,3)]
  | 74 => some [(7,2),(8,2)]
  | 75 => some [(4,0),(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(1,1),(6,1)]
  | 79 => some [(4,1),(8,1)]
  | 80 => some [(0,2),(6,5)]
  | 81 => some [(0,4),(1,1)]
  | 82 => some [(5,1),(5,4)]
  | 83 => some [(0,1),(6,4)]
  | 84 => some [(1,2),(6,2)]
  | 85 => some [(7,3),(8,3)]
  | 86 => some [(5,2),(5,5)]
  | 87 => some [(7,0),(8,0)]
  | 88 => some [(4,3),(8,3)]
  | 89 => some [(3,5),(5,5)]
  | _ => some [(0,3),(1,0)]
theorem root4Node66Domains0_fast_eq : root4Node66Domains0 = expandDomains root4Node66Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node66Domains0 v = expandDomains root4Node66Domains0Fast v from by decide) v
def root4Node66Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(7,2)]
  | 6 => [(4,3)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(4,1)]
  | 10 => [(0,2)]
  | 11 => [(1,1)]
  | 12 => [(8,1)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(2,2)]
  | 16 => [(3,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(4,1)]
  | 22 => [(0,2)]
  | 23 => [(1,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4)]
  | 30 => [(7,3)]
  | 31 => [(5,2)]
  | 32 => [(5,0)]
  | 33 => [(4,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(7,1)]
  | 39 => [(7,5)]
  | 40 => [(0,1)]
  | 41 => [(6,2)]
  | 42 => [(8,4)]
  | 43 => [(0,0)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(8,0)]
  | 49 => [(7,3)]
  | 50 => [(4,2),(8,2)]
  | 51 => [(1,0)]
  | 52 => [(7,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(6,4)]
  | 60 => [(1,2)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(7,0)]
  | 64 => [(8,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(0,3)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(6,3)]
  | 74 => [(7,2)]
  | 75 => [(4,0)]
  | 76 => [(7,3)]
  | 77 => [(4,2)]
  | 78 => [(6,1)]
  | 79 => [(4,1)]
  | 80 => [(0,2)]
  | 81 => [(1,1)]
  | 82 => [(5,1)]
  | 83 => [(0,1),(6,4)]
  | 84 => [(1,2),(6,2)]
  | 85 => [(7,3)]
  | 86 => [(5,2)]
  | 87 => [(8,0)]
  | 88 => [(8,3)]
  | 89 => [(3,5),(5,5)]
  | _ => [(0,3),(1,0)]
def root4Node66Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(8,1)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(2,2)]
  | 16 => some [(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(4,1)]
  | 22 => some [(0,2)]
  | 23 => some [(1,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(7,3)]
  | 31 => some [(5,2)]
  | 32 => some [(5,0)]
  | 33 => some [(4,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(7,1)]
  | 39 => some [(7,5)]
  | 40 => some [(0,1)]
  | 41 => some [(6,2)]
  | 42 => some [(8,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3)]
  | 50 => some [(4,2),(8,2)]
  | 51 => some [(1,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(6,3)]
  | 74 => some [(7,2)]
  | 75 => some [(4,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(6,1)]
  | 79 => some [(4,1)]
  | 80 => some [(0,2)]
  | 81 => some [(1,1)]
  | 82 => some [(5,1)]
  | 83 => some [(0,1),(6,4)]
  | 84 => some [(1,2),(6,2)]
  | 85 => some [(7,3)]
  | 86 => some [(5,2)]
  | 87 => some [(8,0)]
  | 88 => some [(8,3)]
  | 89 => some [(3,5),(5,5)]
  | _ => some [(0,3),(1,0)]
theorem root4Node66Domains1_fast_eq : root4Node66Domains1 = expandDomains root4Node66Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node66Domains1 v = expandDomains root4Node66Domains1Fast v from by decide) v
theorem root4Node66Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq (by decide)
theorem root4Node66Step1Narrowing_checked :
    checkNarrowing table54 root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root4Node66Domains0 root4Node66Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node66Step1Chunk0_0_checked, root4Node66Step1Chunk0_1_checked, root4Node66Step1Chunk0_2_checked, root4Node66Step1Chunk0_3_checked, root4Node66Step1Chunk0_4_checked, root4Node66Step1Chunk0_5_checked, root4Node66Step1Chunk1_0_checked, root4Node66Step1Chunk1_1_checked, root4Node66Step1Chunk1_2_checked, root4Node66Step1Chunk1_3_checked, root4Node66Step1Chunk1_4_checked, root4Node66Step1Chunk1_5_checked, root4Node66Step1Chunk2_0_checked, root4Node66Step1Chunk2_1_checked, root4Node66Step1Chunk2_2_checked, root4Node66Step1Chunk2_3_checked, root4Node66Step1Chunk2_4_checked, root4Node66Step1Chunk2_5_checked, root4Node66Step1Chunk3_0_checked, root4Node66Step1Chunk3_1_checked, root4Node66Step1Chunk3_2_checked, root4Node66Step1Chunk3_3_checked, root4Node66Step1Chunk3_4_checked, root4Node66Step1Chunk3_5_checked, root4Node66Step1Chunk4_0_checked, root4Node66Step1Chunk4_1_checked, root4Node66Step1Chunk4_2_checked, root4Node66Step1Chunk4_3_checked, root4Node66Step1Chunk4_4_checked, root4Node66Step1Chunk4_5_checked, root4Node66Step1Chunk5_0_checked, root4Node66Step1Chunk5_1_checked, root4Node66Step1Chunk5_2_checked, root4Node66Step1Chunk5_3_checked, root4Node66Step1Chunk5_4_checked, root4Node66Step1Chunk5_5_checked, root4Node66Step1Chunk6_0_checked, root4Node66Step1Chunk6_1_checked, root4Node66Step1Chunk6_2_checked, root4Node66Step1Chunk6_3_checked, root4Node66Step1Chunk6_4_checked, root4Node66Step1Chunk6_5_checked, root4Node66Step1Chunk7_0_checked, root4Node66Step1Chunk7_1_checked, root4Node66Step1Chunk7_2_checked, root4Node66Step1Chunk7_3_checked, root4Node66Step1Chunk7_4_checked, root4Node66Step1Chunk7_5_checked, root4Node66Step1Chunk8_0_checked, root4Node66Step1Chunk8_1_checked, root4Node66Step1Chunk8_2_checked, root4Node66Step1Chunk8_3_checked, root4Node66Step1Chunk8_4_checked, root4Node66Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node66Step1_checked :
    checkReplacement table54 root4Node66Domains0 root4Node66Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node66Domains0 root4Node66Domains1
    root4Node66Domains0Fast root4Node66Domains1Fast
    root4Node66Domains0_fast_eq root4Node66Domains1_fast_eq
    root4Node66Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
