module

public import SpectreFinite.RadiusFiveRoot5Part5
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable12
public import SpectreFinite.RadiusFiveTable13
public import SpectreFinite.RadiusFiveTable2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node11Domains0 : Domains 91 State := restrict root5Node9Domains2 0 (1,4)
def root5Node11Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5),(6,2)]
  | 2 => some [(4,4),(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(2,0),(2,4),(4,4)]
  | 6 => some [(2,5),(4,5)]
  | 7 => some [(1,0),(6,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(3,1),(7,1)]
  | 12 => some [(0,1),(1,5),(6,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0),(7,0)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(0,0)]
  | 28 => some [(7,2)]
  | 29 => some [(4,0),(7,4)]
  | 30 => some [(4,5),(8,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1),(8,1)]
  | 39 => some [(0,1),(6,5)]
  | 40 => some [(0,0),(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(1,1),(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,0)]
  | 75 => some [(7,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(3,1)]
  | 82 => some [(0,1)]
  | 83 => some [(6,2)]
  | 84 => some [(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0)]
  | _ => some [(7,1)]
theorem root5Node11Domains0_fast_eq : root5Node11Domains0 = expandDomains root5Node11Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node11Domains0 v = expandDomains root5Node11Domains0Fast v from by decide) v
def root5Node11Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(2,0),(2,4),(4,4)]
  | 6 => [(2,5)]
  | 7 => [(6,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(6,0)]
  | 11 => [(3,1),(7,1)]
  | 12 => [(0,1),(1,5),(6,5)]
  | 13 => [(0,0)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(1,0),(7,0)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(0,0)]
  | 28 => [(7,2)]
  | 29 => [(4,0),(7,4)]
  | 30 => [(4,5)]
  | 31 => [(7,0)]
  | 32 => [(8,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1),(8,1)]
  | 39 => [(0,1),(6,5)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(7,0)]
  | 48 => [(8,3)]
  | 49 => [(8,5)]
  | 50 => [(1,0),(7,0)]
  | 51 => [(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
  | 62 => [(5,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5)]
  | 71 => [(4,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(2,0)]
  | 75 => [(7,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(3,1)]
  | 82 => [(0,1)]
  | 83 => [(6,2)]
  | 84 => [(8,4)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(1,0)]
  | _ => [(7,1)]
def root5Node11Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(4,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(2,0),(2,4),(4,4)]
  | 6 => some [(2,5)]
  | 7 => some [(6,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(3,1),(7,1)]
  | 12 => some [(0,1),(1,5),(6,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0),(7,0)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(0,0)]
  | 28 => some [(7,2)]
  | 29 => some [(4,0),(7,4)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1),(8,1)]
  | 39 => some [(0,1),(6,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,0)]
  | 75 => some [(7,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(3,1)]
  | 82 => some [(0,1)]
  | 83 => some [(6,2)]
  | 84 => some [(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0)]
  | _ => some [(7,1)]
theorem root5Node11Domains1_fast_eq : root5Node11Domains1 = expandDomains root5Node11Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node11Domains1 v = expandDomains root5Node11Domains1Fast v from by decide) v
theorem root5Node11Step1Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq (by decide)
theorem root5Node11Step1Narrowing_checked :
    checkNarrowing table13 root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkNarrowing_flatten table13Scope [table13Rows0_0,table13Rows0_1,table13Rows0_2,table13Rows0_3,table13Rows0_4,table13Rows0_5,table13Rows1_0,table13Rows1_1,table13Rows1_2,table13Rows1_3,table13Rows1_4,table13Rows1_5,table13Rows2_0,table13Rows2_1,table13Rows2_2,table13Rows2_3,table13Rows2_4,table13Rows2_5,table13Rows3_0,table13Rows3_1,table13Rows3_2,table13Rows3_3,table13Rows3_4,table13Rows3_5,table13Rows4_0,table13Rows4_1,table13Rows4_2,table13Rows4_3,table13Rows4_4,table13Rows4_5,table13Rows5_0,table13Rows5_1,table13Rows5_2,table13Rows5_3,table13Rows5_4,table13Rows5_5,table13Rows6_0,table13Rows6_1,table13Rows6_2,table13Rows6_3,table13Rows6_4,table13Rows6_5,table13Rows7_0,table13Rows7_1,table13Rows7_2,table13Rows7_3,table13Rows7_4,table13Rows7_5,table13Rows8_0,table13Rows8_1,table13Rows8_2,table13Rows8_3,table13Rows8_4,table13Rows8_5]
    root5Node11Domains0 root5Node11Domains1 (by
      simp only [List.all_cons, List.all_nil, root5Node11Step1Chunk0_0_checked, root5Node11Step1Chunk0_1_checked, root5Node11Step1Chunk0_2_checked, root5Node11Step1Chunk0_3_checked, root5Node11Step1Chunk0_4_checked, root5Node11Step1Chunk0_5_checked, root5Node11Step1Chunk1_0_checked, root5Node11Step1Chunk1_1_checked, root5Node11Step1Chunk1_2_checked, root5Node11Step1Chunk1_3_checked, root5Node11Step1Chunk1_4_checked, root5Node11Step1Chunk1_5_checked, root5Node11Step1Chunk2_0_checked, root5Node11Step1Chunk2_1_checked, root5Node11Step1Chunk2_2_checked, root5Node11Step1Chunk2_3_checked, root5Node11Step1Chunk2_4_checked, root5Node11Step1Chunk2_5_checked, root5Node11Step1Chunk3_0_checked, root5Node11Step1Chunk3_1_checked, root5Node11Step1Chunk3_2_checked, root5Node11Step1Chunk3_3_checked, root5Node11Step1Chunk3_4_checked, root5Node11Step1Chunk3_5_checked, root5Node11Step1Chunk4_0_checked, root5Node11Step1Chunk4_1_checked, root5Node11Step1Chunk4_2_checked, root5Node11Step1Chunk4_3_checked, root5Node11Step1Chunk4_4_checked, root5Node11Step1Chunk4_5_checked, root5Node11Step1Chunk5_0_checked, root5Node11Step1Chunk5_1_checked, root5Node11Step1Chunk5_2_checked, root5Node11Step1Chunk5_3_checked, root5Node11Step1Chunk5_4_checked, root5Node11Step1Chunk5_5_checked, root5Node11Step1Chunk6_0_checked, root5Node11Step1Chunk6_1_checked, root5Node11Step1Chunk6_2_checked, root5Node11Step1Chunk6_3_checked, root5Node11Step1Chunk6_4_checked, root5Node11Step1Chunk6_5_checked, root5Node11Step1Chunk7_0_checked, root5Node11Step1Chunk7_1_checked, root5Node11Step1Chunk7_2_checked, root5Node11Step1Chunk7_3_checked, root5Node11Step1Chunk7_4_checked, root5Node11Step1Chunk7_5_checked, root5Node11Step1Chunk8_0_checked, root5Node11Step1Chunk8_1_checked, root5Node11Step1Chunk8_2_checked, root5Node11Step1Chunk8_3_checked, root5Node11Step1Chunk8_4_checked, root5Node11Step1Chunk8_5_checked, Bool.true_and])
theorem root5Node11Step1_checked :
    checkReplacement table13 root5Node11Domains0 root5Node11Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root5Node11Domains0 root5Node11Domains1
    root5Node11Domains0Fast root5Node11Domains1Fast
    root5Node11Domains0_fast_eq root5Node11Domains1_fast_eq
    root5Node11Step1Narrowing_checked (by decide)
def root5Node12Domains0 : Domains 91 State := restrict root5Node11Domains1 11 (3,1)
def root5Node12Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(4,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(2,0),(2,4),(4,4)]
  | 6 => some [(2,5)]
  | 7 => some [(6,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(3,1)]
  | 12 => some [(0,1),(1,5),(6,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0),(7,0)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(0,0)]
  | 28 => some [(7,2)]
  | 29 => some [(4,0),(7,4)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1),(8,1)]
  | 39 => some [(0,1),(6,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,0)]
  | 75 => some [(7,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(3,1)]
  | 82 => some [(0,1)]
  | 83 => some [(6,2)]
  | 84 => some [(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0)]
  | _ => some [(7,1)]
theorem root5Node12Domains0_fast_eq : root5Node12Domains0 = expandDomains root5Node12Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node12Domains0 v = expandDomains root5Node12Domains0Fast v from by decide) v
def root5Node12Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(2,0)]
  | 6 => [(2,5)]
  | 7 => [(6,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(6,0)]
  | 11 => [(3,1)]
  | 12 => [(0,1)]
  | 13 => [(0,0)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(1,0)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(0,0)]
  | 28 => [(7,2)]
  | 29 => [(4,0)]
  | 30 => [(4,5)]
  | 31 => [(7,0)]
  | 32 => [(8,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(7,0)]
  | 48 => [(8,3)]
  | 49 => [(8,5)]
  | 50 => [(1,0)]
  | 51 => [(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
  | 62 => [(5,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5)]
  | 71 => [(4,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(2,0)]
  | 75 => [(7,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(3,1)]
  | 82 => [(0,1)]
  | 83 => [(6,2)]
  | 84 => [(8,4)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(1,0)]
  | _ => [(7,1)]
def root5Node12Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(4,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(2,0)]
  | 6 => some [(2,5)]
  | 7 => some [(6,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(3,1)]
  | 12 => some [(0,1)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(0,0)]
  | 28 => some [(7,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,0)]
  | 75 => some [(7,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(3,1)]
  | 82 => some [(0,1)]
  | 83 => some [(6,2)]
  | 84 => some [(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0)]
  | _ => some [(7,1)]
theorem root5Node12Domains1_fast_eq : root5Node12Domains1 = expandDomains root5Node12Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node12Domains1 v = expandDomains root5Node12Domains1Fast v from by decide) v
theorem root5Node12Step1Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Narrowing_checked :
    checkNarrowing table12 root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_flatten table12Scope [table12Rows0_0,table12Rows0_1,table12Rows0_2,table12Rows0_3,table12Rows0_4,table12Rows0_5,table12Rows1_0,table12Rows1_1,table12Rows1_2,table12Rows1_3,table12Rows1_4,table12Rows1_5,table12Rows2_0,table12Rows2_1,table12Rows2_2,table12Rows2_3,table12Rows2_4,table12Rows2_5,table12Rows3_0,table12Rows3_1,table12Rows3_2,table12Rows3_3,table12Rows3_4,table12Rows3_5,table12Rows4_0,table12Rows4_1,table12Rows4_2,table12Rows4_3,table12Rows4_4,table12Rows4_5,table12Rows5_0,table12Rows5_1,table12Rows5_2,table12Rows5_3,table12Rows5_4,table12Rows5_5,table12Rows6_0,table12Rows6_1,table12Rows6_2,table12Rows6_3,table12Rows6_4,table12Rows6_5,table12Rows7_0,table12Rows7_1,table12Rows7_2,table12Rows7_3,table12Rows7_4,table12Rows7_5,table12Rows8_0,table12Rows8_1,table12Rows8_2,table12Rows8_3,table12Rows8_4,table12Rows8_5]
    root5Node12Domains0 root5Node12Domains1 (by
      simp only [List.all_cons, List.all_nil, root5Node12Step1Chunk0_0_checked, root5Node12Step1Chunk0_1_checked, root5Node12Step1Chunk0_2_checked, root5Node12Step1Chunk0_3_checked, root5Node12Step1Chunk0_4_checked, root5Node12Step1Chunk0_5_checked, root5Node12Step1Chunk1_0_checked, root5Node12Step1Chunk1_1_checked, root5Node12Step1Chunk1_2_checked, root5Node12Step1Chunk1_3_checked, root5Node12Step1Chunk1_4_checked, root5Node12Step1Chunk1_5_checked, root5Node12Step1Chunk2_0_checked, root5Node12Step1Chunk2_1_checked, root5Node12Step1Chunk2_2_checked, root5Node12Step1Chunk2_3_checked, root5Node12Step1Chunk2_4_checked, root5Node12Step1Chunk2_5_checked, root5Node12Step1Chunk3_0_checked, root5Node12Step1Chunk3_1_checked, root5Node12Step1Chunk3_2_checked, root5Node12Step1Chunk3_3_checked, root5Node12Step1Chunk3_4_checked, root5Node12Step1Chunk3_5_checked, root5Node12Step1Chunk4_0_checked, root5Node12Step1Chunk4_1_checked, root5Node12Step1Chunk4_2_checked, root5Node12Step1Chunk4_3_checked, root5Node12Step1Chunk4_4_checked, root5Node12Step1Chunk4_5_checked, root5Node12Step1Chunk5_0_checked, root5Node12Step1Chunk5_1_checked, root5Node12Step1Chunk5_2_checked, root5Node12Step1Chunk5_3_checked, root5Node12Step1Chunk5_4_checked, root5Node12Step1Chunk5_5_checked, root5Node12Step1Chunk6_0_checked, root5Node12Step1Chunk6_1_checked, root5Node12Step1Chunk6_2_checked, root5Node12Step1Chunk6_3_checked, root5Node12Step1Chunk6_4_checked, root5Node12Step1Chunk6_5_checked, root5Node12Step1Chunk7_0_checked, root5Node12Step1Chunk7_1_checked, root5Node12Step1Chunk7_2_checked, root5Node12Step1Chunk7_3_checked, root5Node12Step1Chunk7_4_checked, root5Node12Step1Chunk7_5_checked, root5Node12Step1Chunk8_0_checked, root5Node12Step1Chunk8_1_checked, root5Node12Step1Chunk8_2_checked, root5Node12Step1Chunk8_3_checked, root5Node12Step1Chunk8_4_checked, root5Node12Step1Chunk8_5_checked, Bool.true_and])
theorem root5Node12Step1_checked :
    checkReplacement table12 root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq
    root5Node12Step1Narrowing_checked (by decide)
theorem root5Node12Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node12Domains1 (.output 5) = true := by decide
def root5Node13Domains0 : Domains 91 State := restrict root5Node11Domains1 11 (7,1)
def root5Node13Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(4,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(2,0),(2,4),(4,4)]
  | 6 => some [(2,5)]
  | 7 => some [(6,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(0,1),(1,5),(6,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0),(7,0)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(0,0)]
  | 28 => some [(7,2)]
  | 29 => some [(4,0),(7,4)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1),(8,1)]
  | 39 => some [(0,1),(6,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,0)]
  | 75 => some [(7,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(3,1)]
  | 82 => some [(0,1)]
  | 83 => some [(6,2)]
  | 84 => some [(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0)]
  | _ => some [(7,1)]
theorem root5Node13Domains0_fast_eq : root5Node13Domains0 = expandDomains root5Node13Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node13Domains0 v = expandDomains root5Node13Domains0Fast v from by decide) v
def root5Node13Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(2,4),(4,4)]
  | 6 => [(2,5)]
  | 7 => [(6,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(6,0)]
  | 11 => [(7,1)]
  | 12 => [(1,5),(6,5)]
  | 13 => [(0,0)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(7,0)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(0,0)]
  | 28 => [(7,2)]
  | 29 => [(7,4)]
  | 30 => [(4,5)]
  | 31 => [(7,0)]
  | 32 => [(8,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(8,1)]
  | 39 => [(6,5)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(7,0)]
  | 48 => [(8,3)]
  | 49 => [(8,5)]
  | 50 => [(7,0)]
  | 51 => [(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
  | 62 => [(5,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5)]
  | 71 => [(4,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(2,0)]
  | 75 => [(7,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(3,1)]
  | 82 => [(0,1)]
  | 83 => [(6,2)]
  | 84 => [(8,4)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(1,0)]
  | _ => [(7,1)]
def root5Node13Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(4,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(2,4),(4,4)]
  | 6 => some [(2,5)]
  | 7 => some [(6,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(1,5),(6,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(7,0)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(0,0)]
  | 28 => some [(7,2)]
  | 29 => some [(7,4)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(8,1)]
  | 39 => some [(6,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,0)]
  | 75 => some [(7,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(3,1)]
  | 82 => some [(0,1)]
  | 83 => some [(6,2)]
  | 84 => some [(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0)]
  | _ => some [(7,1)]
theorem root5Node13Domains1_fast_eq : root5Node13Domains1 = expandDomains root5Node13Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node13Domains1 v = expandDomains root5Node13Domains1Fast v from by decide) v
theorem root5Node13Step1Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Narrowing_checked :
    checkNarrowing table12 root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_flatten table12Scope [table12Rows0_0,table12Rows0_1,table12Rows0_2,table12Rows0_3,table12Rows0_4,table12Rows0_5,table12Rows1_0,table12Rows1_1,table12Rows1_2,table12Rows1_3,table12Rows1_4,table12Rows1_5,table12Rows2_0,table12Rows2_1,table12Rows2_2,table12Rows2_3,table12Rows2_4,table12Rows2_5,table12Rows3_0,table12Rows3_1,table12Rows3_2,table12Rows3_3,table12Rows3_4,table12Rows3_5,table12Rows4_0,table12Rows4_1,table12Rows4_2,table12Rows4_3,table12Rows4_4,table12Rows4_5,table12Rows5_0,table12Rows5_1,table12Rows5_2,table12Rows5_3,table12Rows5_4,table12Rows5_5,table12Rows6_0,table12Rows6_1,table12Rows6_2,table12Rows6_3,table12Rows6_4,table12Rows6_5,table12Rows7_0,table12Rows7_1,table12Rows7_2,table12Rows7_3,table12Rows7_4,table12Rows7_5,table12Rows8_0,table12Rows8_1,table12Rows8_2,table12Rows8_3,table12Rows8_4,table12Rows8_5]
    root5Node13Domains0 root5Node13Domains1 (by
      simp only [List.all_cons, List.all_nil, root5Node13Step1Chunk0_0_checked, root5Node13Step1Chunk0_1_checked, root5Node13Step1Chunk0_2_checked, root5Node13Step1Chunk0_3_checked, root5Node13Step1Chunk0_4_checked, root5Node13Step1Chunk0_5_checked, root5Node13Step1Chunk1_0_checked, root5Node13Step1Chunk1_1_checked, root5Node13Step1Chunk1_2_checked, root5Node13Step1Chunk1_3_checked, root5Node13Step1Chunk1_4_checked, root5Node13Step1Chunk1_5_checked, root5Node13Step1Chunk2_0_checked, root5Node13Step1Chunk2_1_checked, root5Node13Step1Chunk2_2_checked, root5Node13Step1Chunk2_3_checked, root5Node13Step1Chunk2_4_checked, root5Node13Step1Chunk2_5_checked, root5Node13Step1Chunk3_0_checked, root5Node13Step1Chunk3_1_checked, root5Node13Step1Chunk3_2_checked, root5Node13Step1Chunk3_3_checked, root5Node13Step1Chunk3_4_checked, root5Node13Step1Chunk3_5_checked, root5Node13Step1Chunk4_0_checked, root5Node13Step1Chunk4_1_checked, root5Node13Step1Chunk4_2_checked, root5Node13Step1Chunk4_3_checked, root5Node13Step1Chunk4_4_checked, root5Node13Step1Chunk4_5_checked, root5Node13Step1Chunk5_0_checked, root5Node13Step1Chunk5_1_checked, root5Node13Step1Chunk5_2_checked, root5Node13Step1Chunk5_3_checked, root5Node13Step1Chunk5_4_checked, root5Node13Step1Chunk5_5_checked, root5Node13Step1Chunk6_0_checked, root5Node13Step1Chunk6_1_checked, root5Node13Step1Chunk6_2_checked, root5Node13Step1Chunk6_3_checked, root5Node13Step1Chunk6_4_checked, root5Node13Step1Chunk6_5_checked, root5Node13Step1Chunk7_0_checked, root5Node13Step1Chunk7_1_checked, root5Node13Step1Chunk7_2_checked, root5Node13Step1Chunk7_3_checked, root5Node13Step1Chunk7_4_checked, root5Node13Step1Chunk7_5_checked, root5Node13Step1Chunk8_0_checked, root5Node13Step1Chunk8_1_checked, root5Node13Step1Chunk8_2_checked, root5Node13Step1Chunk8_3_checked, root5Node13Step1Chunk8_4_checked, root5Node13Step1Chunk8_5_checked, Bool.true_and])
theorem root5Node13Step1_checked :
    checkReplacement table12 root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq
    root5Node13Step1Narrowing_checked (by decide)
def root5Node14Domains0 : Domains 91 State := restrict root5Node13Domains1 5 (2,4)
def root5Node14Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(4,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(2,4)]
  | 6 => some [(2,5)]
  | 7 => some [(6,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(1,5),(6,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(7,0)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(0,0)]
  | 28 => some [(7,2)]
  | 29 => some [(7,4)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(8,1)]
  | 39 => some [(6,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,0)]
  | 75 => some [(7,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(3,1)]
  | 82 => some [(0,1)]
  | 83 => some [(6,2)]
  | 84 => some [(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0)]
  | _ => some [(7,1)]
theorem root5Node14Domains0_fast_eq : root5Node14Domains0 = expandDomains root5Node14Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node14Domains0 v = expandDomains root5Node14Domains0Fast v from by decide) v
def root5Node14Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(2,4)]
  | 6 => [(2,5)]
  | 7 => [(6,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(6,0)]
  | 11 => [(7,1)]
  | 12 => [(6,5)]
  | 13 => [(0,0)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(7,0)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(0,0)]
  | 28 => [(7,2)]
  | 29 => [(7,4)]
  | 30 => [(4,5)]
  | 31 => [(7,0)]
  | 32 => [(8,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(8,1)]
  | 39 => [(6,5)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(7,0)]
  | 48 => [(8,3)]
  | 49 => [(8,5)]
  | 50 => [(7,0)]
  | 51 => [(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
  | 62 => [(5,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5)]
  | 71 => [(4,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(2,0)]
  | 75 => [(7,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(3,1)]
  | 82 => [(0,1)]
  | 83 => [(6,2)]
  | 84 => [(8,4)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(1,0)]
  | _ => [(7,1)]
def root5Node14Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(4,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(2,4)]
  | 6 => some [(2,5)]
  | 7 => some [(6,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(6,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(7,0)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(0,0)]
  | 28 => some [(7,2)]
  | 29 => some [(7,4)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(8,1)]
  | 39 => some [(6,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,0)]
  | 75 => some [(7,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(3,1)]
  | 82 => some [(0,1)]
  | 83 => some [(6,2)]
  | 84 => some [(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0)]
  | _ => some [(7,1)]
theorem root5Node14Domains1_fast_eq : root5Node14Domains1 = expandDomains root5Node14Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node14Domains1 v = expandDomains root5Node14Domains1Fast v from by decide) v
theorem root5Node14Step1Chunk0_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk0_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk0_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk0_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk0_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk0_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk1_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk1_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk1_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk1_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk1_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk1_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk2_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk2_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk2_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk2_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk2_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk2_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk3_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk3_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk3_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk3_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk3_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk3_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk4_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk4_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk4_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk4_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk4_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk4_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk5_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk5_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk5_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk5_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk5_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk5_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk6_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk6_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk6_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk6_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk6_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk6_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk7_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk7_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk7_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk7_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk7_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk7_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk8_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk8_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk8_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk8_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk8_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk8_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Narrowing_checked :
    checkNarrowing table2 root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_flatten table2Scope [table2Rows0_0,table2Rows0_1,table2Rows0_2,table2Rows0_3,table2Rows0_4,table2Rows0_5,table2Rows1_0,table2Rows1_1,table2Rows1_2,table2Rows1_3,table2Rows1_4,table2Rows1_5,table2Rows2_0,table2Rows2_1,table2Rows2_2,table2Rows2_3,table2Rows2_4,table2Rows2_5,table2Rows3_0,table2Rows3_1,table2Rows3_2,table2Rows3_3,table2Rows3_4,table2Rows3_5,table2Rows4_0,table2Rows4_1,table2Rows4_2,table2Rows4_3,table2Rows4_4,table2Rows4_5,table2Rows5_0,table2Rows5_1,table2Rows5_2,table2Rows5_3,table2Rows5_4,table2Rows5_5,table2Rows6_0,table2Rows6_1,table2Rows6_2,table2Rows6_3,table2Rows6_4,table2Rows6_5,table2Rows7_0,table2Rows7_1,table2Rows7_2,table2Rows7_3,table2Rows7_4,table2Rows7_5,table2Rows8_0,table2Rows8_1,table2Rows8_2,table2Rows8_3,table2Rows8_4,table2Rows8_5]
    root5Node14Domains0 root5Node14Domains1 (by
      simp only [List.all_cons, List.all_nil, root5Node14Step1Chunk0_0_checked, root5Node14Step1Chunk0_1_checked, root5Node14Step1Chunk0_2_checked, root5Node14Step1Chunk0_3_checked, root5Node14Step1Chunk0_4_checked, root5Node14Step1Chunk0_5_checked, root5Node14Step1Chunk1_0_checked, root5Node14Step1Chunk1_1_checked, root5Node14Step1Chunk1_2_checked, root5Node14Step1Chunk1_3_checked, root5Node14Step1Chunk1_4_checked, root5Node14Step1Chunk1_5_checked, root5Node14Step1Chunk2_0_checked, root5Node14Step1Chunk2_1_checked, root5Node14Step1Chunk2_2_checked, root5Node14Step1Chunk2_3_checked, root5Node14Step1Chunk2_4_checked, root5Node14Step1Chunk2_5_checked, root5Node14Step1Chunk3_0_checked, root5Node14Step1Chunk3_1_checked, root5Node14Step1Chunk3_2_checked, root5Node14Step1Chunk3_3_checked, root5Node14Step1Chunk3_4_checked, root5Node14Step1Chunk3_5_checked, root5Node14Step1Chunk4_0_checked, root5Node14Step1Chunk4_1_checked, root5Node14Step1Chunk4_2_checked, root5Node14Step1Chunk4_3_checked, root5Node14Step1Chunk4_4_checked, root5Node14Step1Chunk4_5_checked, root5Node14Step1Chunk5_0_checked, root5Node14Step1Chunk5_1_checked, root5Node14Step1Chunk5_2_checked, root5Node14Step1Chunk5_3_checked, root5Node14Step1Chunk5_4_checked, root5Node14Step1Chunk5_5_checked, root5Node14Step1Chunk6_0_checked, root5Node14Step1Chunk6_1_checked, root5Node14Step1Chunk6_2_checked, root5Node14Step1Chunk6_3_checked, root5Node14Step1Chunk6_4_checked, root5Node14Step1Chunk6_5_checked, root5Node14Step1Chunk7_0_checked, root5Node14Step1Chunk7_1_checked, root5Node14Step1Chunk7_2_checked, root5Node14Step1Chunk7_3_checked, root5Node14Step1Chunk7_4_checked, root5Node14Step1Chunk7_5_checked, root5Node14Step1Chunk8_0_checked, root5Node14Step1Chunk8_1_checked, root5Node14Step1Chunk8_2_checked, root5Node14Step1Chunk8_3_checked, root5Node14Step1Chunk8_4_checked, root5Node14Step1Chunk8_5_checked, Bool.true_and])
theorem root5Node14Step1_checked :
    checkReplacement table2 root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq
    root5Node14Step1Narrowing_checked (by decide)
theorem root5Node14Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node14Domains1 (.output 6) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
