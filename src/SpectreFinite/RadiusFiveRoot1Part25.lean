module

public import SpectreFinite.RadiusFiveRoot1Part24
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable12
public import SpectreFinite.RadiusFiveTable35
public import SpectreFinite.RadiusFiveTable65

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node60Domains0 : Domains 91 State := restrict root1Node59Domains4 4 (4,3)
def root1Node60Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(1,5),(3,5),(5,5)]
  | 6 => some [(0,4)]
  | 7 => some [(1,4)]
  | 8 => some [(0,5)]
  | 9 => some [(4,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(2,0),(2,4),(4,4)]
  | 13 => some [(3,0)]
  | 14 => some [(2,5)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(3,1),(7,1)]
  | 20 => some [(0,1),(1,5),(6,5),(7,5)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3)]
  | 29 => some [(1,0),(4,2),(7,0),(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(4,0),(7,4),(8,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5),(7,5)]
  | 48 => some [(0,3),(6,1)]
  | 49 => some [(5,1),(8,1)]
  | 50 => some [(0,1),(1,5),(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(4,0),(5,0),(8,0)]
  | 57 => some [(4,5),(7,3)]
  | 58 => some [(4,2),(7,0)]
  | 59 => some [(5,3),(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(4,1),(8,1)]
  | 63 => some [(0,2),(6,5)]
  | 64 => some [(0,4),(1,1)]
  | 65 => some [(5,1),(5,4)]
  | 66 => some [(0,0),(0,1),(6,4)]
  | 67 => some [(1,2),(6,2),(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(7,3),(8,3)]
  | 71 => some [(5,2),(5,5),(8,5)]
  | 72 => some [(7,0),(8,0)]
  | 73 => some [(4,3),(8,3)]
  | 74 => some [(1,5),(3,5),(5,5),(7,5)]
  | 75 => some [(0,3),(1,0),(6,1)]
  | 76 => some [(2,1),(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5),(6,2),(6,3)]
  | 79 => some [(4,4),(7,2),(8,4)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(6,3)]
  | 82 => some [(2,0),(2,2),(2,4),(4,4)]
  | 83 => some [(0,0),(1,3),(3,3),(7,3)]
  | 84 => some [(3,2),(5,2)]
  | 85 => some [(1,1),(7,1)]
  | 86 => some [(4,1),(7,5)]
  | 87 => some [(0,2),(6,0)]
  | 88 => some [(1,1),(3,1),(7,1)]
  | 89 => some [(0,1),(1,5),(6,5)]
  | _ => some [(0,4),(6,1),(6,2)]
theorem root1Node60Domains0_fast_eq : root1Node60Domains0 = expandDomains root1Node60Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node60Domains0 v = expandDomains root1Node60Domains0Fast v from by decide) v
def root1Node60Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(5,5)]
  | 3 => [(7,0)]
  | 4 => [(4,3)]
  | 5 => [(1,5),(3,5)]
  | 6 => [(0,4)]
  | 7 => [(1,4)]
  | 8 => [(0,5)]
  | 9 => [(4,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(2,0),(2,4)]
  | 13 => [(3,0)]
  | 14 => [(2,5)]
  | 15 => [(6,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(3,1),(7,1)]
  | 20 => [(0,1),(6,5)]
  | 21 => [(4,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(8,2)]
  | 27 => [(5,0)]
  | 28 => [(4,5)]
  | 29 => [(1,0),(7,0)]
  | 30 => [(7,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0),(7,4)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(1,5)]
  | 48 => [(6,1)]
  | 49 => [(5,1),(8,1)]
  | 50 => [(0,1),(1,5),(6,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(7,0)]
  | 59 => [(8,3)]
  | 60 => [(8,5)]
  | 61 => [(6,1)]
  | 62 => [(4,1),(8,1)]
  | 63 => [(6,5)]
  | 64 => [(0,4)]
  | 65 => [(5,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(7,4)]
  | 69 => [(6,3)]
  | 70 => [(7,3),(8,3)]
  | 71 => [(5,2),(5,5),(8,5)]
  | 72 => [(7,0)]
  | 73 => [(4,3)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(4,1)]
  | 77 => [(0,2)]
  | 78 => [(0,5),(6,2),(6,3)]
  | 79 => [(4,4),(7,2),(8,4)]
  | 80 => [(1,4),(7,4)]
  | 81 => [(0,5),(6,3)]
  | 82 => [(2,0),(2,2),(2,4),(4,4)]
  | 83 => [(0,0),(1,3),(3,3),(7,3)]
  | 84 => [(3,2),(5,2)]
  | 85 => [(1,1),(7,1)]
  | 86 => [(4,1),(7,5)]
  | 87 => [(0,2),(6,0)]
  | 88 => [(1,1),(3,1),(7,1)]
  | 89 => [(0,1),(1,5),(6,5)]
  | _ => [(0,4),(6,1),(6,2)]
def root1Node60Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(1,5),(3,5)]
  | 6 => some [(0,4)]
  | 7 => some [(1,4)]
  | 8 => some [(0,5)]
  | 9 => some [(4,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(2,0),(2,4)]
  | 13 => some [(3,0)]
  | 14 => some [(2,5)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(3,1),(7,1)]
  | 20 => some [(0,1),(6,5)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0)]
  | 28 => some [(4,5)]
  | 29 => some [(1,0),(7,0)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0),(7,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(5,1),(8,1)]
  | 50 => some [(0,1),(1,5),(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(4,1),(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(7,3),(8,3)]
  | 71 => some [(5,2),(5,5),(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5),(6,2),(6,3)]
  | 79 => some [(4,4),(7,2),(8,4)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(6,3)]
  | 82 => some [(2,0),(2,2),(2,4),(4,4)]
  | 83 => some [(0,0),(1,3),(3,3),(7,3)]
  | 84 => some [(3,2),(5,2)]
  | 85 => some [(1,1),(7,1)]
  | 86 => some [(4,1),(7,5)]
  | 87 => some [(0,2),(6,0)]
  | 88 => some [(1,1),(3,1),(7,1)]
  | 89 => some [(0,1),(1,5),(6,5)]
  | _ => some [(0,4),(6,1),(6,2)]
theorem root1Node60Domains1_fast_eq : root1Node60Domains1 = expandDomains root1Node60Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node60Domains1 v = expandDomains root1Node60Domains1Fast v from by decide) v
theorem root1Node60Step1Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq (by decide)
theorem root1Node60Step1Narrowing_checked :
    checkNarrowing table35 root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkNarrowing_flatten table35Scope [table35Rows0_0,table35Rows0_1,table35Rows0_2,table35Rows0_3,table35Rows0_4,table35Rows0_5,table35Rows1_0,table35Rows1_1,table35Rows1_2,table35Rows1_3,table35Rows1_4,table35Rows1_5,table35Rows2_0,table35Rows2_1,table35Rows2_2,table35Rows2_3,table35Rows2_4,table35Rows2_5,table35Rows3_0,table35Rows3_1,table35Rows3_2,table35Rows3_3,table35Rows3_4,table35Rows3_5,table35Rows4_0,table35Rows4_1,table35Rows4_2,table35Rows4_3,table35Rows4_4,table35Rows4_5,table35Rows5_0,table35Rows5_1,table35Rows5_2,table35Rows5_3,table35Rows5_4,table35Rows5_5,table35Rows6_0,table35Rows6_1,table35Rows6_2,table35Rows6_3,table35Rows6_4,table35Rows6_5,table35Rows7_0,table35Rows7_1,table35Rows7_2,table35Rows7_3,table35Rows7_4,table35Rows7_5,table35Rows8_0,table35Rows8_1,table35Rows8_2,table35Rows8_3,table35Rows8_4,table35Rows8_5]
    root1Node60Domains0 root1Node60Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node60Step1Chunk0_0_checked, root1Node60Step1Chunk0_1_checked, root1Node60Step1Chunk0_2_checked, root1Node60Step1Chunk0_3_checked, root1Node60Step1Chunk0_4_checked, root1Node60Step1Chunk0_5_checked, root1Node60Step1Chunk1_0_checked, root1Node60Step1Chunk1_1_checked, root1Node60Step1Chunk1_2_checked, root1Node60Step1Chunk1_3_checked, root1Node60Step1Chunk1_4_checked, root1Node60Step1Chunk1_5_checked, root1Node60Step1Chunk2_0_checked, root1Node60Step1Chunk2_1_checked, root1Node60Step1Chunk2_2_checked, root1Node60Step1Chunk2_3_checked, root1Node60Step1Chunk2_4_checked, root1Node60Step1Chunk2_5_checked, root1Node60Step1Chunk3_0_checked, root1Node60Step1Chunk3_1_checked, root1Node60Step1Chunk3_2_checked, root1Node60Step1Chunk3_3_checked, root1Node60Step1Chunk3_4_checked, root1Node60Step1Chunk3_5_checked, root1Node60Step1Chunk4_0_checked, root1Node60Step1Chunk4_1_checked, root1Node60Step1Chunk4_2_checked, root1Node60Step1Chunk4_3_checked, root1Node60Step1Chunk4_4_checked, root1Node60Step1Chunk4_5_checked, root1Node60Step1Chunk5_0_checked, root1Node60Step1Chunk5_1_checked, root1Node60Step1Chunk5_2_checked, root1Node60Step1Chunk5_3_checked, root1Node60Step1Chunk5_4_checked, root1Node60Step1Chunk5_5_checked, root1Node60Step1Chunk6_0_checked, root1Node60Step1Chunk6_1_checked, root1Node60Step1Chunk6_2_checked, root1Node60Step1Chunk6_3_checked, root1Node60Step1Chunk6_4_checked, root1Node60Step1Chunk6_5_checked, root1Node60Step1Chunk7_0_checked, root1Node60Step1Chunk7_1_checked, root1Node60Step1Chunk7_2_checked, root1Node60Step1Chunk7_3_checked, root1Node60Step1Chunk7_4_checked, root1Node60Step1Chunk7_5_checked, root1Node60Step1Chunk8_0_checked, root1Node60Step1Chunk8_1_checked, root1Node60Step1Chunk8_2_checked, root1Node60Step1Chunk8_3_checked, root1Node60Step1Chunk8_4_checked, root1Node60Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node60Step1_checked :
    checkReplacement table35 root1Node60Domains0 root1Node60Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node60Domains0 root1Node60Domains1
    root1Node60Domains0Fast root1Node60Domains1Fast
    root1Node60Domains0_fast_eq root1Node60Domains1_fast_eq
    root1Node60Step1Narrowing_checked (by decide)
def root1Node60Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(5,5)]
  | 3 => [(7,0)]
  | 4 => [(4,3)]
  | 5 => [(1,5),(3,5)]
  | 6 => [(0,4)]
  | 7 => [(1,4)]
  | 8 => [(0,5)]
  | 9 => [(4,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(2,0),(2,4)]
  | 13 => [(3,0)]
  | 14 => [(2,5)]
  | 15 => [(6,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(3,1),(7,1)]
  | 20 => [(0,1),(6,5)]
  | 21 => [(4,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(8,2)]
  | 27 => [(5,0)]
  | 28 => [(4,5)]
  | 29 => [(1,0),(7,0)]
  | 30 => [(7,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0),(7,4)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(1,5)]
  | 48 => [(6,1)]
  | 49 => [(5,1),(8,1)]
  | 50 => [(0,1),(1,5),(6,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(7,0)]
  | 59 => [(8,3)]
  | 60 => [(8,5)]
  | 61 => [(6,1)]
  | 62 => [(8,1)]
  | 63 => [(6,5)]
  | 64 => [(0,4)]
  | 65 => [(5,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(7,4)]
  | 69 => [(6,3)]
  | 70 => [(8,3)]
  | 71 => [(5,5)]
  | 72 => [(7,0)]
  | 73 => [(4,3)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(4,1)]
  | 77 => [(0,2)]
  | 78 => [(0,5)]
  | 79 => [(4,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(2,0)]
  | 83 => [(7,3)]
  | 84 => [(5,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(3,1)]
  | 89 => [(0,1)]
  | _ => [(6,2)]
def root1Node60Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(1,5),(3,5)]
  | 6 => some [(0,4)]
  | 7 => some [(1,4)]
  | 8 => some [(0,5)]
  | 9 => some [(4,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(2,0),(2,4)]
  | 13 => some [(3,0)]
  | 14 => some [(2,5)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(3,1),(7,1)]
  | 20 => some [(0,1),(6,5)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0)]
  | 28 => some [(4,5)]
  | 29 => some [(1,0),(7,0)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0),(7,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(5,1),(8,1)]
  | 50 => some [(0,1),(1,5),(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(8,3)]
  | 71 => some [(5,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5)]
  | 79 => some [(4,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(2,0)]
  | 83 => some [(7,3)]
  | 84 => some [(5,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(3,1)]
  | 89 => some [(0,1)]
  | _ => some [(6,2)]
theorem root1Node60Domains2_fast_eq : root1Node60Domains2 = expandDomains root1Node60Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node60Domains2 v = expandDomains root1Node60Domains2Fast v from by decide) v
theorem root1Node60Step2Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq (by decide)
theorem root1Node60Step2Narrowing_checked :
    checkNarrowing table65 root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root1Node60Domains1 root1Node60Domains2 (by
      simp only [List.all_cons, List.all_nil, root1Node60Step2Chunk0_0_checked, root1Node60Step2Chunk0_1_checked, root1Node60Step2Chunk0_2_checked, root1Node60Step2Chunk0_3_checked, root1Node60Step2Chunk0_4_checked, root1Node60Step2Chunk0_5_checked, root1Node60Step2Chunk1_0_checked, root1Node60Step2Chunk1_1_checked, root1Node60Step2Chunk1_2_checked, root1Node60Step2Chunk1_3_checked, root1Node60Step2Chunk1_4_checked, root1Node60Step2Chunk1_5_checked, root1Node60Step2Chunk2_0_checked, root1Node60Step2Chunk2_1_checked, root1Node60Step2Chunk2_2_checked, root1Node60Step2Chunk2_3_checked, root1Node60Step2Chunk2_4_checked, root1Node60Step2Chunk2_5_checked, root1Node60Step2Chunk3_0_checked, root1Node60Step2Chunk3_1_checked, root1Node60Step2Chunk3_2_checked, root1Node60Step2Chunk3_3_checked, root1Node60Step2Chunk3_4_checked, root1Node60Step2Chunk3_5_checked, root1Node60Step2Chunk4_0_checked, root1Node60Step2Chunk4_1_checked, root1Node60Step2Chunk4_2_checked, root1Node60Step2Chunk4_3_checked, root1Node60Step2Chunk4_4_checked, root1Node60Step2Chunk4_5_checked, root1Node60Step2Chunk5_0_checked, root1Node60Step2Chunk5_1_checked, root1Node60Step2Chunk5_2_checked, root1Node60Step2Chunk5_3_checked, root1Node60Step2Chunk5_4_checked, root1Node60Step2Chunk5_5_checked, root1Node60Step2Chunk6_0_checked, root1Node60Step2Chunk6_1_checked, root1Node60Step2Chunk6_2_checked, root1Node60Step2Chunk6_3_checked, root1Node60Step2Chunk6_4_checked, root1Node60Step2Chunk6_5_checked, root1Node60Step2Chunk7_0_checked, root1Node60Step2Chunk7_1_checked, root1Node60Step2Chunk7_2_checked, root1Node60Step2Chunk7_3_checked, root1Node60Step2Chunk7_4_checked, root1Node60Step2Chunk7_5_checked, root1Node60Step2Chunk8_0_checked, root1Node60Step2Chunk8_1_checked, root1Node60Step2Chunk8_2_checked, root1Node60Step2Chunk8_3_checked, root1Node60Step2Chunk8_4_checked, root1Node60Step2Chunk8_5_checked, Bool.true_and])
theorem root1Node60Step2_checked :
    checkReplacement table65 root1Node60Domains1 root1Node60Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root1Node60Domains1 root1Node60Domains2
    root1Node60Domains1Fast root1Node60Domains2Fast
    root1Node60Domains1_fast_eq root1Node60Domains2_fast_eq
    root1Node60Step2Narrowing_checked (by decide)
def root1Node60Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(5,5)]
  | 3 => [(7,0)]
  | 4 => [(4,3)]
  | 5 => [(1,5),(3,5)]
  | 6 => [(0,4)]
  | 7 => [(1,4)]
  | 8 => [(0,5)]
  | 9 => [(4,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(2,0),(2,4)]
  | 13 => [(3,0)]
  | 14 => [(2,5)]
  | 15 => [(6,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(3,1),(7,1)]
  | 20 => [(0,1),(6,5)]
  | 21 => [(4,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(8,2)]
  | 27 => [(5,0)]
  | 28 => [(4,5)]
  | 29 => [(1,0),(7,0)]
  | 30 => [(7,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0),(7,4)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(1,5)]
  | 48 => [(6,1)]
  | 49 => [(5,1),(8,1)]
  | 50 => [(0,1),(6,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(7,0)]
  | 59 => [(8,3)]
  | 60 => [(8,5)]
  | 61 => [(6,1)]
  | 62 => [(8,1)]
  | 63 => [(6,5)]
  | 64 => [(0,4)]
  | 65 => [(5,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(7,4)]
  | 69 => [(6,3)]
  | 70 => [(8,3)]
  | 71 => [(5,5)]
  | 72 => [(7,0)]
  | 73 => [(4,3)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(4,1)]
  | 77 => [(0,2)]
  | 78 => [(0,5)]
  | 79 => [(4,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(2,0)]
  | 83 => [(7,3)]
  | 84 => [(5,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(3,1)]
  | 89 => [(0,1)]
  | _ => [(6,2)]
def root1Node60Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(1,5),(3,5)]
  | 6 => some [(0,4)]
  | 7 => some [(1,4)]
  | 8 => some [(0,5)]
  | 9 => some [(4,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(2,0),(2,4)]
  | 13 => some [(3,0)]
  | 14 => some [(2,5)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(3,1),(7,1)]
  | 20 => some [(0,1),(6,5)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0)]
  | 28 => some [(4,5)]
  | 29 => some [(1,0),(7,0)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0),(7,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(5,1),(8,1)]
  | 50 => some [(0,1),(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(8,3)]
  | 71 => some [(5,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5)]
  | 79 => some [(4,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(2,0)]
  | 83 => some [(7,3)]
  | 84 => some [(5,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(3,1)]
  | 89 => some [(0,1)]
  | _ => some [(6,2)]
theorem root1Node60Domains3_fast_eq : root1Node60Domains3 = expandDomains root1Node60Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node60Domains3 v = expandDomains root1Node60Domains3Fast v from by decide) v
theorem root1Node60Step3Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq (by decide)
theorem root1Node60Step3Narrowing_checked :
    checkNarrowing table12 root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkNarrowing_flatten table12Scope [table12Rows0_0,table12Rows0_1,table12Rows0_2,table12Rows0_3,table12Rows0_4,table12Rows0_5,table12Rows1_0,table12Rows1_1,table12Rows1_2,table12Rows1_3,table12Rows1_4,table12Rows1_5,table12Rows2_0,table12Rows2_1,table12Rows2_2,table12Rows2_3,table12Rows2_4,table12Rows2_5,table12Rows3_0,table12Rows3_1,table12Rows3_2,table12Rows3_3,table12Rows3_4,table12Rows3_5,table12Rows4_0,table12Rows4_1,table12Rows4_2,table12Rows4_3,table12Rows4_4,table12Rows4_5,table12Rows5_0,table12Rows5_1,table12Rows5_2,table12Rows5_3,table12Rows5_4,table12Rows5_5,table12Rows6_0,table12Rows6_1,table12Rows6_2,table12Rows6_3,table12Rows6_4,table12Rows6_5,table12Rows7_0,table12Rows7_1,table12Rows7_2,table12Rows7_3,table12Rows7_4,table12Rows7_5,table12Rows8_0,table12Rows8_1,table12Rows8_2,table12Rows8_3,table12Rows8_4,table12Rows8_5]
    root1Node60Domains2 root1Node60Domains3 (by
      simp only [List.all_cons, List.all_nil, root1Node60Step3Chunk0_0_checked, root1Node60Step3Chunk0_1_checked, root1Node60Step3Chunk0_2_checked, root1Node60Step3Chunk0_3_checked, root1Node60Step3Chunk0_4_checked, root1Node60Step3Chunk0_5_checked, root1Node60Step3Chunk1_0_checked, root1Node60Step3Chunk1_1_checked, root1Node60Step3Chunk1_2_checked, root1Node60Step3Chunk1_3_checked, root1Node60Step3Chunk1_4_checked, root1Node60Step3Chunk1_5_checked, root1Node60Step3Chunk2_0_checked, root1Node60Step3Chunk2_1_checked, root1Node60Step3Chunk2_2_checked, root1Node60Step3Chunk2_3_checked, root1Node60Step3Chunk2_4_checked, root1Node60Step3Chunk2_5_checked, root1Node60Step3Chunk3_0_checked, root1Node60Step3Chunk3_1_checked, root1Node60Step3Chunk3_2_checked, root1Node60Step3Chunk3_3_checked, root1Node60Step3Chunk3_4_checked, root1Node60Step3Chunk3_5_checked, root1Node60Step3Chunk4_0_checked, root1Node60Step3Chunk4_1_checked, root1Node60Step3Chunk4_2_checked, root1Node60Step3Chunk4_3_checked, root1Node60Step3Chunk4_4_checked, root1Node60Step3Chunk4_5_checked, root1Node60Step3Chunk5_0_checked, root1Node60Step3Chunk5_1_checked, root1Node60Step3Chunk5_2_checked, root1Node60Step3Chunk5_3_checked, root1Node60Step3Chunk5_4_checked, root1Node60Step3Chunk5_5_checked, root1Node60Step3Chunk6_0_checked, root1Node60Step3Chunk6_1_checked, root1Node60Step3Chunk6_2_checked, root1Node60Step3Chunk6_3_checked, root1Node60Step3Chunk6_4_checked, root1Node60Step3Chunk6_5_checked, root1Node60Step3Chunk7_0_checked, root1Node60Step3Chunk7_1_checked, root1Node60Step3Chunk7_2_checked, root1Node60Step3Chunk7_3_checked, root1Node60Step3Chunk7_4_checked, root1Node60Step3Chunk7_5_checked, root1Node60Step3Chunk8_0_checked, root1Node60Step3Chunk8_1_checked, root1Node60Step3Chunk8_2_checked, root1Node60Step3Chunk8_3_checked, root1Node60Step3Chunk8_4_checked, root1Node60Step3Chunk8_5_checked, Bool.true_and])
theorem root1Node60Step3_checked :
    checkReplacement table12 root1Node60Domains2 root1Node60Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root1Node60Domains2 root1Node60Domains3
    root1Node60Domains2Fast root1Node60Domains3Fast
    root1Node60Domains2_fast_eq root1Node60Domains3_fast_eq
    root1Node60Step3Narrowing_checked (by decide)
def root1Node61Domains0 : Domains 91 State := restrict root1Node60Domains3 5 (1,5)
def root1Node61Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(1,5)]
  | 6 => some [(0,4)]
  | 7 => some [(1,4)]
  | 8 => some [(0,5)]
  | 9 => some [(4,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(2,0),(2,4)]
  | 13 => some [(3,0)]
  | 14 => some [(2,5)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(3,1),(7,1)]
  | 20 => some [(0,1),(6,5)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0)]
  | 28 => some [(4,5)]
  | 29 => some [(1,0),(7,0)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0),(7,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(5,1),(8,1)]
  | 50 => some [(0,1),(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(8,3)]
  | 71 => some [(5,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5)]
  | 79 => some [(4,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(2,0)]
  | 83 => some [(7,3)]
  | 84 => some [(5,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(3,1)]
  | 89 => some [(0,1)]
  | _ => some [(6,2)]
theorem root1Node61Domains0_fast_eq : root1Node61Domains0 = expandDomains root1Node61Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node61Domains0 v = expandDomains root1Node61Domains0Fast v from by decide) v
def root1Node61Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(5,5)]
  | 3 => [(7,0)]
  | 4 => [(4,3)]
  | 5 => [(1,5)]
  | 6 => [(0,4)]
  | 7 => [(1,4)]
  | 8 => [(0,5)]
  | 9 => [(4,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(2,0)]
  | 13 => [(3,0)]
  | 14 => [(2,5)]
  | 15 => [(6,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(3,1)]
  | 20 => [(0,1)]
  | 21 => [(4,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(8,2)]
  | 27 => [(5,0)]
  | 28 => [(4,5)]
  | 29 => [(1,0)]
  | 30 => [(7,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(1,5)]
  | 48 => [(6,1)]
  | 49 => [(5,1)]
  | 50 => [(0,1)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(7,0)]
  | 59 => [(8,3)]
  | 60 => [(8,5)]
  | 61 => [(6,1)]
  | 62 => [(8,1)]
  | 63 => [(6,5)]
  | 64 => [(0,4)]
  | 65 => [(5,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(7,4)]
  | 69 => [(6,3)]
  | 70 => [(8,3)]
  | 71 => [(5,5)]
  | 72 => [(7,0)]
  | 73 => [(4,3)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(4,1)]
  | 77 => [(0,2)]
  | 78 => [(0,5)]
  | 79 => [(4,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(2,0)]
  | 83 => [(7,3)]
  | 84 => [(5,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(3,1)]
  | 89 => [(0,1)]
  | _ => [(6,2)]
def root1Node61Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(1,5)]
  | 6 => some [(0,4)]
  | 7 => some [(1,4)]
  | 8 => some [(0,5)]
  | 9 => some [(4,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(2,0)]
  | 13 => some [(3,0)]
  | 14 => some [(2,5)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(3,1)]
  | 20 => some [(0,1)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0)]
  | 28 => some [(4,5)]
  | 29 => some [(1,0)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(5,1)]
  | 50 => some [(0,1)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(8,3)]
  | 71 => some [(5,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5)]
  | 79 => some [(4,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(2,0)]
  | 83 => some [(7,3)]
  | 84 => some [(5,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(3,1)]
  | 89 => some [(0,1)]
  | _ => some [(6,2)]
theorem root1Node61Domains1_fast_eq : root1Node61Domains1 = expandDomains root1Node61Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node61Domains1 v = expandDomains root1Node61Domains1Fast v from by decide) v
theorem root1Node61Step1Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq (by decide)
theorem root1Node61Step1Narrowing_checked :
    checkNarrowing table12 root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkNarrowing_flatten table12Scope [table12Rows0_0,table12Rows0_1,table12Rows0_2,table12Rows0_3,table12Rows0_4,table12Rows0_5,table12Rows1_0,table12Rows1_1,table12Rows1_2,table12Rows1_3,table12Rows1_4,table12Rows1_5,table12Rows2_0,table12Rows2_1,table12Rows2_2,table12Rows2_3,table12Rows2_4,table12Rows2_5,table12Rows3_0,table12Rows3_1,table12Rows3_2,table12Rows3_3,table12Rows3_4,table12Rows3_5,table12Rows4_0,table12Rows4_1,table12Rows4_2,table12Rows4_3,table12Rows4_4,table12Rows4_5,table12Rows5_0,table12Rows5_1,table12Rows5_2,table12Rows5_3,table12Rows5_4,table12Rows5_5,table12Rows6_0,table12Rows6_1,table12Rows6_2,table12Rows6_3,table12Rows6_4,table12Rows6_5,table12Rows7_0,table12Rows7_1,table12Rows7_2,table12Rows7_3,table12Rows7_4,table12Rows7_5,table12Rows8_0,table12Rows8_1,table12Rows8_2,table12Rows8_3,table12Rows8_4,table12Rows8_5]
    root1Node61Domains0 root1Node61Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node61Step1Chunk0_0_checked, root1Node61Step1Chunk0_1_checked, root1Node61Step1Chunk0_2_checked, root1Node61Step1Chunk0_3_checked, root1Node61Step1Chunk0_4_checked, root1Node61Step1Chunk0_5_checked, root1Node61Step1Chunk1_0_checked, root1Node61Step1Chunk1_1_checked, root1Node61Step1Chunk1_2_checked, root1Node61Step1Chunk1_3_checked, root1Node61Step1Chunk1_4_checked, root1Node61Step1Chunk1_5_checked, root1Node61Step1Chunk2_0_checked, root1Node61Step1Chunk2_1_checked, root1Node61Step1Chunk2_2_checked, root1Node61Step1Chunk2_3_checked, root1Node61Step1Chunk2_4_checked, root1Node61Step1Chunk2_5_checked, root1Node61Step1Chunk3_0_checked, root1Node61Step1Chunk3_1_checked, root1Node61Step1Chunk3_2_checked, root1Node61Step1Chunk3_3_checked, root1Node61Step1Chunk3_4_checked, root1Node61Step1Chunk3_5_checked, root1Node61Step1Chunk4_0_checked, root1Node61Step1Chunk4_1_checked, root1Node61Step1Chunk4_2_checked, root1Node61Step1Chunk4_3_checked, root1Node61Step1Chunk4_4_checked, root1Node61Step1Chunk4_5_checked, root1Node61Step1Chunk5_0_checked, root1Node61Step1Chunk5_1_checked, root1Node61Step1Chunk5_2_checked, root1Node61Step1Chunk5_3_checked, root1Node61Step1Chunk5_4_checked, root1Node61Step1Chunk5_5_checked, root1Node61Step1Chunk6_0_checked, root1Node61Step1Chunk6_1_checked, root1Node61Step1Chunk6_2_checked, root1Node61Step1Chunk6_3_checked, root1Node61Step1Chunk6_4_checked, root1Node61Step1Chunk6_5_checked, root1Node61Step1Chunk7_0_checked, root1Node61Step1Chunk7_1_checked, root1Node61Step1Chunk7_2_checked, root1Node61Step1Chunk7_3_checked, root1Node61Step1Chunk7_4_checked, root1Node61Step1Chunk7_5_checked, root1Node61Step1Chunk8_0_checked, root1Node61Step1Chunk8_1_checked, root1Node61Step1Chunk8_2_checked, root1Node61Step1Chunk8_3_checked, root1Node61Step1Chunk8_4_checked, root1Node61Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node61Step1_checked :
    checkReplacement table12 root1Node61Domains0 root1Node61Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node61Domains0 root1Node61Domains1
    root1Node61Domains0Fast root1Node61Domains1Fast
    root1Node61Domains0_fast_eq root1Node61Domains1_fast_eq
    root1Node61Step1Narrowing_checked (by decide)
theorem root1Node61Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node61Domains1 (.output 29) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
