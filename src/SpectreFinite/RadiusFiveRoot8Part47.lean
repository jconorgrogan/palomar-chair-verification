module

public import SpectreFinite.RadiusFiveRoot8Part46
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable35
public import SpectreFinite.RadiusFiveTable52
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node127Domains0 : Domains 91 State := restrict root8Node123Domains2 20 (3,5)
def root8Node127Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(3,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(3,5)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(2,0),(2,4)]
  | 30 => some [(4,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1),(7,1)]
  | 39 => some [(0,1),(6,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(1,3),(6,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4),(1,1)]
  | 79 => some [(5,1),(5,4)]
  | 80 => some [(0,1),(6,4)]
  | 81 => some [(1,2),(6,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(3,5),(5,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(2,1),(4,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root8Node127Domains0_fast_eq : root8Node127Domains0 = expandDomains root8Node127Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node127Domains0 v = expandDomains root8Node127Domains0Fast v from by decide) v
def root8Node127Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(8,2)]
  | 6 => [(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(3,3)]
  | 14 => [(5,2)]
  | 15 => [(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(3,5)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(2,4)]
  | 30 => [(4,5)]
  | 31 => [(1,0)]
  | 32 => [(7,1)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(7,1)]
  | 39 => [(6,5)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(4,0)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(7,0)]
  | 51 => [(6,1)]
  | 52 => [(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
  | 62 => [(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3)]
  | 67 => [(8,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(1,3),(6,3)]
  | 71 => [(7,2),(8,2)]
  | 72 => [(4,0)]
  | 73 => [(7,3)]
  | 74 => [(4,2)]
  | 75 => [(5,3)]
  | 76 => [(8,5)]
  | 77 => [(7,0)]
  | 78 => [(0,4),(1,1)]
  | 79 => [(5,1),(5,4)]
  | 80 => [(0,1)]
  | 81 => [(6,2)]
  | 82 => [(7,4)]
  | 83 => [(6,3)]
  | 84 => [(7,2)]
  | 85 => [(4,3),(8,3)]
  | 86 => [(3,5),(5,5)]
  | 87 => [(1,0)]
  | 88 => [(2,1)]
  | 89 => [(0,2)]
  | _ => [(1,1)]
def root8Node127Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(3,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(3,5)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(2,4)]
  | 30 => some [(4,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(7,1)]
  | 39 => some [(6,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(1,3),(6,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4),(1,1)]
  | 79 => some [(5,1),(5,4)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(3,5),(5,5)]
  | 87 => some [(1,0)]
  | 88 => some [(2,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root8Node127Domains1_fast_eq : root8Node127Domains1 = expandDomains root8Node127Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node127Domains1 v = expandDomains root8Node127Domains1Fast v from by decide) v
theorem root8Node127Step1Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq (by decide)
theorem root8Node127Step1Narrowing_checked :
    checkNarrowing table57 root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root8Node127Domains0 root8Node127Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node127Step1Chunk0_0_checked, root8Node127Step1Chunk0_1_checked, root8Node127Step1Chunk0_2_checked, root8Node127Step1Chunk0_3_checked, root8Node127Step1Chunk0_4_checked, root8Node127Step1Chunk0_5_checked, root8Node127Step1Chunk1_0_checked, root8Node127Step1Chunk1_1_checked, root8Node127Step1Chunk1_2_checked, root8Node127Step1Chunk1_3_checked, root8Node127Step1Chunk1_4_checked, root8Node127Step1Chunk1_5_checked, root8Node127Step1Chunk2_0_checked, root8Node127Step1Chunk2_1_checked, root8Node127Step1Chunk2_2_checked, root8Node127Step1Chunk2_3_checked, root8Node127Step1Chunk2_4_checked, root8Node127Step1Chunk2_5_checked, root8Node127Step1Chunk3_0_checked, root8Node127Step1Chunk3_1_checked, root8Node127Step1Chunk3_2_checked, root8Node127Step1Chunk3_3_checked, root8Node127Step1Chunk3_4_checked, root8Node127Step1Chunk3_5_checked, root8Node127Step1Chunk4_0_checked, root8Node127Step1Chunk4_1_checked, root8Node127Step1Chunk4_2_checked, root8Node127Step1Chunk4_3_checked, root8Node127Step1Chunk4_4_checked, root8Node127Step1Chunk4_5_checked, root8Node127Step1Chunk5_0_checked, root8Node127Step1Chunk5_1_checked, root8Node127Step1Chunk5_2_checked, root8Node127Step1Chunk5_3_checked, root8Node127Step1Chunk5_4_checked, root8Node127Step1Chunk5_5_checked, root8Node127Step1Chunk6_0_checked, root8Node127Step1Chunk6_1_checked, root8Node127Step1Chunk6_2_checked, root8Node127Step1Chunk6_3_checked, root8Node127Step1Chunk6_4_checked, root8Node127Step1Chunk6_5_checked, root8Node127Step1Chunk7_0_checked, root8Node127Step1Chunk7_1_checked, root8Node127Step1Chunk7_2_checked, root8Node127Step1Chunk7_3_checked, root8Node127Step1Chunk7_4_checked, root8Node127Step1Chunk7_5_checked, root8Node127Step1Chunk8_0_checked, root8Node127Step1Chunk8_1_checked, root8Node127Step1Chunk8_2_checked, root8Node127Step1Chunk8_3_checked, root8Node127Step1Chunk8_4_checked, root8Node127Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node127Step1_checked :
    checkReplacement table57 root8Node127Domains0 root8Node127Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node127Domains0 root8Node127Domains1
    root8Node127Domains0Fast root8Node127Domains1Fast
    root8Node127Domains0_fast_eq root8Node127Domains1_fast_eq
    root8Node127Step1Narrowing_checked (by decide)
def root8Node127Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(8,2)]
  | 6 => [(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(3,3)]
  | 14 => [(5,2)]
  | 15 => [(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(3,5)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(2,4)]
  | 30 => [(4,5)]
  | 31 => [(1,0)]
  | 32 => [(7,1)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(7,1)]
  | 39 => [(6,5)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(4,0)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(7,0)]
  | 51 => [(6,1)]
  | 52 => [(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
  | 62 => [(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3)]
  | 67 => [(8,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(6,3)]
  | 71 => [(7,2)]
  | 72 => [(4,0)]
  | 73 => [(7,3)]
  | 74 => [(4,2)]
  | 75 => [(5,3)]
  | 76 => [(8,5)]
  | 77 => [(7,0)]
  | 78 => [(1,1)]
  | 79 => [(5,1)]
  | 80 => [(0,1)]
  | 81 => [(6,2)]
  | 82 => [(7,4)]
  | 83 => [(6,3)]
  | 84 => [(7,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5)]
  | 87 => [(1,0)]
  | 88 => [(2,1)]
  | 89 => [(0,2)]
  | _ => [(1,1)]
def root8Node127Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(3,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(3,5)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(2,4)]
  | 30 => some [(4,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(7,1)]
  | 39 => some [(6,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(4,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(1,1)]
  | 79 => some [(5,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(1,0)]
  | 88 => some [(2,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root8Node127Domains2_fast_eq : root8Node127Domains2 = expandDomains root8Node127Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node127Domains2 v = expandDomains root8Node127Domains2Fast v from by decide) v
theorem root8Node127Step2Chunk0_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_0⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk0_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_1⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk0_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_2⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk0_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_3⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk0_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_4⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk0_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_5⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk1_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_0⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk1_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_1⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk1_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_2⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk1_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_3⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk1_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_4⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk1_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_5⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk2_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_0⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk2_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_1⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk2_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_2⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk2_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_3⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk2_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_4⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk2_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_5⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk3_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_0⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk3_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_1⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk3_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_2⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk3_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_3⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk3_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_4⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk3_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_5⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk4_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_0⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk4_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_1⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk4_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_2⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk4_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_3⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk4_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_4⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk4_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_5⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk5_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_0⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk5_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_1⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk5_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_2⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk5_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_3⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk5_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_4⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk5_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_5⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk6_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_0⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk6_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_1⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk6_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_2⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk6_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_3⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk6_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_4⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk6_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_5⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk7_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_0⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk7_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_1⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk7_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_2⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk7_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_3⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk7_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_4⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk7_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_5⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk8_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_0⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk8_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_1⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk8_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_2⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk8_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_3⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk8_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_4⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Chunk8_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_5⟩
      root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq (by decide)
theorem root8Node127Step2Narrowing_checked :
    checkNarrowing table52 root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkNarrowing_flatten table52Scope [table52Rows0_0,table52Rows0_1,table52Rows0_2,table52Rows0_3,table52Rows0_4,table52Rows0_5,table52Rows1_0,table52Rows1_1,table52Rows1_2,table52Rows1_3,table52Rows1_4,table52Rows1_5,table52Rows2_0,table52Rows2_1,table52Rows2_2,table52Rows2_3,table52Rows2_4,table52Rows2_5,table52Rows3_0,table52Rows3_1,table52Rows3_2,table52Rows3_3,table52Rows3_4,table52Rows3_5,table52Rows4_0,table52Rows4_1,table52Rows4_2,table52Rows4_3,table52Rows4_4,table52Rows4_5,table52Rows5_0,table52Rows5_1,table52Rows5_2,table52Rows5_3,table52Rows5_4,table52Rows5_5,table52Rows6_0,table52Rows6_1,table52Rows6_2,table52Rows6_3,table52Rows6_4,table52Rows6_5,table52Rows7_0,table52Rows7_1,table52Rows7_2,table52Rows7_3,table52Rows7_4,table52Rows7_5,table52Rows8_0,table52Rows8_1,table52Rows8_2,table52Rows8_3,table52Rows8_4,table52Rows8_5]
    root8Node127Domains1 root8Node127Domains2 (by
      simp only [List.all_cons, List.all_nil, root8Node127Step2Chunk0_0_checked, root8Node127Step2Chunk0_1_checked, root8Node127Step2Chunk0_2_checked, root8Node127Step2Chunk0_3_checked, root8Node127Step2Chunk0_4_checked, root8Node127Step2Chunk0_5_checked, root8Node127Step2Chunk1_0_checked, root8Node127Step2Chunk1_1_checked, root8Node127Step2Chunk1_2_checked, root8Node127Step2Chunk1_3_checked, root8Node127Step2Chunk1_4_checked, root8Node127Step2Chunk1_5_checked, root8Node127Step2Chunk2_0_checked, root8Node127Step2Chunk2_1_checked, root8Node127Step2Chunk2_2_checked, root8Node127Step2Chunk2_3_checked, root8Node127Step2Chunk2_4_checked, root8Node127Step2Chunk2_5_checked, root8Node127Step2Chunk3_0_checked, root8Node127Step2Chunk3_1_checked, root8Node127Step2Chunk3_2_checked, root8Node127Step2Chunk3_3_checked, root8Node127Step2Chunk3_4_checked, root8Node127Step2Chunk3_5_checked, root8Node127Step2Chunk4_0_checked, root8Node127Step2Chunk4_1_checked, root8Node127Step2Chunk4_2_checked, root8Node127Step2Chunk4_3_checked, root8Node127Step2Chunk4_4_checked, root8Node127Step2Chunk4_5_checked, root8Node127Step2Chunk5_0_checked, root8Node127Step2Chunk5_1_checked, root8Node127Step2Chunk5_2_checked, root8Node127Step2Chunk5_3_checked, root8Node127Step2Chunk5_4_checked, root8Node127Step2Chunk5_5_checked, root8Node127Step2Chunk6_0_checked, root8Node127Step2Chunk6_1_checked, root8Node127Step2Chunk6_2_checked, root8Node127Step2Chunk6_3_checked, root8Node127Step2Chunk6_4_checked, root8Node127Step2Chunk6_5_checked, root8Node127Step2Chunk7_0_checked, root8Node127Step2Chunk7_1_checked, root8Node127Step2Chunk7_2_checked, root8Node127Step2Chunk7_3_checked, root8Node127Step2Chunk7_4_checked, root8Node127Step2Chunk7_5_checked, root8Node127Step2Chunk8_0_checked, root8Node127Step2Chunk8_1_checked, root8Node127Step2Chunk8_2_checked, root8Node127Step2Chunk8_3_checked, root8Node127Step2Chunk8_4_checked, root8Node127Step2Chunk8_5_checked, Bool.true_and])
theorem root8Node127Step2_checked :
    checkReplacement table52 root8Node127Domains1 root8Node127Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root8Node127Domains1 root8Node127Domains2
    root8Node127Domains1Fast root8Node127Domains2Fast
    root8Node127Domains1_fast_eq root8Node127Domains2_fast_eq
    root8Node127Step2Narrowing_checked (by decide)
theorem root8Node127Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node127Domains2 (.output 63) = true := by decide
def root8Node128Domains0 : Domains 91 State := restrict root8Node98Domains1 4 (6,3)
def root8Node128Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,2),(7,2),(8,2)]
  | 6 => some [(2,1),(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(4,1),(8,1)]
  | 10 => some [(0,2),(6,5)]
  | 11 => some [(0,4),(1,1)]
  | 12 => some [(3,4),(4,1),(5,1),(5,4),(8,1)]
  | 13 => some [(0,0),(1,3),(3,3),(7,3)]
  | 14 => some [(3,2),(5,2)]
  | 15 => some [(4,0),(8,0)]
  | 16 => some [(7,3),(8,3)]
  | 17 => some [(5,2),(5,5)]
  | 18 => some [(7,0),(8,0)]
  | 19 => some [(2,3),(4,3),(7,3),(8,3)]
  | 20 => some [(0,2),(1,5),(3,5),(5,2),(5,5)]
  | 21 => some [(0,1),(1,5),(6,5)]
  | 22 => some [(0,4),(6,1),(6,2)]
  | 23 => some [(5,1),(5,4),(8,4)]
  | 24 => some [(0,1),(1,4)]
  | 25 => some [(0,5),(6,2)]
  | 26 => some [(4,4),(8,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(2,0),(2,4),(4,0),(4,4),(8,4)]
  | 30 => some [(4,5)]
  | 31 => some [(1,0),(7,0)]
  | 32 => some [(4,3),(7,1),(8,3)]
  | 33 => some [(7,5),(8,5)]
  | 34 => some [(1,0),(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(3,1),(5,1),(7,1),(8,1)]
  | 39 => some [(0,1),(1,5),(6,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0),(7,4)]
  | 43 => some [(1,3),(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3)]
  | 49 => some [(4,5),(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1),(8,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(1,3),(6,3)]
  | 60 => some [(7,2),(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1),(8,1)]
  | 68 => some [(0,2),(1,5),(6,5)]
  | 69 => some [(0,4),(1,1),(6,1)]
  | 70 => some [(0,5),(1,3),(6,3)]
  | 71 => some [(4,4),(7,2),(8,2)]
  | 72 => some [(1,4),(4,0),(7,4),(8,0)]
  | 73 => some [(0,5),(1,3),(6,3),(7,3)]
  | 74 => some [(2,2),(2,4),(4,2)]
  | 75 => some [(1,3),(3,3),(5,3)]
  | 76 => some [(5,2),(5,5),(8,5)]
  | 77 => some [(7,0),(8,0)]
  | 78 => some [(0,4),(1,1),(7,1)]
  | 79 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 80 => some [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 81 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 82 => some [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | 83 => some [(0,4),(0,5),(6,2),(6,3)]
  | 84 => some [(4,4),(5,4),(7,2),(8,4)]
  | 85 => some [(4,3),(7,3),(8,3)]
  | 86 => some [(3,5),(5,2),(5,5),(8,2)]
  | 87 => some [(0,3),(1,0),(3,0),(5,0),(7,0)]
  | 88 => some [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 89 => some [(0,2),(1,0),(6,0),(7,0)]
  | _ => some [(1,1),(4,3),(7,1)]
theorem root8Node128Domains0_fast_eq : root8Node128Domains0 = expandDomains root8Node128Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node128Domains0 v = expandDomains root8Node128Domains0Fast v from by decide) v
def root8Node128Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(7,2)]
  | 6 => [(2,1),(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(4,1)]
  | 10 => [(0,2)]
  | 11 => [(1,1)]
  | 12 => [(4,1),(5,1),(8,1)]
  | 13 => [(0,0),(1,3),(3,3),(7,3)]
  | 14 => [(3,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(5,2),(5,5)]
  | 21 => [(0,1),(1,5),(6,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(1,4),(6,4)]
  | 28 => [(0,5),(1,2)]
  | 29 => [(4,4),(8,4)]
  | 30 => [(4,5)]
  | 31 => [(7,0)]
  | 32 => [(8,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3),(6,0)]
  | 38 => [(7,1),(8,1)]
  | 39 => [(1,5)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2),(8,2)]
  | 48 => [(5,0),(5,3)]
  | 49 => [(4,5),(8,5)]
  | 50 => [(1,0),(7,0)]
  | 51 => [(6,1)]
  | 52 => [(5,1),(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4),(8,4)]
  | 59 => [(0,0),(6,3)]
  | 60 => [(7,2),(8,2)]
  | 61 => [(8,3)]
  | 62 => [(5,5),(8,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(3,5),(7,5)]
  | 66 => [(0,3)]
  | 67 => [(4,1),(8,1)]
  | 68 => [(0,2),(1,5)]
  | 69 => [(0,4),(1,1),(6,1)]
  | 70 => [(0,5),(1,3),(6,3)]
  | 71 => [(4,4),(7,2),(8,2)]
  | 72 => [(1,4),(7,4)]
  | 73 => [(0,5),(1,3),(6,3)]
  | 74 => [(2,2),(2,4),(4,2)]
  | 75 => [(1,3),(3,3),(5,3)]
  | 76 => [(5,2),(5,5),(8,5)]
  | 77 => [(7,0),(8,0)]
  | 78 => [(0,4),(1,1),(7,1)]
  | 79 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 80 => [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 81 => [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 82 => [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | 83 => [(0,4),(0,5),(6,2),(6,3)]
  | 84 => [(4,4),(5,4),(7,2),(8,4)]
  | 85 => [(4,3),(7,3),(8,3)]
  | 86 => [(3,5),(5,2),(5,5),(8,2)]
  | 87 => [(0,3),(1,0),(3,0),(5,0),(7,0)]
  | 88 => [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 89 => [(0,2),(1,0),(6,0),(7,0)]
  | _ => [(1,1),(4,3),(7,1)]
def root8Node128Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(2,1),(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(4,1),(5,1),(8,1)]
  | 13 => some [(0,0),(1,3),(3,3),(7,3)]
  | 14 => some [(3,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(5,2),(5,5)]
  | 21 => some [(0,1),(1,5),(6,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(4,4),(8,4)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(7,1),(8,1)]
  | 39 => some [(1,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3)]
  | 49 => some [(4,5),(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1),(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(6,3)]
  | 60 => some [(7,2),(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1),(8,1)]
  | 68 => some [(0,2),(1,5)]
  | 69 => some [(0,4),(1,1),(6,1)]
  | 70 => some [(0,5),(1,3),(6,3)]
  | 71 => some [(4,4),(7,2),(8,2)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(1,3),(6,3)]
  | 74 => some [(2,2),(2,4),(4,2)]
  | 75 => some [(1,3),(3,3),(5,3)]
  | 76 => some [(5,2),(5,5),(8,5)]
  | 77 => some [(7,0),(8,0)]
  | 78 => some [(0,4),(1,1),(7,1)]
  | 79 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 80 => some [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 81 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 82 => some [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | 83 => some [(0,4),(0,5),(6,2),(6,3)]
  | 84 => some [(4,4),(5,4),(7,2),(8,4)]
  | 85 => some [(4,3),(7,3),(8,3)]
  | 86 => some [(3,5),(5,2),(5,5),(8,2)]
  | 87 => some [(0,3),(1,0),(3,0),(5,0),(7,0)]
  | 88 => some [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 89 => some [(0,2),(1,0),(6,0),(7,0)]
  | _ => some [(1,1),(4,3),(7,1)]
theorem root8Node128Domains1_fast_eq : root8Node128Domains1 = expandDomains root8Node128Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node128Domains1 v = expandDomains root8Node128Domains1Fast v from by decide) v
theorem root8Node128Step1Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq (by decide)
theorem root8Node128Step1Narrowing_checked :
    checkNarrowing table35 root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkNarrowing_flatten table35Scope [table35Rows0_0,table35Rows0_1,table35Rows0_2,table35Rows0_3,table35Rows0_4,table35Rows0_5,table35Rows1_0,table35Rows1_1,table35Rows1_2,table35Rows1_3,table35Rows1_4,table35Rows1_5,table35Rows2_0,table35Rows2_1,table35Rows2_2,table35Rows2_3,table35Rows2_4,table35Rows2_5,table35Rows3_0,table35Rows3_1,table35Rows3_2,table35Rows3_3,table35Rows3_4,table35Rows3_5,table35Rows4_0,table35Rows4_1,table35Rows4_2,table35Rows4_3,table35Rows4_4,table35Rows4_5,table35Rows5_0,table35Rows5_1,table35Rows5_2,table35Rows5_3,table35Rows5_4,table35Rows5_5,table35Rows6_0,table35Rows6_1,table35Rows6_2,table35Rows6_3,table35Rows6_4,table35Rows6_5,table35Rows7_0,table35Rows7_1,table35Rows7_2,table35Rows7_3,table35Rows7_4,table35Rows7_5,table35Rows8_0,table35Rows8_1,table35Rows8_2,table35Rows8_3,table35Rows8_4,table35Rows8_5]
    root8Node128Domains0 root8Node128Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node128Step1Chunk0_0_checked, root8Node128Step1Chunk0_1_checked, root8Node128Step1Chunk0_2_checked, root8Node128Step1Chunk0_3_checked, root8Node128Step1Chunk0_4_checked, root8Node128Step1Chunk0_5_checked, root8Node128Step1Chunk1_0_checked, root8Node128Step1Chunk1_1_checked, root8Node128Step1Chunk1_2_checked, root8Node128Step1Chunk1_3_checked, root8Node128Step1Chunk1_4_checked, root8Node128Step1Chunk1_5_checked, root8Node128Step1Chunk2_0_checked, root8Node128Step1Chunk2_1_checked, root8Node128Step1Chunk2_2_checked, root8Node128Step1Chunk2_3_checked, root8Node128Step1Chunk2_4_checked, root8Node128Step1Chunk2_5_checked, root8Node128Step1Chunk3_0_checked, root8Node128Step1Chunk3_1_checked, root8Node128Step1Chunk3_2_checked, root8Node128Step1Chunk3_3_checked, root8Node128Step1Chunk3_4_checked, root8Node128Step1Chunk3_5_checked, root8Node128Step1Chunk4_0_checked, root8Node128Step1Chunk4_1_checked, root8Node128Step1Chunk4_2_checked, root8Node128Step1Chunk4_3_checked, root8Node128Step1Chunk4_4_checked, root8Node128Step1Chunk4_5_checked, root8Node128Step1Chunk5_0_checked, root8Node128Step1Chunk5_1_checked, root8Node128Step1Chunk5_2_checked, root8Node128Step1Chunk5_3_checked, root8Node128Step1Chunk5_4_checked, root8Node128Step1Chunk5_5_checked, root8Node128Step1Chunk6_0_checked, root8Node128Step1Chunk6_1_checked, root8Node128Step1Chunk6_2_checked, root8Node128Step1Chunk6_3_checked, root8Node128Step1Chunk6_4_checked, root8Node128Step1Chunk6_5_checked, root8Node128Step1Chunk7_0_checked, root8Node128Step1Chunk7_1_checked, root8Node128Step1Chunk7_2_checked, root8Node128Step1Chunk7_3_checked, root8Node128Step1Chunk7_4_checked, root8Node128Step1Chunk7_5_checked, root8Node128Step1Chunk8_0_checked, root8Node128Step1Chunk8_1_checked, root8Node128Step1Chunk8_2_checked, root8Node128Step1Chunk8_3_checked, root8Node128Step1Chunk8_4_checked, root8Node128Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node128Step1_checked :
    checkReplacement table35 root8Node128Domains0 root8Node128Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node128Domains0 root8Node128Domains1
    root8Node128Domains0Fast root8Node128Domains1Fast
    root8Node128Domains0_fast_eq root8Node128Domains1_fast_eq
    root8Node128Step1Narrowing_checked (by decide)
def root8Node128Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(7,2)]
  | 6 => [(2,1),(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(4,1)]
  | 10 => [(0,2)]
  | 11 => [(1,1)]
  | 12 => [(4,1),(5,1),(8,1)]
  | 13 => [(0,0)]
  | 14 => [(3,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(5,2),(5,5)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(1,4),(6,4)]
  | 28 => [(0,5),(1,2)]
  | 29 => [(4,4),(8,4)]
  | 30 => [(4,5)]
  | 31 => [(7,0)]
  | 32 => [(8,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3),(6,0)]
  | 38 => [(7,1),(8,1)]
  | 39 => [(1,5)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2),(8,2)]
  | 48 => [(5,0),(5,3)]
  | 49 => [(4,5),(8,5)]
  | 50 => [(1,0),(7,0)]
  | 51 => [(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4),(8,4)]
  | 59 => [(0,0),(6,3)]
  | 60 => [(7,2),(8,2)]
  | 61 => [(8,3)]
  | 62 => [(5,5),(8,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(3,5),(7,5)]
  | 66 => [(0,3)]
  | 67 => [(4,1),(8,1)]
  | 68 => [(0,2),(1,5)]
  | 69 => [(0,4),(1,1),(6,1)]
  | 70 => [(0,5),(6,3)]
  | 71 => [(4,4),(7,2)]
  | 72 => [(1,4),(7,4)]
  | 73 => [(0,5),(1,3),(6,3)]
  | 74 => [(2,2),(2,4),(4,2)]
  | 75 => [(1,3),(3,3),(5,3)]
  | 76 => [(5,2),(5,5),(8,5)]
  | 77 => [(7,0),(8,0)]
  | 78 => [(1,1),(7,1)]
  | 79 => [(4,1),(7,5),(8,1)]
  | 80 => [(0,2),(6,0),(6,5)]
  | 81 => [(0,4),(1,1),(7,1)]
  | 82 => [(0,1),(1,4),(3,4),(6,5)]
  | 83 => [(0,4),(0,5),(6,2),(6,3)]
  | 84 => [(4,4),(5,4),(7,2),(8,4)]
  | 85 => [(7,3),(8,3)]
  | 86 => [(5,2),(5,5),(8,2)]
  | 87 => [(3,0),(5,0),(7,0)]
  | 88 => [(2,3),(2,5),(4,5)]
  | 89 => [(0,2),(1,0),(6,0),(7,0)]
  | _ => [(1,1),(4,3),(7,1)]
def root8Node128Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(2,1),(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(4,1),(5,1),(8,1)]
  | 13 => some [(0,0)]
  | 14 => some [(3,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(5,2),(5,5)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(4,4),(8,4)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(7,1),(8,1)]
  | 39 => some [(1,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3)]
  | 49 => some [(4,5),(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(6,3)]
  | 60 => some [(7,2),(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1),(8,1)]
  | 68 => some [(0,2),(1,5)]
  | 69 => some [(0,4),(1,1),(6,1)]
  | 70 => some [(0,5),(6,3)]
  | 71 => some [(4,4),(7,2)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(1,3),(6,3)]
  | 74 => some [(2,2),(2,4),(4,2)]
  | 75 => some [(1,3),(3,3),(5,3)]
  | 76 => some [(5,2),(5,5),(8,5)]
  | 77 => some [(7,0),(8,0)]
  | 78 => some [(1,1),(7,1)]
  | 79 => some [(4,1),(7,5),(8,1)]
  | 80 => some [(0,2),(6,0),(6,5)]
  | 81 => some [(0,4),(1,1),(7,1)]
  | 82 => some [(0,1),(1,4),(3,4),(6,5)]
  | 83 => some [(0,4),(0,5),(6,2),(6,3)]
  | 84 => some [(4,4),(5,4),(7,2),(8,4)]
  | 85 => some [(7,3),(8,3)]
  | 86 => some [(5,2),(5,5),(8,2)]
  | 87 => some [(3,0),(5,0),(7,0)]
  | 88 => some [(2,3),(2,5),(4,5)]
  | 89 => some [(0,2),(1,0),(6,0),(7,0)]
  | _ => some [(1,1),(4,3),(7,1)]
theorem root8Node128Domains2_fast_eq : root8Node128Domains2 = expandDomains root8Node128Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node128Domains2 v = expandDomains root8Node128Domains2Fast v from by decide) v
theorem root8Node128Step2Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq (by decide)
theorem root8Node128Step2Narrowing_checked :
    checkNarrowing table54 root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root8Node128Domains1 root8Node128Domains2 (by
      simp only [List.all_cons, List.all_nil, root8Node128Step2Chunk0_0_checked, root8Node128Step2Chunk0_1_checked, root8Node128Step2Chunk0_2_checked, root8Node128Step2Chunk0_3_checked, root8Node128Step2Chunk0_4_checked, root8Node128Step2Chunk0_5_checked, root8Node128Step2Chunk1_0_checked, root8Node128Step2Chunk1_1_checked, root8Node128Step2Chunk1_2_checked, root8Node128Step2Chunk1_3_checked, root8Node128Step2Chunk1_4_checked, root8Node128Step2Chunk1_5_checked, root8Node128Step2Chunk2_0_checked, root8Node128Step2Chunk2_1_checked, root8Node128Step2Chunk2_2_checked, root8Node128Step2Chunk2_3_checked, root8Node128Step2Chunk2_4_checked, root8Node128Step2Chunk2_5_checked, root8Node128Step2Chunk3_0_checked, root8Node128Step2Chunk3_1_checked, root8Node128Step2Chunk3_2_checked, root8Node128Step2Chunk3_3_checked, root8Node128Step2Chunk3_4_checked, root8Node128Step2Chunk3_5_checked, root8Node128Step2Chunk4_0_checked, root8Node128Step2Chunk4_1_checked, root8Node128Step2Chunk4_2_checked, root8Node128Step2Chunk4_3_checked, root8Node128Step2Chunk4_4_checked, root8Node128Step2Chunk4_5_checked, root8Node128Step2Chunk5_0_checked, root8Node128Step2Chunk5_1_checked, root8Node128Step2Chunk5_2_checked, root8Node128Step2Chunk5_3_checked, root8Node128Step2Chunk5_4_checked, root8Node128Step2Chunk5_5_checked, root8Node128Step2Chunk6_0_checked, root8Node128Step2Chunk6_1_checked, root8Node128Step2Chunk6_2_checked, root8Node128Step2Chunk6_3_checked, root8Node128Step2Chunk6_4_checked, root8Node128Step2Chunk6_5_checked, root8Node128Step2Chunk7_0_checked, root8Node128Step2Chunk7_1_checked, root8Node128Step2Chunk7_2_checked, root8Node128Step2Chunk7_3_checked, root8Node128Step2Chunk7_4_checked, root8Node128Step2Chunk7_5_checked, root8Node128Step2Chunk8_0_checked, root8Node128Step2Chunk8_1_checked, root8Node128Step2Chunk8_2_checked, root8Node128Step2Chunk8_3_checked, root8Node128Step2Chunk8_4_checked, root8Node128Step2Chunk8_5_checked, Bool.true_and])
theorem root8Node128Step2_checked :
    checkReplacement table54 root8Node128Domains1 root8Node128Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root8Node128Domains1 root8Node128Domains2
    root8Node128Domains1Fast root8Node128Domains2Fast
    root8Node128Domains1_fast_eq root8Node128Domains2_fast_eq
    root8Node128Step2Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
