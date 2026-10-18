module

public import SpectreFinite.RadiusFiveRoot6Part17
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable36
public import SpectreFinite.RadiusFiveTable45
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node40Domains0 : Domains 91 State := restrict root6Node38Domains2 5 (7,5)
def root6Node40Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,5)]
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
theorem root6Node40Domains0_fast_eq : root6Node40Domains0 = expandDomains root6Node40Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node40Domains0 v = expandDomains root6Node40Domains0Fast v from by decide) v
def root6Node40Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,1)]
  | 5 => [(7,5)]
  | 6 => [(1,2)]
  | 7 => [(7,4)]
  | 8 => [(1,3),(6,3)]
  | 9 => [(7,2),(8,2)]
  | 10 => [(4,0),(8,0)]
  | 11 => [(7,3)]
  | 12 => [(4,2)]
  | 13 => [(0,3)]
  | 14 => [(4,1),(8,1)]
  | 15 => [(0,2),(6,5)]
  | 16 => [(0,4),(1,1)]
  | 17 => [(5,1),(5,4)]
  | 18 => [(0,1),(6,4)]
  | 19 => [(1,2),(6,2)]
  | 20 => [(7,4)]
  | 21 => [(2,2),(2,4),(4,2)]
  | 22 => [(1,3),(3,3),(5,3)]
  | 23 => [(5,2),(5,5)]
  | 24 => [(7,0),(8,0)]
  | 25 => [(4,3),(8,3)]
  | 26 => [(3,5),(5,5)]
  | 27 => [(0,3),(1,0)]
  | 28 => [(2,1),(4,1)]
  | 29 => [(0,2)]
  | 30 => [(0,4),(1,1),(7,1)]
  | 31 => [(0,1),(1,4),(6,5)]
  | 32 => [(0,4),(0,5),(6,2)]
  | 33 => [(4,4),(5,4),(8,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,4),(4,4)]
  | 37 => [(0,0),(1,3)]
  | 38 => [(3,2),(5,2)]
  | 39 => [(4,0),(8,0)]
  | 40 => [(3,0),(5,0)]
  | 41 => [(2,5),(4,5)]
  | 42 => [(1,0),(6,0),(7,0)]
  | 43 => [(4,3),(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(1,5),(6,5)]
  | 48 => [(0,4),(6,1)]
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
def root6Node40Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3),(6,3)]
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
theorem root6Node40Domains1_fast_eq : root6Node40Domains1 = expandDomains root6Node40Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node40Domains1 v = expandDomains root6Node40Domains1Fast v from by decide) v
theorem root6Node40Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Narrowing_checked :
    checkNarrowing table36 root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root6Node40Domains0 root6Node40Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node40Step1Chunk0_0_checked, root6Node40Step1Chunk0_1_checked, root6Node40Step1Chunk0_2_checked, root6Node40Step1Chunk0_3_checked, root6Node40Step1Chunk0_4_checked, root6Node40Step1Chunk0_5_checked, root6Node40Step1Chunk1_0_checked, root6Node40Step1Chunk1_1_checked, root6Node40Step1Chunk1_2_checked, root6Node40Step1Chunk1_3_checked, root6Node40Step1Chunk1_4_checked, root6Node40Step1Chunk1_5_checked, root6Node40Step1Chunk2_0_checked, root6Node40Step1Chunk2_1_checked, root6Node40Step1Chunk2_2_checked, root6Node40Step1Chunk2_3_checked, root6Node40Step1Chunk2_4_checked, root6Node40Step1Chunk2_5_checked, root6Node40Step1Chunk3_0_checked, root6Node40Step1Chunk3_1_checked, root6Node40Step1Chunk3_2_checked, root6Node40Step1Chunk3_3_checked, root6Node40Step1Chunk3_4_checked, root6Node40Step1Chunk3_5_checked, root6Node40Step1Chunk4_0_checked, root6Node40Step1Chunk4_1_checked, root6Node40Step1Chunk4_2_checked, root6Node40Step1Chunk4_3_checked, root6Node40Step1Chunk4_4_checked, root6Node40Step1Chunk4_5_checked, root6Node40Step1Chunk5_0_checked, root6Node40Step1Chunk5_1_checked, root6Node40Step1Chunk5_2_checked, root6Node40Step1Chunk5_3_checked, root6Node40Step1Chunk5_4_checked, root6Node40Step1Chunk5_5_checked, root6Node40Step1Chunk6_0_checked, root6Node40Step1Chunk6_1_checked, root6Node40Step1Chunk6_2_checked, root6Node40Step1Chunk6_3_checked, root6Node40Step1Chunk6_4_checked, root6Node40Step1Chunk6_5_checked, root6Node40Step1Chunk7_0_checked, root6Node40Step1Chunk7_1_checked, root6Node40Step1Chunk7_2_checked, root6Node40Step1Chunk7_3_checked, root6Node40Step1Chunk7_4_checked, root6Node40Step1Chunk7_5_checked, root6Node40Step1Chunk8_0_checked, root6Node40Step1Chunk8_1_checked, root6Node40Step1Chunk8_2_checked, root6Node40Step1Chunk8_3_checked, root6Node40Step1Chunk8_4_checked, root6Node40Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node40Step1_checked :
    checkReplacement table36 root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq
    root6Node40Step1Narrowing_checked (by decide)
def root6Node41Domains0 : Domains 91 State := restrict root6Node40Domains1 8 (1,3)
def root6Node41Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3)]
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
theorem root6Node41Domains0_fast_eq : root6Node41Domains0 = expandDomains root6Node41Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node41Domains0 v = expandDomains root6Node41Domains0Fast v from by decide) v
def root6Node41Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,1)]
  | 5 => [(7,5)]
  | 6 => [(1,2)]
  | 7 => [(7,4)]
  | 8 => [(1,3)]
  | 9 => [(8,2)]
  | 10 => [(8,0)]
  | 11 => [(7,3)]
  | 12 => [(4,2)]
  | 13 => [(0,3)]
  | 14 => [(8,1)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(6,4)]
  | 19 => [(1,2)]
  | 20 => [(7,4)]
  | 21 => [(2,2),(2,4),(4,2)]
  | 22 => [(5,3)]
  | 23 => [(5,5)]
  | 24 => [(7,0)]
  | 25 => [(4,3)]
  | 26 => [(3,5)]
  | 27 => [(0,3)]
  | 28 => [(4,1)]
  | 29 => [(0,2)]
  | 30 => [(0,4),(1,1),(7,1)]
  | 31 => [(1,4)]
  | 32 => [(0,5)]
  | 33 => [(4,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,4)]
  | 37 => [(1,3)]
  | 38 => [(5,2)]
  | 39 => [(4,0),(8,0)]
  | 40 => [(3,0),(5,0)]
  | 41 => [(2,5)]
  | 42 => [(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(6,5)]
  | 48 => [(0,4)]
  | 49 => [(5,4)]
  | 50 => [(0,1),(1,4)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(7,0)]
  | 59 => [(4,3)]
  | 60 => [(7,5),(8,5)]
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
  | 76 => [(8,1)]
  | 77 => [(0,2),(6,5)]
  | 78 => [(0,5),(1,3)]
  | 79 => [(8,2)]
  | 80 => [(5,0)]
  | 81 => [(4,5)]
  | 82 => [(7,0)]
  | 83 => [(8,3)]
  | 84 => [(5,2),(8,5)]
  | 85 => [(0,4),(7,1)]
  | 86 => [(5,4),(7,5)]
  | 87 => [(0,0),(6,0)]
  | 88 => [(3,1),(7,2)]
  | 89 => [(0,1),(7,4)]
  | _ => [(6,2),(6,3)]
def root6Node41Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3)]
  | 9 => some [(8,2)]
  | 10 => some [(8,0)]
  | 11 => some [(7,3)]
  | 12 => some [(4,2)]
  | 13 => some [(0,3)]
  | 14 => some [(8,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(6,4)]
  | 19 => some [(1,2)]
  | 20 => some [(7,4)]
  | 21 => some [(2,2),(2,4),(4,2)]
  | 22 => some [(5,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(4,3)]
  | 26 => some [(3,5)]
  | 27 => some [(0,3)]
  | 28 => some [(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(0,4),(1,1),(7,1)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,4)]
  | 37 => some [(1,3)]
  | 38 => some [(5,2)]
  | 39 => some [(4,0),(8,0)]
  | 40 => some [(3,0),(5,0)]
  | 41 => some [(2,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(5,4)]
  | 50 => some [(0,1),(1,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(4,3)]
  | 60 => some [(7,5),(8,5)]
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
  | 76 => some [(8,1)]
  | 77 => some [(0,2),(6,5)]
  | 78 => some [(0,5),(1,3)]
  | 79 => some [(8,2)]
  | 80 => some [(5,0)]
  | 81 => some [(4,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(5,2),(8,5)]
  | 85 => some [(0,4),(7,1)]
  | 86 => some [(5,4),(7,5)]
  | 87 => some [(0,0),(6,0)]
  | 88 => some [(3,1),(7,2)]
  | 89 => some [(0,1),(7,4)]
  | _ => some [(6,2),(6,3)]
theorem root6Node41Domains1_fast_eq : root6Node41Domains1 = expandDomains root6Node41Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node41Domains1 v = expandDomains root6Node41Domains1Fast v from by decide) v
theorem root6Node41Step1Chunk0_0_checked :
    checkNarrowing ⟨table45Scope, table45Rows0_0⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk0_1_checked :
    checkNarrowing ⟨table45Scope, table45Rows0_1⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk0_2_checked :
    checkNarrowing ⟨table45Scope, table45Rows0_2⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk0_3_checked :
    checkNarrowing ⟨table45Scope, table45Rows0_3⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk0_4_checked :
    checkNarrowing ⟨table45Scope, table45Rows0_4⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk0_5_checked :
    checkNarrowing ⟨table45Scope, table45Rows0_5⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk1_0_checked :
    checkNarrowing ⟨table45Scope, table45Rows1_0⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk1_1_checked :
    checkNarrowing ⟨table45Scope, table45Rows1_1⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk1_2_checked :
    checkNarrowing ⟨table45Scope, table45Rows1_2⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk1_3_checked :
    checkNarrowing ⟨table45Scope, table45Rows1_3⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk1_4_checked :
    checkNarrowing ⟨table45Scope, table45Rows1_4⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk1_5_checked :
    checkNarrowing ⟨table45Scope, table45Rows1_5⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk2_0_checked :
    checkNarrowing ⟨table45Scope, table45Rows2_0⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk2_1_checked :
    checkNarrowing ⟨table45Scope, table45Rows2_1⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk2_2_checked :
    checkNarrowing ⟨table45Scope, table45Rows2_2⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk2_3_checked :
    checkNarrowing ⟨table45Scope, table45Rows2_3⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk2_4_checked :
    checkNarrowing ⟨table45Scope, table45Rows2_4⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk2_5_checked :
    checkNarrowing ⟨table45Scope, table45Rows2_5⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk3_0_checked :
    checkNarrowing ⟨table45Scope, table45Rows3_0⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk3_1_checked :
    checkNarrowing ⟨table45Scope, table45Rows3_1⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk3_2_checked :
    checkNarrowing ⟨table45Scope, table45Rows3_2⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk3_3_checked :
    checkNarrowing ⟨table45Scope, table45Rows3_3⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk3_4_checked :
    checkNarrowing ⟨table45Scope, table45Rows3_4⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk3_5_checked :
    checkNarrowing ⟨table45Scope, table45Rows3_5⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk4_0_checked :
    checkNarrowing ⟨table45Scope, table45Rows4_0⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk4_1_checked :
    checkNarrowing ⟨table45Scope, table45Rows4_1⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk4_2_checked :
    checkNarrowing ⟨table45Scope, table45Rows4_2⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk4_3_checked :
    checkNarrowing ⟨table45Scope, table45Rows4_3⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk4_4_checked :
    checkNarrowing ⟨table45Scope, table45Rows4_4⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk4_5_checked :
    checkNarrowing ⟨table45Scope, table45Rows4_5⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk5_0_checked :
    checkNarrowing ⟨table45Scope, table45Rows5_0⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk5_1_checked :
    checkNarrowing ⟨table45Scope, table45Rows5_1⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk5_2_checked :
    checkNarrowing ⟨table45Scope, table45Rows5_2⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk5_3_checked :
    checkNarrowing ⟨table45Scope, table45Rows5_3⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk5_4_checked :
    checkNarrowing ⟨table45Scope, table45Rows5_4⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk5_5_checked :
    checkNarrowing ⟨table45Scope, table45Rows5_5⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk6_0_checked :
    checkNarrowing ⟨table45Scope, table45Rows6_0⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk6_1_checked :
    checkNarrowing ⟨table45Scope, table45Rows6_1⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk6_2_checked :
    checkNarrowing ⟨table45Scope, table45Rows6_2⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk6_3_checked :
    checkNarrowing ⟨table45Scope, table45Rows6_3⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk6_4_checked :
    checkNarrowing ⟨table45Scope, table45Rows6_4⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk6_5_checked :
    checkNarrowing ⟨table45Scope, table45Rows6_5⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk7_0_checked :
    checkNarrowing ⟨table45Scope, table45Rows7_0⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk7_1_checked :
    checkNarrowing ⟨table45Scope, table45Rows7_1⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk7_2_checked :
    checkNarrowing ⟨table45Scope, table45Rows7_2⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk7_3_checked :
    checkNarrowing ⟨table45Scope, table45Rows7_3⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk7_4_checked :
    checkNarrowing ⟨table45Scope, table45Rows7_4⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk7_5_checked :
    checkNarrowing ⟨table45Scope, table45Rows7_5⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk8_0_checked :
    checkNarrowing ⟨table45Scope, table45Rows8_0⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk8_1_checked :
    checkNarrowing ⟨table45Scope, table45Rows8_1⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk8_2_checked :
    checkNarrowing ⟨table45Scope, table45Rows8_2⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk8_3_checked :
    checkNarrowing ⟨table45Scope, table45Rows8_3⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk8_4_checked :
    checkNarrowing ⟨table45Scope, table45Rows8_4⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Chunk8_5_checked :
    checkNarrowing ⟨table45Scope, table45Rows8_5⟩
      root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq (by decide)
theorem root6Node41Step1Narrowing_checked :
    checkNarrowing table45 root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkNarrowing_flatten table45Scope [table45Rows0_0,table45Rows0_1,table45Rows0_2,table45Rows0_3,table45Rows0_4,table45Rows0_5,table45Rows1_0,table45Rows1_1,table45Rows1_2,table45Rows1_3,table45Rows1_4,table45Rows1_5,table45Rows2_0,table45Rows2_1,table45Rows2_2,table45Rows2_3,table45Rows2_4,table45Rows2_5,table45Rows3_0,table45Rows3_1,table45Rows3_2,table45Rows3_3,table45Rows3_4,table45Rows3_5,table45Rows4_0,table45Rows4_1,table45Rows4_2,table45Rows4_3,table45Rows4_4,table45Rows4_5,table45Rows5_0,table45Rows5_1,table45Rows5_2,table45Rows5_3,table45Rows5_4,table45Rows5_5,table45Rows6_0,table45Rows6_1,table45Rows6_2,table45Rows6_3,table45Rows6_4,table45Rows6_5,table45Rows7_0,table45Rows7_1,table45Rows7_2,table45Rows7_3,table45Rows7_4,table45Rows7_5,table45Rows8_0,table45Rows8_1,table45Rows8_2,table45Rows8_3,table45Rows8_4,table45Rows8_5]
    root6Node41Domains0 root6Node41Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node41Step1Chunk0_0_checked, root6Node41Step1Chunk0_1_checked, root6Node41Step1Chunk0_2_checked, root6Node41Step1Chunk0_3_checked, root6Node41Step1Chunk0_4_checked, root6Node41Step1Chunk0_5_checked, root6Node41Step1Chunk1_0_checked, root6Node41Step1Chunk1_1_checked, root6Node41Step1Chunk1_2_checked, root6Node41Step1Chunk1_3_checked, root6Node41Step1Chunk1_4_checked, root6Node41Step1Chunk1_5_checked, root6Node41Step1Chunk2_0_checked, root6Node41Step1Chunk2_1_checked, root6Node41Step1Chunk2_2_checked, root6Node41Step1Chunk2_3_checked, root6Node41Step1Chunk2_4_checked, root6Node41Step1Chunk2_5_checked, root6Node41Step1Chunk3_0_checked, root6Node41Step1Chunk3_1_checked, root6Node41Step1Chunk3_2_checked, root6Node41Step1Chunk3_3_checked, root6Node41Step1Chunk3_4_checked, root6Node41Step1Chunk3_5_checked, root6Node41Step1Chunk4_0_checked, root6Node41Step1Chunk4_1_checked, root6Node41Step1Chunk4_2_checked, root6Node41Step1Chunk4_3_checked, root6Node41Step1Chunk4_4_checked, root6Node41Step1Chunk4_5_checked, root6Node41Step1Chunk5_0_checked, root6Node41Step1Chunk5_1_checked, root6Node41Step1Chunk5_2_checked, root6Node41Step1Chunk5_3_checked, root6Node41Step1Chunk5_4_checked, root6Node41Step1Chunk5_5_checked, root6Node41Step1Chunk6_0_checked, root6Node41Step1Chunk6_1_checked, root6Node41Step1Chunk6_2_checked, root6Node41Step1Chunk6_3_checked, root6Node41Step1Chunk6_4_checked, root6Node41Step1Chunk6_5_checked, root6Node41Step1Chunk7_0_checked, root6Node41Step1Chunk7_1_checked, root6Node41Step1Chunk7_2_checked, root6Node41Step1Chunk7_3_checked, root6Node41Step1Chunk7_4_checked, root6Node41Step1Chunk7_5_checked, root6Node41Step1Chunk8_0_checked, root6Node41Step1Chunk8_1_checked, root6Node41Step1Chunk8_2_checked, root6Node41Step1Chunk8_3_checked, root6Node41Step1Chunk8_4_checked, root6Node41Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node41Step1_checked :
    checkReplacement table45 root6Node41Domains0 root6Node41Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node41Domains0 root6Node41Domains1
    root6Node41Domains0Fast root6Node41Domains1Fast
    root6Node41Domains0_fast_eq root6Node41Domains1_fast_eq
    root6Node41Step1Narrowing_checked (by decide)
def root6Node41Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,1)]
  | 5 => [(7,5)]
  | 6 => [(1,2)]
  | 7 => [(7,4)]
  | 8 => [(1,3)]
  | 9 => [(8,2)]
  | 10 => [(8,0)]
  | 11 => [(7,3)]
  | 12 => [(4,2)]
  | 13 => [(0,3)]
  | 14 => [(8,1)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(6,4)]
  | 19 => [(1,2)]
  | 20 => [(7,4)]
  | 21 => [(4,2)]
  | 22 => [(5,3)]
  | 23 => [(5,5)]
  | 24 => [(7,0)]
  | 25 => [(4,3)]
  | 26 => [(3,5)]
  | 27 => [(0,3)]
  | 28 => [(4,1)]
  | 29 => [(0,2)]
  | 30 => [(0,4)]
  | 31 => [(1,4)]
  | 32 => [(0,5)]
  | 33 => [(4,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,4)]
  | 37 => [(1,3)]
  | 38 => [(5,2)]
  | 39 => [(4,0),(8,0)]
  | 40 => [(3,0)]
  | 41 => [(2,5)]
  | 42 => [(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(6,5)]
  | 48 => [(0,4)]
  | 49 => [(5,4)]
  | 50 => [(0,1),(1,4)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(7,0)]
  | 59 => [(4,3)]
  | 60 => [(7,5),(8,5)]
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
  | 76 => [(8,1)]
  | 77 => [(0,2),(6,5)]
  | 78 => [(1,3)]
  | 79 => [(8,2)]
  | 80 => [(5,0)]
  | 81 => [(4,5)]
  | 82 => [(7,0)]
  | 83 => [(8,3)]
  | 84 => [(5,2),(8,5)]
  | 85 => [(0,4)]
  | 86 => [(5,4)]
  | 87 => [(0,0)]
  | 88 => [(7,2)]
  | 89 => [(0,1),(7,4)]
  | _ => [(6,2),(6,3)]
def root6Node41Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3)]
  | 9 => some [(8,2)]
  | 10 => some [(8,0)]
  | 11 => some [(7,3)]
  | 12 => some [(4,2)]
  | 13 => some [(0,3)]
  | 14 => some [(8,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(6,4)]
  | 19 => some [(1,2)]
  | 20 => some [(7,4)]
  | 21 => some [(4,2)]
  | 22 => some [(5,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(4,3)]
  | 26 => some [(3,5)]
  | 27 => some [(0,3)]
  | 28 => some [(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(0,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,4)]
  | 37 => some [(1,3)]
  | 38 => some [(5,2)]
  | 39 => some [(4,0),(8,0)]
  | 40 => some [(3,0)]
  | 41 => some [(2,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(5,4)]
  | 50 => some [(0,1),(1,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(4,3)]
  | 60 => some [(7,5),(8,5)]
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
  | 76 => some [(8,1)]
  | 77 => some [(0,2),(6,5)]
  | 78 => some [(1,3)]
  | 79 => some [(8,2)]
  | 80 => some [(5,0)]
  | 81 => some [(4,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(5,2),(8,5)]
  | 85 => some [(0,4)]
  | 86 => some [(5,4)]
  | 87 => some [(0,0)]
  | 88 => some [(7,2)]
  | 89 => some [(0,1),(7,4)]
  | _ => some [(6,2),(6,3)]
theorem root6Node41Domains2_fast_eq : root6Node41Domains2 = expandDomains root6Node41Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node41Domains2 v = expandDomains root6Node41Domains2Fast v from by decide) v
theorem root6Node41Step2Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq (by decide)
theorem root6Node41Step2Narrowing_checked :
    checkNarrowing table54 root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root6Node41Domains1 root6Node41Domains2 (by
      simp only [List.all_cons, List.all_nil, root6Node41Step2Chunk0_0_checked, root6Node41Step2Chunk0_1_checked, root6Node41Step2Chunk0_2_checked, root6Node41Step2Chunk0_3_checked, root6Node41Step2Chunk0_4_checked, root6Node41Step2Chunk0_5_checked, root6Node41Step2Chunk1_0_checked, root6Node41Step2Chunk1_1_checked, root6Node41Step2Chunk1_2_checked, root6Node41Step2Chunk1_3_checked, root6Node41Step2Chunk1_4_checked, root6Node41Step2Chunk1_5_checked, root6Node41Step2Chunk2_0_checked, root6Node41Step2Chunk2_1_checked, root6Node41Step2Chunk2_2_checked, root6Node41Step2Chunk2_3_checked, root6Node41Step2Chunk2_4_checked, root6Node41Step2Chunk2_5_checked, root6Node41Step2Chunk3_0_checked, root6Node41Step2Chunk3_1_checked, root6Node41Step2Chunk3_2_checked, root6Node41Step2Chunk3_3_checked, root6Node41Step2Chunk3_4_checked, root6Node41Step2Chunk3_5_checked, root6Node41Step2Chunk4_0_checked, root6Node41Step2Chunk4_1_checked, root6Node41Step2Chunk4_2_checked, root6Node41Step2Chunk4_3_checked, root6Node41Step2Chunk4_4_checked, root6Node41Step2Chunk4_5_checked, root6Node41Step2Chunk5_0_checked, root6Node41Step2Chunk5_1_checked, root6Node41Step2Chunk5_2_checked, root6Node41Step2Chunk5_3_checked, root6Node41Step2Chunk5_4_checked, root6Node41Step2Chunk5_5_checked, root6Node41Step2Chunk6_0_checked, root6Node41Step2Chunk6_1_checked, root6Node41Step2Chunk6_2_checked, root6Node41Step2Chunk6_3_checked, root6Node41Step2Chunk6_4_checked, root6Node41Step2Chunk6_5_checked, root6Node41Step2Chunk7_0_checked, root6Node41Step2Chunk7_1_checked, root6Node41Step2Chunk7_2_checked, root6Node41Step2Chunk7_3_checked, root6Node41Step2Chunk7_4_checked, root6Node41Step2Chunk7_5_checked, root6Node41Step2Chunk8_0_checked, root6Node41Step2Chunk8_1_checked, root6Node41Step2Chunk8_2_checked, root6Node41Step2Chunk8_3_checked, root6Node41Step2Chunk8_4_checked, root6Node41Step2Chunk8_5_checked, Bool.true_and])
theorem root6Node41Step2_checked :
    checkReplacement table54 root6Node41Domains1 root6Node41Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root6Node41Domains1 root6Node41Domains2
    root6Node41Domains1Fast root6Node41Domains2Fast
    root6Node41Domains1_fast_eq root6Node41Domains2_fast_eq
    root6Node41Step2Narrowing_checked (by decide)
def root6Node41Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,1)]
  | 5 => [(7,5)]
  | 6 => [(1,2)]
  | 7 => [(7,4)]
  | 8 => [(1,3)]
  | 9 => [(8,2)]
  | 10 => [(8,0)]
  | 11 => [(7,3)]
  | 12 => [(4,2)]
  | 13 => [(0,3)]
  | 14 => [(8,1)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(6,4)]
  | 19 => [(1,2)]
  | 20 => [(7,4)]
  | 21 => [(4,2)]
  | 22 => [(5,3)]
  | 23 => [(5,5)]
  | 24 => [(7,0)]
  | 25 => [(4,3)]
  | 26 => [(3,5)]
  | 27 => [(0,3)]
  | 28 => [(4,1)]
  | 29 => [(0,2)]
  | 30 => [(0,4)]
  | 31 => [(1,4)]
  | 32 => [(0,5)]
  | 33 => [(4,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,4)]
  | 37 => [(1,3)]
  | 38 => [(5,2)]
  | 39 => [(8,0)]
  | 40 => [(3,0)]
  | 41 => [(2,5)]
  | 42 => [(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(6,5)]
  | 48 => [(0,4)]
  | 49 => [(5,4)]
  | 50 => [(1,4)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(7,0)]
  | 59 => [(4,3)]
  | 60 => [(7,5)]
  | 61 => [(6,1)]
  | 62 => [(5,1)]
  | 63 => [(0,1)]
  | 64 => [(6,2)]
  | 65 => [(8,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(7,4)]
  | 69 => [(1,3)]
  | 70 => [(8,3)]
  | 71 => [(8,5)]
  | 72 => [(1,0)]
  | 73 => [(7,1)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(8,1)]
  | 77 => [(6,5)]
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
def root6Node41Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3)]
  | 9 => some [(8,2)]
  | 10 => some [(8,0)]
  | 11 => some [(7,3)]
  | 12 => some [(4,2)]
  | 13 => some [(0,3)]
  | 14 => some [(8,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(6,4)]
  | 19 => some [(1,2)]
  | 20 => some [(7,4)]
  | 21 => some [(4,2)]
  | 22 => some [(5,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(4,3)]
  | 26 => some [(3,5)]
  | 27 => some [(0,3)]
  | 28 => some [(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(0,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,4)]
  | 37 => some [(1,3)]
  | 38 => some [(5,2)]
  | 39 => some [(8,0)]
  | 40 => some [(3,0)]
  | 41 => some [(2,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(5,4)]
  | 50 => some [(1,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(4,3)]
  | 60 => some [(7,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(8,1)]
  | 77 => some [(6,5)]
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
theorem root6Node41Domains3_fast_eq : root6Node41Domains3 = expandDomains root6Node41Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node41Domains3 v = expandDomains root6Node41Domains3Fast v from by decide) v
theorem root6Node41Step3Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq (by decide)
theorem root6Node41Step3Narrowing_checked :
    checkNarrowing table57 root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root6Node41Domains2 root6Node41Domains3 (by
      simp only [List.all_cons, List.all_nil, root6Node41Step3Chunk0_0_checked, root6Node41Step3Chunk0_1_checked, root6Node41Step3Chunk0_2_checked, root6Node41Step3Chunk0_3_checked, root6Node41Step3Chunk0_4_checked, root6Node41Step3Chunk0_5_checked, root6Node41Step3Chunk1_0_checked, root6Node41Step3Chunk1_1_checked, root6Node41Step3Chunk1_2_checked, root6Node41Step3Chunk1_3_checked, root6Node41Step3Chunk1_4_checked, root6Node41Step3Chunk1_5_checked, root6Node41Step3Chunk2_0_checked, root6Node41Step3Chunk2_1_checked, root6Node41Step3Chunk2_2_checked, root6Node41Step3Chunk2_3_checked, root6Node41Step3Chunk2_4_checked, root6Node41Step3Chunk2_5_checked, root6Node41Step3Chunk3_0_checked, root6Node41Step3Chunk3_1_checked, root6Node41Step3Chunk3_2_checked, root6Node41Step3Chunk3_3_checked, root6Node41Step3Chunk3_4_checked, root6Node41Step3Chunk3_5_checked, root6Node41Step3Chunk4_0_checked, root6Node41Step3Chunk4_1_checked, root6Node41Step3Chunk4_2_checked, root6Node41Step3Chunk4_3_checked, root6Node41Step3Chunk4_4_checked, root6Node41Step3Chunk4_5_checked, root6Node41Step3Chunk5_0_checked, root6Node41Step3Chunk5_1_checked, root6Node41Step3Chunk5_2_checked, root6Node41Step3Chunk5_3_checked, root6Node41Step3Chunk5_4_checked, root6Node41Step3Chunk5_5_checked, root6Node41Step3Chunk6_0_checked, root6Node41Step3Chunk6_1_checked, root6Node41Step3Chunk6_2_checked, root6Node41Step3Chunk6_3_checked, root6Node41Step3Chunk6_4_checked, root6Node41Step3Chunk6_5_checked, root6Node41Step3Chunk7_0_checked, root6Node41Step3Chunk7_1_checked, root6Node41Step3Chunk7_2_checked, root6Node41Step3Chunk7_3_checked, root6Node41Step3Chunk7_4_checked, root6Node41Step3Chunk7_5_checked, root6Node41Step3Chunk8_0_checked, root6Node41Step3Chunk8_1_checked, root6Node41Step3Chunk8_2_checked, root6Node41Step3Chunk8_3_checked, root6Node41Step3Chunk8_4_checked, root6Node41Step3Chunk8_5_checked, Bool.true_and])
theorem root6Node41Step3_checked :
    checkReplacement table57 root6Node41Domains2 root6Node41Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root6Node41Domains2 root6Node41Domains3
    root6Node41Domains2Fast root6Node41Domains3Fast
    root6Node41Domains2_fast_eq root6Node41Domains3_fast_eq
    root6Node41Step3Narrowing_checked (by decide)
theorem root6Node41Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node41Domains3 (.output 19) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
