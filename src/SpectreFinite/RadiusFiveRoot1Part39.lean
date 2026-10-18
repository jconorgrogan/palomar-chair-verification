module

public import SpectreFinite.RadiusFiveRoot1Part38
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable36
public import SpectreFinite.RadiusFiveTable46
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node95Domains0 : Domains 91 State := restrict root1Node93Domains3 4 (8,3)
def root1Node95Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,2),(5,5)]
  | 6 => some [(3,1)]
  | 7 => some [(0,1)]
  | 8 => some [(6,2)]
  | 9 => some [(8,4)]
  | 10 => some [(1,4),(6,4)]
  | 11 => some [(0,5),(1,2)]
  | 12 => some [(4,4),(8,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3),(6,0)]
  | 19 => some [(7,1),(8,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(4,2),(8,2)]
  | 27 => some [(5,0),(5,3),(8,0)]
  | 28 => some [(4,5),(7,3),(8,5)]
  | 29 => some [(4,2),(7,0)]
  | 30 => some [(7,1),(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(7,4),(8,4)]
  | 37 => some [(0,0),(6,3),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(5,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(2,1),(7,1)]
  | 47 => some [(0,2),(1,5),(7,5)]
  | 48 => some [(0,3),(1,1),(6,1)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(6,5)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(1,3),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2)]
  | 56 => some [(0,0),(4,0),(5,0),(8,0)]
  | 57 => some [(3,2),(4,5),(7,3)]
  | 58 => some [(4,0),(4,2),(7,0)]
  | 59 => some [(5,3),(7,3),(8,3)]
  | 60 => some [(5,2),(8,5)]
  | 61 => some [(1,1),(6,1),(7,1)]
  | 62 => some [(4,1),(7,5),(8,1)]
  | 63 => some [(0,2),(6,0),(6,5)]
  | 64 => some [(0,4),(1,1),(7,1)]
  | 65 => some [(1,5),(5,1),(5,4)]
  | 66 => some [(0,0),(0,1),(6,1),(6,4)]
  | 67 => some [(1,2),(5,1),(6,2),(7,2)]
  | 68 => some [(0,1),(7,4)]
  | 69 => some [(6,2),(6,3)]
  | 70 => some [(7,3),(8,3)]
  | 71 => some [(5,2),(5,5),(8,2)]
  | 72 => some [(5,0),(7,0),(8,0)]
  | 73 => some [(4,3),(4,5),(8,3)]
  | 74 => some [(1,5),(3,5),(5,5),(7,0)]
  | 75 => some [(0,3),(1,0),(6,1),(8,3)]
  | 76 => some [(2,1),(4,1),(8,5)]
  | 77 => some [(0,2),(1,0)]
  | 78 => some [(0,5),(6,2)]
  | 79 => some [(4,4),(8,4)]
  | 80 => some [(0,0),(1,4)]
  | 81 => some [(0,5),(7,2)]
  | 82 => some [(2,0),(2,4),(4,4),(7,4)]
  | 83 => some [(0,0),(1,3),(7,3)]
  | 84 => some [(3,2),(5,2),(8,2)]
  | 85 => some [(7,1)]
  | 86 => some [(1,5),(7,5)]
  | 87 => some [(6,0),(6,1)]
  | 88 => some [(3,1),(7,1),(8,1)]
  | 89 => some [(0,1),(1,5),(6,5)]
  | _ => some [(0,4),(6,1),(6,2)]
theorem root1Node95Domains0_fast_eq : root1Node95Domains0 = expandDomains root1Node95Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node95Domains0 v = expandDomains root1Node95Domains0Fast v from by decide) v
def root1Node95Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(8,3)]
  | 5 => [(5,5)]
  | 6 => [(3,1)]
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
  | 20 => [(1,5),(7,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(8,2)]
  | 27 => [(5,0),(8,0)]
  | 28 => [(4,5),(7,3)]
  | 29 => [(4,2),(7,0)]
  | 30 => [(7,1),(8,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0),(6,4)]
  | 38 => [(1,2),(7,2)]
  | 39 => [(7,4)]
  | 40 => [(5,0),(5,3)]
  | 41 => [(4,5),(5,5),(8,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(1,5),(7,5)]
  | 48 => [(0,3),(6,1)]
  | 49 => [(8,1)]
  | 50 => [(6,5)]
  | 51 => [(0,0),(0,5),(6,3)]
  | 52 => [(4,4),(7,2)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(1,3),(6,3)]
  | 55 => [(7,2),(8,2)]
  | 56 => [(4,0),(5,0),(8,0)]
  | 57 => [(4,5),(7,3)]
  | 58 => [(4,2),(7,0)]
  | 59 => [(5,3),(8,3)]
  | 60 => [(8,5)]
  | 61 => [(1,1),(6,1),(7,1)]
  | 62 => [(4,1),(7,5),(8,1)]
  | 63 => [(0,2),(6,0),(6,5)]
  | 64 => [(0,4),(1,1)]
  | 65 => [(5,1),(5,4)]
  | 66 => [(0,0),(0,1),(6,4)]
  | 67 => [(1,2),(6,2),(7,2)]
  | 68 => [(7,4)]
  | 69 => [(6,3)]
  | 70 => [(7,3),(8,3)]
  | 71 => [(5,2),(5,5),(8,2)]
  | 72 => [(5,0),(7,0),(8,0)]
  | 73 => [(4,3),(8,3)]
  | 74 => [(1,5),(3,5),(5,5)]
  | 75 => [(0,3),(1,0),(6,1)]
  | 76 => [(2,1),(4,1)]
  | 77 => [(0,2)]
  | 78 => [(0,5),(6,2)]
  | 79 => [(4,4),(8,4)]
  | 80 => [(0,0),(1,4)]
  | 81 => [(0,5),(7,2)]
  | 82 => [(2,0),(2,4),(4,4),(7,4)]
  | 83 => [(0,0),(1,3),(7,3)]
  | 84 => [(3,2),(5,2),(8,2)]
  | 85 => [(7,1)]
  | 86 => [(1,5),(7,5)]
  | 87 => [(6,0),(6,1)]
  | 88 => [(3,1),(7,1),(8,1)]
  | 89 => [(0,1),(1,5),(6,5)]
  | _ => [(0,4),(6,1),(6,2)]
def root1Node95Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(3,1)]
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
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3)]
  | 29 => some [(4,2),(7,0)]
  | 30 => some [(7,1),(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(5,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5),(7,5)]
  | 48 => some [(0,3),(6,1)]
  | 49 => some [(8,1)]
  | 50 => some [(6,5)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(4,0),(5,0),(8,0)]
  | 57 => some [(4,5),(7,3)]
  | 58 => some [(4,2),(7,0)]
  | 59 => some [(5,3),(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(1,1),(6,1),(7,1)]
  | 62 => some [(4,1),(7,5),(8,1)]
  | 63 => some [(0,2),(6,0),(6,5)]
  | 64 => some [(0,4),(1,1)]
  | 65 => some [(5,1),(5,4)]
  | 66 => some [(0,0),(0,1),(6,4)]
  | 67 => some [(1,2),(6,2),(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(7,3),(8,3)]
  | 71 => some [(5,2),(5,5),(8,2)]
  | 72 => some [(5,0),(7,0),(8,0)]
  | 73 => some [(4,3),(8,3)]
  | 74 => some [(1,5),(3,5),(5,5)]
  | 75 => some [(0,3),(1,0),(6,1)]
  | 76 => some [(2,1),(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5),(6,2)]
  | 79 => some [(4,4),(8,4)]
  | 80 => some [(0,0),(1,4)]
  | 81 => some [(0,5),(7,2)]
  | 82 => some [(2,0),(2,4),(4,4),(7,4)]
  | 83 => some [(0,0),(1,3),(7,3)]
  | 84 => some [(3,2),(5,2),(8,2)]
  | 85 => some [(7,1)]
  | 86 => some [(1,5),(7,5)]
  | 87 => some [(6,0),(6,1)]
  | 88 => some [(3,1),(7,1),(8,1)]
  | 89 => some [(0,1),(1,5),(6,5)]
  | _ => some [(0,4),(6,1),(6,2)]
theorem root1Node95Domains1_fast_eq : root1Node95Domains1 = expandDomains root1Node95Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node95Domains1 v = expandDomains root1Node95Domains1Fast v from by decide) v
theorem root1Node95Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq (by decide)
theorem root1Node95Step1Narrowing_checked :
    checkNarrowing table36 root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root1Node95Domains0 root1Node95Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node95Step1Chunk0_0_checked, root1Node95Step1Chunk0_1_checked, root1Node95Step1Chunk0_2_checked, root1Node95Step1Chunk0_3_checked, root1Node95Step1Chunk0_4_checked, root1Node95Step1Chunk0_5_checked, root1Node95Step1Chunk1_0_checked, root1Node95Step1Chunk1_1_checked, root1Node95Step1Chunk1_2_checked, root1Node95Step1Chunk1_3_checked, root1Node95Step1Chunk1_4_checked, root1Node95Step1Chunk1_5_checked, root1Node95Step1Chunk2_0_checked, root1Node95Step1Chunk2_1_checked, root1Node95Step1Chunk2_2_checked, root1Node95Step1Chunk2_3_checked, root1Node95Step1Chunk2_4_checked, root1Node95Step1Chunk2_5_checked, root1Node95Step1Chunk3_0_checked, root1Node95Step1Chunk3_1_checked, root1Node95Step1Chunk3_2_checked, root1Node95Step1Chunk3_3_checked, root1Node95Step1Chunk3_4_checked, root1Node95Step1Chunk3_5_checked, root1Node95Step1Chunk4_0_checked, root1Node95Step1Chunk4_1_checked, root1Node95Step1Chunk4_2_checked, root1Node95Step1Chunk4_3_checked, root1Node95Step1Chunk4_4_checked, root1Node95Step1Chunk4_5_checked, root1Node95Step1Chunk5_0_checked, root1Node95Step1Chunk5_1_checked, root1Node95Step1Chunk5_2_checked, root1Node95Step1Chunk5_3_checked, root1Node95Step1Chunk5_4_checked, root1Node95Step1Chunk5_5_checked, root1Node95Step1Chunk6_0_checked, root1Node95Step1Chunk6_1_checked, root1Node95Step1Chunk6_2_checked, root1Node95Step1Chunk6_3_checked, root1Node95Step1Chunk6_4_checked, root1Node95Step1Chunk6_5_checked, root1Node95Step1Chunk7_0_checked, root1Node95Step1Chunk7_1_checked, root1Node95Step1Chunk7_2_checked, root1Node95Step1Chunk7_3_checked, root1Node95Step1Chunk7_4_checked, root1Node95Step1Chunk7_5_checked, root1Node95Step1Chunk8_0_checked, root1Node95Step1Chunk8_1_checked, root1Node95Step1Chunk8_2_checked, root1Node95Step1Chunk8_3_checked, root1Node95Step1Chunk8_4_checked, root1Node95Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node95Step1_checked :
    checkReplacement table36 root1Node95Domains0 root1Node95Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node95Domains0 root1Node95Domains1
    root1Node95Domains0Fast root1Node95Domains1Fast
    root1Node95Domains0_fast_eq root1Node95Domains1_fast_eq
    root1Node95Step1Narrowing_checked (by decide)
def root1Node95Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(8,3)]
  | 5 => [(5,5)]
  | 6 => [(3,1)]
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
  | 20 => [(1,5),(7,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(8,2)]
  | 27 => [(5,0),(8,0)]
  | 28 => [(4,5),(7,3)]
  | 29 => [(4,2),(7,0)]
  | 30 => [(7,1),(8,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0),(6,4)]
  | 38 => [(1,2),(7,2)]
  | 39 => [(7,4)]
  | 40 => [(5,0),(5,3)]
  | 41 => [(4,5),(8,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(1,5),(7,5)]
  | 48 => [(0,3),(6,1)]
  | 49 => [(8,1)]
  | 50 => [(6,5)]
  | 51 => [(0,0),(6,3)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3),(6,3)]
  | 55 => [(7,2),(8,2)]
  | 56 => [(4,0),(5,0),(8,0)]
  | 57 => [(4,5),(7,3)]
  | 58 => [(4,2),(7,0)]
  | 59 => [(5,3),(8,3)]
  | 60 => [(8,5)]
  | 61 => [(1,1),(6,1)]
  | 62 => [(4,1),(8,1)]
  | 63 => [(0,2),(6,5)]
  | 64 => [(0,4),(1,1)]
  | 65 => [(5,1),(5,4)]
  | 66 => [(0,0),(0,1),(6,4)]
  | 67 => [(1,2),(6,2),(7,2)]
  | 68 => [(7,4)]
  | 69 => [(6,3)]
  | 70 => [(7,3),(8,3)]
  | 71 => [(5,2),(5,5)]
  | 72 => [(7,0),(8,0)]
  | 73 => [(4,3),(8,3)]
  | 74 => [(1,5),(3,5),(5,5)]
  | 75 => [(0,3),(1,0),(6,1)]
  | 76 => [(2,1),(4,1)]
  | 77 => [(0,2)]
  | 78 => [(0,5),(6,2)]
  | 79 => [(4,4),(8,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(2,0),(2,4),(4,4)]
  | 83 => [(0,0),(1,3),(7,3)]
  | 84 => [(3,2),(5,2),(8,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(3,1),(7,1)]
  | 89 => [(0,1),(1,5),(6,5)]
  | _ => [(0,4),(6,1),(6,2)]
def root1Node95Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(3,1)]
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
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3)]
  | 29 => some [(4,2),(7,0)]
  | 30 => some [(7,1),(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5),(7,5)]
  | 48 => some [(0,3),(6,1)]
  | 49 => some [(8,1)]
  | 50 => some [(6,5)]
  | 51 => some [(0,0),(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(4,0),(5,0),(8,0)]
  | 57 => some [(4,5),(7,3)]
  | 58 => some [(4,2),(7,0)]
  | 59 => some [(5,3),(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(1,1),(6,1)]
  | 62 => some [(4,1),(8,1)]
  | 63 => some [(0,2),(6,5)]
  | 64 => some [(0,4),(1,1)]
  | 65 => some [(5,1),(5,4)]
  | 66 => some [(0,0),(0,1),(6,4)]
  | 67 => some [(1,2),(6,2),(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(7,3),(8,3)]
  | 71 => some [(5,2),(5,5)]
  | 72 => some [(7,0),(8,0)]
  | 73 => some [(4,3),(8,3)]
  | 74 => some [(1,5),(3,5),(5,5)]
  | 75 => some [(0,3),(1,0),(6,1)]
  | 76 => some [(2,1),(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5),(6,2)]
  | 79 => some [(4,4),(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(2,0),(2,4),(4,4)]
  | 83 => some [(0,0),(1,3),(7,3)]
  | 84 => some [(3,2),(5,2),(8,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(3,1),(7,1)]
  | 89 => some [(0,1),(1,5),(6,5)]
  | _ => some [(0,4),(6,1),(6,2)]
theorem root1Node95Domains2_fast_eq : root1Node95Domains2 = expandDomains root1Node95Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node95Domains2 v = expandDomains root1Node95Domains2Fast v from by decide) v
theorem root1Node95Step2Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq (by decide)
theorem root1Node95Step2Narrowing_checked :
    checkNarrowing table54 root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root1Node95Domains1 root1Node95Domains2 (by
      simp only [List.all_cons, List.all_nil, root1Node95Step2Chunk0_0_checked, root1Node95Step2Chunk0_1_checked, root1Node95Step2Chunk0_2_checked, root1Node95Step2Chunk0_3_checked, root1Node95Step2Chunk0_4_checked, root1Node95Step2Chunk0_5_checked, root1Node95Step2Chunk1_0_checked, root1Node95Step2Chunk1_1_checked, root1Node95Step2Chunk1_2_checked, root1Node95Step2Chunk1_3_checked, root1Node95Step2Chunk1_4_checked, root1Node95Step2Chunk1_5_checked, root1Node95Step2Chunk2_0_checked, root1Node95Step2Chunk2_1_checked, root1Node95Step2Chunk2_2_checked, root1Node95Step2Chunk2_3_checked, root1Node95Step2Chunk2_4_checked, root1Node95Step2Chunk2_5_checked, root1Node95Step2Chunk3_0_checked, root1Node95Step2Chunk3_1_checked, root1Node95Step2Chunk3_2_checked, root1Node95Step2Chunk3_3_checked, root1Node95Step2Chunk3_4_checked, root1Node95Step2Chunk3_5_checked, root1Node95Step2Chunk4_0_checked, root1Node95Step2Chunk4_1_checked, root1Node95Step2Chunk4_2_checked, root1Node95Step2Chunk4_3_checked, root1Node95Step2Chunk4_4_checked, root1Node95Step2Chunk4_5_checked, root1Node95Step2Chunk5_0_checked, root1Node95Step2Chunk5_1_checked, root1Node95Step2Chunk5_2_checked, root1Node95Step2Chunk5_3_checked, root1Node95Step2Chunk5_4_checked, root1Node95Step2Chunk5_5_checked, root1Node95Step2Chunk6_0_checked, root1Node95Step2Chunk6_1_checked, root1Node95Step2Chunk6_2_checked, root1Node95Step2Chunk6_3_checked, root1Node95Step2Chunk6_4_checked, root1Node95Step2Chunk6_5_checked, root1Node95Step2Chunk7_0_checked, root1Node95Step2Chunk7_1_checked, root1Node95Step2Chunk7_2_checked, root1Node95Step2Chunk7_3_checked, root1Node95Step2Chunk7_4_checked, root1Node95Step2Chunk7_5_checked, root1Node95Step2Chunk8_0_checked, root1Node95Step2Chunk8_1_checked, root1Node95Step2Chunk8_2_checked, root1Node95Step2Chunk8_3_checked, root1Node95Step2Chunk8_4_checked, root1Node95Step2Chunk8_5_checked, Bool.true_and])
theorem root1Node95Step2_checked :
    checkReplacement table54 root1Node95Domains1 root1Node95Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root1Node95Domains1 root1Node95Domains2
    root1Node95Domains1Fast root1Node95Domains2Fast
    root1Node95Domains1_fast_eq root1Node95Domains2_fast_eq
    root1Node95Step2Narrowing_checked (by decide)
def root1Node95Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(8,3)]
  | 5 => [(5,5)]
  | 6 => [(3,1)]
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
  | 20 => [(1,5),(7,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(8,2)]
  | 27 => [(5,0),(8,0)]
  | 28 => [(4,5),(7,3)]
  | 29 => [(4,2),(7,0)]
  | 30 => [(7,1),(8,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0),(6,4)]
  | 38 => [(1,2),(7,2)]
  | 39 => [(7,4)]
  | 40 => [(5,0),(5,3)]
  | 41 => [(4,5),(8,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(1,5),(7,5)]
  | 48 => [(0,3),(6,1)]
  | 49 => [(8,1)]
  | 50 => [(6,5)]
  | 51 => [(0,0),(6,3)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3),(6,3)]
  | 55 => [(7,2),(8,2)]
  | 56 => [(4,0),(5,0),(8,0)]
  | 57 => [(4,5),(7,3)]
  | 58 => [(4,2),(7,0)]
  | 59 => [(5,3),(8,3)]
  | 60 => [(8,5)]
  | 61 => [(1,1),(6,1)]
  | 62 => [(4,1),(8,1)]
  | 63 => [(0,2),(6,5)]
  | 64 => [(0,4),(1,1)]
  | 65 => [(5,1),(5,4)]
  | 66 => [(0,0),(0,1),(6,4)]
  | 67 => [(1,2),(6,2),(7,2)]
  | 68 => [(7,4)]
  | 69 => [(6,3)]
  | 70 => [(7,3),(8,3)]
  | 71 => [(5,2),(5,5)]
  | 72 => [(7,0),(8,0)]
  | 73 => [(4,3),(8,3)]
  | 74 => [(1,5),(3,5),(5,5)]
  | 75 => [(0,3),(1,0),(6,1)]
  | 76 => [(2,1),(4,1)]
  | 77 => [(0,2)]
  | 78 => [(0,5),(6,2)]
  | 79 => [(4,4),(8,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(2,0),(2,4),(4,4)]
  | 83 => [(0,0),(1,3),(7,3)]
  | 84 => [(3,2),(5,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(3,1),(7,1)]
  | 89 => [(0,1),(1,5),(6,5)]
  | _ => [(0,4),(6,1),(6,2)]
def root1Node95Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(3,1)]
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
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3)]
  | 29 => some [(4,2),(7,0)]
  | 30 => some [(7,1),(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5),(7,5)]
  | 48 => some [(0,3),(6,1)]
  | 49 => some [(8,1)]
  | 50 => some [(6,5)]
  | 51 => some [(0,0),(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(4,0),(5,0),(8,0)]
  | 57 => some [(4,5),(7,3)]
  | 58 => some [(4,2),(7,0)]
  | 59 => some [(5,3),(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(1,1),(6,1)]
  | 62 => some [(4,1),(8,1)]
  | 63 => some [(0,2),(6,5)]
  | 64 => some [(0,4),(1,1)]
  | 65 => some [(5,1),(5,4)]
  | 66 => some [(0,0),(0,1),(6,4)]
  | 67 => some [(1,2),(6,2),(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(7,3),(8,3)]
  | 71 => some [(5,2),(5,5)]
  | 72 => some [(7,0),(8,0)]
  | 73 => some [(4,3),(8,3)]
  | 74 => some [(1,5),(3,5),(5,5)]
  | 75 => some [(0,3),(1,0),(6,1)]
  | 76 => some [(2,1),(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5),(6,2)]
  | 79 => some [(4,4),(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(2,0),(2,4),(4,4)]
  | 83 => some [(0,0),(1,3),(7,3)]
  | 84 => some [(3,2),(5,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(3,1),(7,1)]
  | 89 => some [(0,1),(1,5),(6,5)]
  | _ => some [(0,4),(6,1),(6,2)]
theorem root1Node95Domains3_fast_eq : root1Node95Domains3 = expandDomains root1Node95Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node95Domains3 v = expandDomains root1Node95Domains3Fast v from by decide) v
theorem root1Node95Step3Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq (by decide)
theorem root1Node95Step3Narrowing_checked :
    checkNarrowing table46 root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkNarrowing_flatten table46Scope [table46Rows0_0,table46Rows0_1,table46Rows0_2,table46Rows0_3,table46Rows0_4,table46Rows0_5,table46Rows1_0,table46Rows1_1,table46Rows1_2,table46Rows1_3,table46Rows1_4,table46Rows1_5,table46Rows2_0,table46Rows2_1,table46Rows2_2,table46Rows2_3,table46Rows2_4,table46Rows2_5,table46Rows3_0,table46Rows3_1,table46Rows3_2,table46Rows3_3,table46Rows3_4,table46Rows3_5,table46Rows4_0,table46Rows4_1,table46Rows4_2,table46Rows4_3,table46Rows4_4,table46Rows4_5,table46Rows5_0,table46Rows5_1,table46Rows5_2,table46Rows5_3,table46Rows5_4,table46Rows5_5,table46Rows6_0,table46Rows6_1,table46Rows6_2,table46Rows6_3,table46Rows6_4,table46Rows6_5,table46Rows7_0,table46Rows7_1,table46Rows7_2,table46Rows7_3,table46Rows7_4,table46Rows7_5,table46Rows8_0,table46Rows8_1,table46Rows8_2,table46Rows8_3,table46Rows8_4,table46Rows8_5]
    root1Node95Domains2 root1Node95Domains3 (by
      simp only [List.all_cons, List.all_nil, root1Node95Step3Chunk0_0_checked, root1Node95Step3Chunk0_1_checked, root1Node95Step3Chunk0_2_checked, root1Node95Step3Chunk0_3_checked, root1Node95Step3Chunk0_4_checked, root1Node95Step3Chunk0_5_checked, root1Node95Step3Chunk1_0_checked, root1Node95Step3Chunk1_1_checked, root1Node95Step3Chunk1_2_checked, root1Node95Step3Chunk1_3_checked, root1Node95Step3Chunk1_4_checked, root1Node95Step3Chunk1_5_checked, root1Node95Step3Chunk2_0_checked, root1Node95Step3Chunk2_1_checked, root1Node95Step3Chunk2_2_checked, root1Node95Step3Chunk2_3_checked, root1Node95Step3Chunk2_4_checked, root1Node95Step3Chunk2_5_checked, root1Node95Step3Chunk3_0_checked, root1Node95Step3Chunk3_1_checked, root1Node95Step3Chunk3_2_checked, root1Node95Step3Chunk3_3_checked, root1Node95Step3Chunk3_4_checked, root1Node95Step3Chunk3_5_checked, root1Node95Step3Chunk4_0_checked, root1Node95Step3Chunk4_1_checked, root1Node95Step3Chunk4_2_checked, root1Node95Step3Chunk4_3_checked, root1Node95Step3Chunk4_4_checked, root1Node95Step3Chunk4_5_checked, root1Node95Step3Chunk5_0_checked, root1Node95Step3Chunk5_1_checked, root1Node95Step3Chunk5_2_checked, root1Node95Step3Chunk5_3_checked, root1Node95Step3Chunk5_4_checked, root1Node95Step3Chunk5_5_checked, root1Node95Step3Chunk6_0_checked, root1Node95Step3Chunk6_1_checked, root1Node95Step3Chunk6_2_checked, root1Node95Step3Chunk6_3_checked, root1Node95Step3Chunk6_4_checked, root1Node95Step3Chunk6_5_checked, root1Node95Step3Chunk7_0_checked, root1Node95Step3Chunk7_1_checked, root1Node95Step3Chunk7_2_checked, root1Node95Step3Chunk7_3_checked, root1Node95Step3Chunk7_4_checked, root1Node95Step3Chunk7_5_checked, root1Node95Step3Chunk8_0_checked, root1Node95Step3Chunk8_1_checked, root1Node95Step3Chunk8_2_checked, root1Node95Step3Chunk8_3_checked, root1Node95Step3Chunk8_4_checked, root1Node95Step3Chunk8_5_checked, Bool.true_and])
theorem root1Node95Step3_checked :
    checkReplacement table46 root1Node95Domains2 root1Node95Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root1Node95Domains2 root1Node95Domains3
    root1Node95Domains2Fast root1Node95Domains3Fast
    root1Node95Domains2_fast_eq root1Node95Domains3_fast_eq
    root1Node95Step3Narrowing_checked (by decide)
def root1Node96Domains0 : Domains 91 State := restrict root1Node95Domains3 20 (1,5)
def root1Node96Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(3,1)]
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
  | 20 => some [(1,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3)]
  | 29 => some [(4,2),(7,0)]
  | 30 => some [(7,1),(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5),(7,5)]
  | 48 => some [(0,3),(6,1)]
  | 49 => some [(8,1)]
  | 50 => some [(6,5)]
  | 51 => some [(0,0),(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(4,0),(5,0),(8,0)]
  | 57 => some [(4,5),(7,3)]
  | 58 => some [(4,2),(7,0)]
  | 59 => some [(5,3),(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(1,1),(6,1)]
  | 62 => some [(4,1),(8,1)]
  | 63 => some [(0,2),(6,5)]
  | 64 => some [(0,4),(1,1)]
  | 65 => some [(5,1),(5,4)]
  | 66 => some [(0,0),(0,1),(6,4)]
  | 67 => some [(1,2),(6,2),(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(7,3),(8,3)]
  | 71 => some [(5,2),(5,5)]
  | 72 => some [(7,0),(8,0)]
  | 73 => some [(4,3),(8,3)]
  | 74 => some [(1,5),(3,5),(5,5)]
  | 75 => some [(0,3),(1,0),(6,1)]
  | 76 => some [(2,1),(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5),(6,2)]
  | 79 => some [(4,4),(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(2,0),(2,4),(4,4)]
  | 83 => some [(0,0),(1,3),(7,3)]
  | 84 => some [(3,2),(5,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(3,1),(7,1)]
  | 89 => some [(0,1),(1,5),(6,5)]
  | _ => some [(0,4),(6,1),(6,2)]
theorem root1Node96Domains0_fast_eq : root1Node96Domains0 = expandDomains root1Node96Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node96Domains0 v = expandDomains root1Node96Domains0Fast v from by decide) v
def root1Node96Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(8,3)]
  | 5 => [(5,5)]
  | 6 => [(3,1)]
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
  | 20 => [(1,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(8,2)]
  | 27 => [(5,0)]
  | 28 => [(4,5)]
  | 29 => [(7,0)]
  | 30 => [(7,1),(8,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(5,0),(5,3)]
  | 41 => [(4,5),(8,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(1,5)]
  | 48 => [(6,1)]
  | 49 => [(8,1)]
  | 50 => [(6,5)]
  | 51 => [(0,0),(6,3)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(7,0)]
  | 59 => [(8,3)]
  | 60 => [(8,5)]
  | 61 => [(1,1),(6,1)]
  | 62 => [(4,1),(8,1)]
  | 63 => [(6,5)]
  | 64 => [(0,4)]
  | 65 => [(5,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(7,4)]
  | 69 => [(6,3)]
  | 70 => [(7,3),(8,3)]
  | 71 => [(5,2),(5,5)]
  | 72 => [(7,0)]
  | 73 => [(4,3)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(4,1)]
  | 77 => [(0,2)]
  | 78 => [(0,5),(6,2)]
  | 79 => [(4,4),(8,4)]
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
def root1Node96Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(3,1)]
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
  | 20 => some [(1,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0)]
  | 28 => some [(4,5)]
  | 29 => some [(7,0)]
  | 30 => some [(7,1),(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(8,1)]
  | 50 => some [(6,5)]
  | 51 => some [(0,0),(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(1,1),(6,1)]
  | 62 => some [(4,1),(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(7,3),(8,3)]
  | 71 => some [(5,2),(5,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5),(6,2)]
  | 79 => some [(4,4),(8,4)]
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
theorem root1Node96Domains1_fast_eq : root1Node96Domains1 = expandDomains root1Node96Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node96Domains1 v = expandDomains root1Node96Domains1Fast v from by decide) v
theorem root1Node96Step1Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq (by decide)
theorem root1Node96Step1Narrowing_checked :
    checkNarrowing table57 root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root1Node96Domains0 root1Node96Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node96Step1Chunk0_0_checked, root1Node96Step1Chunk0_1_checked, root1Node96Step1Chunk0_2_checked, root1Node96Step1Chunk0_3_checked, root1Node96Step1Chunk0_4_checked, root1Node96Step1Chunk0_5_checked, root1Node96Step1Chunk1_0_checked, root1Node96Step1Chunk1_1_checked, root1Node96Step1Chunk1_2_checked, root1Node96Step1Chunk1_3_checked, root1Node96Step1Chunk1_4_checked, root1Node96Step1Chunk1_5_checked, root1Node96Step1Chunk2_0_checked, root1Node96Step1Chunk2_1_checked, root1Node96Step1Chunk2_2_checked, root1Node96Step1Chunk2_3_checked, root1Node96Step1Chunk2_4_checked, root1Node96Step1Chunk2_5_checked, root1Node96Step1Chunk3_0_checked, root1Node96Step1Chunk3_1_checked, root1Node96Step1Chunk3_2_checked, root1Node96Step1Chunk3_3_checked, root1Node96Step1Chunk3_4_checked, root1Node96Step1Chunk3_5_checked, root1Node96Step1Chunk4_0_checked, root1Node96Step1Chunk4_1_checked, root1Node96Step1Chunk4_2_checked, root1Node96Step1Chunk4_3_checked, root1Node96Step1Chunk4_4_checked, root1Node96Step1Chunk4_5_checked, root1Node96Step1Chunk5_0_checked, root1Node96Step1Chunk5_1_checked, root1Node96Step1Chunk5_2_checked, root1Node96Step1Chunk5_3_checked, root1Node96Step1Chunk5_4_checked, root1Node96Step1Chunk5_5_checked, root1Node96Step1Chunk6_0_checked, root1Node96Step1Chunk6_1_checked, root1Node96Step1Chunk6_2_checked, root1Node96Step1Chunk6_3_checked, root1Node96Step1Chunk6_4_checked, root1Node96Step1Chunk6_5_checked, root1Node96Step1Chunk7_0_checked, root1Node96Step1Chunk7_1_checked, root1Node96Step1Chunk7_2_checked, root1Node96Step1Chunk7_3_checked, root1Node96Step1Chunk7_4_checked, root1Node96Step1Chunk7_5_checked, root1Node96Step1Chunk8_0_checked, root1Node96Step1Chunk8_1_checked, root1Node96Step1Chunk8_2_checked, root1Node96Step1Chunk8_3_checked, root1Node96Step1Chunk8_4_checked, root1Node96Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node96Step1_checked :
    checkReplacement table57 root1Node96Domains0 root1Node96Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node96Domains0 root1Node96Domains1
    root1Node96Domains0Fast root1Node96Domains1Fast
    root1Node96Domains0_fast_eq root1Node96Domains1_fast_eq
    root1Node96Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
