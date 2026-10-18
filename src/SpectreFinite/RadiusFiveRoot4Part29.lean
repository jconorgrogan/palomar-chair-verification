module

public import SpectreFinite.RadiusFiveRoot4Part28
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable0
public import SpectreFinite.RadiusFiveTable12
public import SpectreFinite.RadiusFiveTable65

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node74Domains0 : Domains 91 State := restrict root4Node73Domains0 73 (1,3)
def root4Node74Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 40 => some [(6,4)]
  | 41 => some [(1,2)]
  | 42 => some [(8,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3)]
  | 50 => some [(8,2)]
  | 51 => some [(0,3)]
  | 52 => some [(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(5,3)]
  | 62 => some [(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(7,2),(8,2)]
  | 75 => some [(4,0),(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(1,1)]
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
theorem root4Node74Domains0_fast_eq : root4Node74Domains0 = expandDomains root4Node74Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node74Domains0 v = expandDomains root4Node74Domains0Fast v from by decide) v
def root4Node74Domains1 (v : Fin 91) : List State :=
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
  | 40 => [(6,4)]
  | 41 => [(1,2)]
  | 42 => [(8,4)]
  | 43 => [(0,0)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(8,0)]
  | 49 => [(7,3)]
  | 50 => [(8,2)]
  | 51 => [(0,3)]
  | 52 => [(8,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(6,4)]
  | 60 => [(1,2)]
  | 61 => [(5,3)]
  | 62 => [(8,5)]
  | 63 => [(7,0)]
  | 64 => [(8,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(0,3)]
  | 70 => [(6,3)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(8,2)]
  | 75 => [(8,0)]
  | 76 => [(7,3)]
  | 77 => [(4,2)]
  | 78 => [(1,1)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(5,4)]
  | 83 => [(6,4)]
  | 84 => [(1,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5)]
  | 87 => [(7,0)]
  | 88 => [(4,3)]
  | 89 => [(3,5)]
  | _ => [(0,3)]
def root4Node74Domains1Fast (v : Fin 91) : Option (List State) :=
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
  | 40 => some [(6,4)]
  | 41 => some [(1,2)]
  | 42 => some [(8,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3)]
  | 50 => some [(8,2)]
  | 51 => some [(0,3)]
  | 52 => some [(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(5,3)]
  | 62 => some [(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(1,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(3,5)]
  | _ => some [(0,3)]
theorem root4Node74Domains1_fast_eq : root4Node74Domains1 = expandDomains root4Node74Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node74Domains1 v = expandDomains root4Node74Domains1Fast v from by decide) v
theorem root4Node74Step1Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq (by decide)
theorem root4Node74Step1Narrowing_checked :
    checkNarrowing table65 root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root4Node74Domains0 root4Node74Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node74Step1Chunk0_0_checked, root4Node74Step1Chunk0_1_checked, root4Node74Step1Chunk0_2_checked, root4Node74Step1Chunk0_3_checked, root4Node74Step1Chunk0_4_checked, root4Node74Step1Chunk0_5_checked, root4Node74Step1Chunk1_0_checked, root4Node74Step1Chunk1_1_checked, root4Node74Step1Chunk1_2_checked, root4Node74Step1Chunk1_3_checked, root4Node74Step1Chunk1_4_checked, root4Node74Step1Chunk1_5_checked, root4Node74Step1Chunk2_0_checked, root4Node74Step1Chunk2_1_checked, root4Node74Step1Chunk2_2_checked, root4Node74Step1Chunk2_3_checked, root4Node74Step1Chunk2_4_checked, root4Node74Step1Chunk2_5_checked, root4Node74Step1Chunk3_0_checked, root4Node74Step1Chunk3_1_checked, root4Node74Step1Chunk3_2_checked, root4Node74Step1Chunk3_3_checked, root4Node74Step1Chunk3_4_checked, root4Node74Step1Chunk3_5_checked, root4Node74Step1Chunk4_0_checked, root4Node74Step1Chunk4_1_checked, root4Node74Step1Chunk4_2_checked, root4Node74Step1Chunk4_3_checked, root4Node74Step1Chunk4_4_checked, root4Node74Step1Chunk4_5_checked, root4Node74Step1Chunk5_0_checked, root4Node74Step1Chunk5_1_checked, root4Node74Step1Chunk5_2_checked, root4Node74Step1Chunk5_3_checked, root4Node74Step1Chunk5_4_checked, root4Node74Step1Chunk5_5_checked, root4Node74Step1Chunk6_0_checked, root4Node74Step1Chunk6_1_checked, root4Node74Step1Chunk6_2_checked, root4Node74Step1Chunk6_3_checked, root4Node74Step1Chunk6_4_checked, root4Node74Step1Chunk6_5_checked, root4Node74Step1Chunk7_0_checked, root4Node74Step1Chunk7_1_checked, root4Node74Step1Chunk7_2_checked, root4Node74Step1Chunk7_3_checked, root4Node74Step1Chunk7_4_checked, root4Node74Step1Chunk7_5_checked, root4Node74Step1Chunk8_0_checked, root4Node74Step1Chunk8_1_checked, root4Node74Step1Chunk8_2_checked, root4Node74Step1Chunk8_3_checked, root4Node74Step1Chunk8_4_checked, root4Node74Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node74Step1_checked :
    checkReplacement table65 root4Node74Domains0 root4Node74Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node74Domains0 root4Node74Domains1
    root4Node74Domains0Fast root4Node74Domains1Fast
    root4Node74Domains0_fast_eq root4Node74Domains1_fast_eq
    root4Node74Step1Narrowing_checked (by decide)
theorem root4Node74Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node74Domains1 (.output 36) = true := by decide
def root4Node75Domains0 : Domains 91 State := restrict root4Node73Domains0 73 (6,3)
def root4Node75Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 40 => some [(6,4)]
  | 41 => some [(1,2)]
  | 42 => some [(8,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3)]
  | 50 => some [(8,2)]
  | 51 => some [(0,3)]
  | 52 => some [(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(5,3)]
  | 62 => some [(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(6,3)]
  | 74 => some [(7,2),(8,2)]
  | 75 => some [(4,0),(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(1,1)]
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
theorem root4Node75Domains0_fast_eq : root4Node75Domains0 = expandDomains root4Node75Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node75Domains0 v = expandDomains root4Node75Domains0Fast v from by decide) v
def root4Node75Domains1 (v : Fin 91) : List State :=
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
  | 40 => [(6,4)]
  | 41 => [(1,2)]
  | 42 => [(8,4)]
  | 43 => [(0,0)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(8,0)]
  | 49 => [(7,3)]
  | 50 => [(8,2)]
  | 51 => [(0,3)]
  | 52 => [(8,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(6,4)]
  | 60 => [(1,2)]
  | 61 => [(5,3)]
  | 62 => [(8,5)]
  | 63 => [(7,0)]
  | 64 => [(8,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(0,3)]
  | 70 => [(6,3)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(6,3)]
  | 74 => [(7,2)]
  | 75 => [(4,0)]
  | 76 => [(7,3)]
  | 77 => [(4,2)]
  | 78 => [(1,1)]
  | 79 => [(4,1)]
  | 80 => [(0,2)]
  | 81 => [(1,1)]
  | 82 => [(5,1)]
  | 83 => [(0,1)]
  | 84 => [(6,2)]
  | 85 => [(7,3)]
  | 86 => [(5,2)]
  | 87 => [(8,0)]
  | 88 => [(8,3)]
  | 89 => [(5,5)]
  | _ => [(1,0)]
def root4Node75Domains1Fast (v : Fin 91) : Option (List State) :=
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
  | 40 => some [(6,4)]
  | 41 => some [(1,2)]
  | 42 => some [(8,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3)]
  | 50 => some [(8,2)]
  | 51 => some [(0,3)]
  | 52 => some [(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(5,3)]
  | 62 => some [(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(6,3)]
  | 74 => some [(7,2)]
  | 75 => some [(4,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(1,1)]
  | 79 => some [(4,1)]
  | 80 => some [(0,2)]
  | 81 => some [(1,1)]
  | 82 => some [(5,1)]
  | 83 => some [(0,1)]
  | 84 => some [(6,2)]
  | 85 => some [(7,3)]
  | 86 => some [(5,2)]
  | 87 => some [(8,0)]
  | 88 => some [(8,3)]
  | 89 => some [(5,5)]
  | _ => some [(1,0)]
theorem root4Node75Domains1_fast_eq : root4Node75Domains1 = expandDomains root4Node75Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node75Domains1 v = expandDomains root4Node75Domains1Fast v from by decide) v
theorem root4Node75Step1Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq (by decide)
theorem root4Node75Step1Narrowing_checked :
    checkNarrowing table65 root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root4Node75Domains0 root4Node75Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node75Step1Chunk0_0_checked, root4Node75Step1Chunk0_1_checked, root4Node75Step1Chunk0_2_checked, root4Node75Step1Chunk0_3_checked, root4Node75Step1Chunk0_4_checked, root4Node75Step1Chunk0_5_checked, root4Node75Step1Chunk1_0_checked, root4Node75Step1Chunk1_1_checked, root4Node75Step1Chunk1_2_checked, root4Node75Step1Chunk1_3_checked, root4Node75Step1Chunk1_4_checked, root4Node75Step1Chunk1_5_checked, root4Node75Step1Chunk2_0_checked, root4Node75Step1Chunk2_1_checked, root4Node75Step1Chunk2_2_checked, root4Node75Step1Chunk2_3_checked, root4Node75Step1Chunk2_4_checked, root4Node75Step1Chunk2_5_checked, root4Node75Step1Chunk3_0_checked, root4Node75Step1Chunk3_1_checked, root4Node75Step1Chunk3_2_checked, root4Node75Step1Chunk3_3_checked, root4Node75Step1Chunk3_4_checked, root4Node75Step1Chunk3_5_checked, root4Node75Step1Chunk4_0_checked, root4Node75Step1Chunk4_1_checked, root4Node75Step1Chunk4_2_checked, root4Node75Step1Chunk4_3_checked, root4Node75Step1Chunk4_4_checked, root4Node75Step1Chunk4_5_checked, root4Node75Step1Chunk5_0_checked, root4Node75Step1Chunk5_1_checked, root4Node75Step1Chunk5_2_checked, root4Node75Step1Chunk5_3_checked, root4Node75Step1Chunk5_4_checked, root4Node75Step1Chunk5_5_checked, root4Node75Step1Chunk6_0_checked, root4Node75Step1Chunk6_1_checked, root4Node75Step1Chunk6_2_checked, root4Node75Step1Chunk6_3_checked, root4Node75Step1Chunk6_4_checked, root4Node75Step1Chunk6_5_checked, root4Node75Step1Chunk7_0_checked, root4Node75Step1Chunk7_1_checked, root4Node75Step1Chunk7_2_checked, root4Node75Step1Chunk7_3_checked, root4Node75Step1Chunk7_4_checked, root4Node75Step1Chunk7_5_checked, root4Node75Step1Chunk8_0_checked, root4Node75Step1Chunk8_1_checked, root4Node75Step1Chunk8_2_checked, root4Node75Step1Chunk8_3_checked, root4Node75Step1Chunk8_4_checked, root4Node75Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node75Step1_checked :
    checkReplacement table65 root4Node75Domains0 root4Node75Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node75Domains0 root4Node75Domains1
    root4Node75Domains0Fast root4Node75Domains1Fast
    root4Node75Domains0_fast_eq root4Node75Domains1_fast_eq
    root4Node75Step1Narrowing_checked (by decide)
theorem root4Node75Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node75Domains1 (.output 37) = true := by decide
def root4Node76Domains0 : Domains 91 State := restrict root4Node58Domains3 2 (7,2)
def root4Node76Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4),(5,4),(7,4)]
  | 1 => some [(0,0),(6,3),(6,4)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(2,1),(2,3),(4,3)]
  | 7 => some [(0,2),(1,5),(7,5)]
  | 8 => some [(0,3),(1,1),(6,1)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(4,1),(5,1),(8,1)]
  | 13 => some [(0,0),(1,4),(6,4),(7,4)]
  | 14 => some [(0,5),(1,2),(3,2),(6,3)]
  | 15 => some [(2,0),(2,2),(4,0)]
  | 16 => some [(3,3),(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(5,2),(5,5)]
  | 21 => some [(1,5),(4,1),(7,5)]
  | 22 => some [(0,2),(0,3),(6,0),(6,1)]
  | 23 => some [(1,1),(3,1),(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(4,4),(8,4)]
  | 30 => some [(4,5),(7,3)]
  | 31 => some [(4,2),(5,2),(7,0),(8,2)]
  | 32 => some [(5,0),(5,3),(8,3)]
  | 33 => some [(4,5),(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(7,1),(8,1)]
  | 39 => some [(1,5),(7,5)]
  | 40 => some [(0,0),(0,1),(6,4)]
  | 41 => some [(1,2),(6,2),(7,2)]
  | 42 => some [(7,4),(8,4)]
  | 43 => some [(0,0),(6,3)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3),(8,0)]
  | 49 => some [(4,5),(7,3),(8,5)]
  | 50 => some [(4,2),(7,0),(8,2)]
  | 51 => some [(0,3),(1,0),(6,1)]
  | 52 => some [(4,1),(7,1),(8,1)]
  | 53 => some [(0,2),(1,5)]
  | 54 => some [(1,1),(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(6,3),(6,4)]
  | 60 => some [(1,2),(7,2)]
  | 61 => some [(1,3),(3,3),(5,0),(5,3),(7,3)]
  | 62 => some [(4,5),(5,2),(5,5),(8,5)]
  | 63 => some [(7,0),(8,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5),(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1),(7,1)]
  | 68 => some [(0,2),(1,5),(7,5)]
  | 69 => some [(0,3),(1,1),(6,1)]
  | 70 => some [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 71 => some [(4,4),(5,4),(7,2),(8,4)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(1,3),(6,3)]
  | 74 => some [(4,4),(7,2),(8,2)]
  | 75 => some [(0,0),(4,0),(5,0),(8,0)]
  | 76 => some [(3,2),(4,5),(7,3)]
  | 77 => some [(4,0),(4,2),(7,0)]
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
  | 89 => some [(1,5),(3,5),(5,5),(7,0)]
  | _ => some [(0,3),(1,0),(6,1),(8,3)]
theorem root4Node76Domains0_fast_eq : root4Node76Domains0 = expandDomains root4Node76Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node76Domains0 v = expandDomains root4Node76Domains0Fast v from by decide) v
def root4Node76Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(3,4),(5,4),(7,4)]
  | 1 => [(0,0),(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(7,2)]
  | 6 => [(2,1),(2,3),(4,3)]
  | 7 => [(0,2),(1,5)]
  | 8 => [(1,1),(6,1)]
  | 9 => [(4,1)]
  | 10 => [(0,2)]
  | 11 => [(1,1)]
  | 12 => [(4,1),(5,1),(8,1)]
  | 13 => [(0,0),(1,4),(6,4)]
  | 14 => [(0,5),(1,2),(3,2)]
  | 15 => [(2,0),(4,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(5,2),(5,5)]
  | 21 => [(1,5),(7,5)]
  | 22 => [(0,3),(6,0),(6,1)]
  | 23 => [(3,1),(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(1,4),(6,4)]
  | 28 => [(0,5),(1,2)]
  | 29 => [(4,4),(8,4)]
  | 30 => [(4,5),(7,3)]
  | 31 => [(4,2),(7,0),(8,2)]
  | 32 => [(5,0),(5,3),(8,3)]
  | 33 => [(4,5),(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3),(6,0)]
  | 38 => [(7,1),(8,1)]
  | 39 => [(1,5),(7,5)]
  | 40 => [(0,0),(0,1),(6,4)]
  | 41 => [(1,2),(6,2),(7,2)]
  | 42 => [(7,4),(8,4)]
  | 43 => [(0,0),(6,3)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2),(8,2)]
  | 48 => [(5,0),(5,3),(8,0)]
  | 49 => [(4,5),(7,3),(8,5)]
  | 50 => [(4,2),(7,0),(8,2)]
  | 51 => [(0,3),(1,0),(6,1)]
  | 52 => [(4,1),(7,1),(8,1)]
  | 53 => [(0,2),(1,5)]
  | 54 => [(1,1),(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(7,4),(8,4)]
  | 59 => [(0,0),(6,3),(6,4)]
  | 60 => [(1,2),(7,2)]
  | 61 => [(1,3),(3,3),(5,0),(5,3),(7,3)]
  | 62 => [(4,5),(5,2),(5,5),(8,5)]
  | 63 => [(7,0),(8,0)]
  | 64 => [(8,3)]
  | 65 => [(5,5),(8,5)]
  | 66 => [(1,0)]
  | 67 => [(2,1),(7,1)]
  | 68 => [(0,2),(1,5),(7,5)]
  | 69 => [(0,3),(1,1),(6,1)]
  | 70 => [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 71 => [(4,4),(5,4),(7,2),(8,4)]
  | 72 => [(1,4),(7,4)]
  | 73 => [(0,5),(1,3),(6,3)]
  | 74 => [(4,4),(7,2),(8,2)]
  | 75 => [(0,0),(4,0),(5,0),(8,0)]
  | 76 => [(3,2),(4,5),(7,3)]
  | 77 => [(4,0),(4,2),(7,0)]
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
  | 89 => [(1,5),(3,5),(5,5),(7,0)]
  | _ => [(0,3),(1,0),(6,1),(8,3)]
def root4Node76Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4),(5,4),(7,4)]
  | 1 => some [(0,0),(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(2,1),(2,3),(4,3)]
  | 7 => some [(0,2),(1,5)]
  | 8 => some [(1,1),(6,1)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(4,1),(5,1),(8,1)]
  | 13 => some [(0,0),(1,4),(6,4)]
  | 14 => some [(0,5),(1,2),(3,2)]
  | 15 => some [(2,0),(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(5,2),(5,5)]
  | 21 => some [(1,5),(7,5)]
  | 22 => some [(0,3),(6,0),(6,1)]
  | 23 => some [(3,1),(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(4,4),(8,4)]
  | 30 => some [(4,5),(7,3)]
  | 31 => some [(4,2),(7,0),(8,2)]
  | 32 => some [(5,0),(5,3),(8,3)]
  | 33 => some [(4,5),(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(7,1),(8,1)]
  | 39 => some [(1,5),(7,5)]
  | 40 => some [(0,0),(0,1),(6,4)]
  | 41 => some [(1,2),(6,2),(7,2)]
  | 42 => some [(7,4),(8,4)]
  | 43 => some [(0,0),(6,3)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3),(8,0)]
  | 49 => some [(4,5),(7,3),(8,5)]
  | 50 => some [(4,2),(7,0),(8,2)]
  | 51 => some [(0,3),(1,0),(6,1)]
  | 52 => some [(4,1),(7,1),(8,1)]
  | 53 => some [(0,2),(1,5)]
  | 54 => some [(1,1),(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(6,3),(6,4)]
  | 60 => some [(1,2),(7,2)]
  | 61 => some [(1,3),(3,3),(5,0),(5,3),(7,3)]
  | 62 => some [(4,5),(5,2),(5,5),(8,5)]
  | 63 => some [(7,0),(8,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5),(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1),(7,1)]
  | 68 => some [(0,2),(1,5),(7,5)]
  | 69 => some [(0,3),(1,1),(6,1)]
  | 70 => some [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 71 => some [(4,4),(5,4),(7,2),(8,4)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(1,3),(6,3)]
  | 74 => some [(4,4),(7,2),(8,2)]
  | 75 => some [(0,0),(4,0),(5,0),(8,0)]
  | 76 => some [(3,2),(4,5),(7,3)]
  | 77 => some [(4,0),(4,2),(7,0)]
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
  | 89 => some [(1,5),(3,5),(5,5),(7,0)]
  | _ => some [(0,3),(1,0),(6,1),(8,3)]
theorem root4Node76Domains1_fast_eq : root4Node76Domains1 = expandDomains root4Node76Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node76Domains1 v = expandDomains root4Node76Domains1Fast v from by decide) v
theorem root4Node76Step1Chunk0_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_0⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk0_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_1⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk0_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_2⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk0_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_3⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk0_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_4⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk0_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_5⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk1_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_0⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk1_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_1⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk1_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_2⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk1_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_3⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk1_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_4⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk1_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_5⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk2_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_0⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk2_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_1⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk2_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_2⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk2_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_3⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk2_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_4⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk2_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_5⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk3_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_0⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk3_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_1⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk3_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_2⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk3_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_3⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk3_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_4⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk3_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_5⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk4_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_0⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk4_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_1⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk4_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_2⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk4_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_3⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk4_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_4⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk4_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_5⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk5_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_0⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk5_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_1⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk5_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_2⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk5_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_3⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk5_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_4⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk5_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_5⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk6_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_0⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk6_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_1⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk6_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_2⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk6_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_3⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk6_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_4⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk6_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_5⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk7_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_0⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk7_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_1⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk7_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_2⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk7_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_3⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk7_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_4⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk7_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_5⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk8_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_0⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk8_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_1⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk8_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_2⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk8_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_3⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk8_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_4⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Chunk8_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_5⟩
      root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq (by decide)
theorem root4Node76Step1Narrowing_checked :
    checkNarrowing table0 root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkNarrowing_flatten table0Scope [table0Rows0_0,table0Rows0_1,table0Rows0_2,table0Rows0_3,table0Rows0_4,table0Rows0_5,table0Rows1_0,table0Rows1_1,table0Rows1_2,table0Rows1_3,table0Rows1_4,table0Rows1_5,table0Rows2_0,table0Rows2_1,table0Rows2_2,table0Rows2_3,table0Rows2_4,table0Rows2_5,table0Rows3_0,table0Rows3_1,table0Rows3_2,table0Rows3_3,table0Rows3_4,table0Rows3_5,table0Rows4_0,table0Rows4_1,table0Rows4_2,table0Rows4_3,table0Rows4_4,table0Rows4_5,table0Rows5_0,table0Rows5_1,table0Rows5_2,table0Rows5_3,table0Rows5_4,table0Rows5_5,table0Rows6_0,table0Rows6_1,table0Rows6_2,table0Rows6_3,table0Rows6_4,table0Rows6_5,table0Rows7_0,table0Rows7_1,table0Rows7_2,table0Rows7_3,table0Rows7_4,table0Rows7_5,table0Rows8_0,table0Rows8_1,table0Rows8_2,table0Rows8_3,table0Rows8_4,table0Rows8_5]
    root4Node76Domains0 root4Node76Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node76Step1Chunk0_0_checked, root4Node76Step1Chunk0_1_checked, root4Node76Step1Chunk0_2_checked, root4Node76Step1Chunk0_3_checked, root4Node76Step1Chunk0_4_checked, root4Node76Step1Chunk0_5_checked, root4Node76Step1Chunk1_0_checked, root4Node76Step1Chunk1_1_checked, root4Node76Step1Chunk1_2_checked, root4Node76Step1Chunk1_3_checked, root4Node76Step1Chunk1_4_checked, root4Node76Step1Chunk1_5_checked, root4Node76Step1Chunk2_0_checked, root4Node76Step1Chunk2_1_checked, root4Node76Step1Chunk2_2_checked, root4Node76Step1Chunk2_3_checked, root4Node76Step1Chunk2_4_checked, root4Node76Step1Chunk2_5_checked, root4Node76Step1Chunk3_0_checked, root4Node76Step1Chunk3_1_checked, root4Node76Step1Chunk3_2_checked, root4Node76Step1Chunk3_3_checked, root4Node76Step1Chunk3_4_checked, root4Node76Step1Chunk3_5_checked, root4Node76Step1Chunk4_0_checked, root4Node76Step1Chunk4_1_checked, root4Node76Step1Chunk4_2_checked, root4Node76Step1Chunk4_3_checked, root4Node76Step1Chunk4_4_checked, root4Node76Step1Chunk4_5_checked, root4Node76Step1Chunk5_0_checked, root4Node76Step1Chunk5_1_checked, root4Node76Step1Chunk5_2_checked, root4Node76Step1Chunk5_3_checked, root4Node76Step1Chunk5_4_checked, root4Node76Step1Chunk5_5_checked, root4Node76Step1Chunk6_0_checked, root4Node76Step1Chunk6_1_checked, root4Node76Step1Chunk6_2_checked, root4Node76Step1Chunk6_3_checked, root4Node76Step1Chunk6_4_checked, root4Node76Step1Chunk6_5_checked, root4Node76Step1Chunk7_0_checked, root4Node76Step1Chunk7_1_checked, root4Node76Step1Chunk7_2_checked, root4Node76Step1Chunk7_3_checked, root4Node76Step1Chunk7_4_checked, root4Node76Step1Chunk7_5_checked, root4Node76Step1Chunk8_0_checked, root4Node76Step1Chunk8_1_checked, root4Node76Step1Chunk8_2_checked, root4Node76Step1Chunk8_3_checked, root4Node76Step1Chunk8_4_checked, root4Node76Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node76Step1_checked :
    checkReplacement table0 root4Node76Domains0 root4Node76Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node76Domains0 root4Node76Domains1
    root4Node76Domains0Fast root4Node76Domains1Fast
    root4Node76Domains0_fast_eq root4Node76Domains1_fast_eq
    root4Node76Step1Narrowing_checked (by decide)
def root4Node76Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(3,4),(5,4),(7,4)]
  | 1 => [(0,0),(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(7,2)]
  | 6 => [(2,1),(2,3),(4,3)]
  | 7 => [(0,2),(1,5)]
  | 8 => [(1,1),(6,1)]
  | 9 => [(4,1)]
  | 10 => [(0,2)]
  | 11 => [(1,1)]
  | 12 => [(4,1),(5,1),(8,1)]
  | 13 => [(0,0),(1,4),(6,4)]
  | 14 => [(0,5),(1,2),(3,2)]
  | 15 => [(2,0),(4,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(5,2),(5,5)]
  | 21 => [(1,5),(7,5)]
  | 22 => [(0,3),(6,0),(6,1)]
  | 23 => [(3,1),(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(1,4),(6,4)]
  | 28 => [(0,5),(1,2)]
  | 29 => [(4,4),(8,4)]
  | 30 => [(4,5),(7,3)]
  | 31 => [(4,2),(7,0),(8,2)]
  | 32 => [(5,0),(5,3),(8,3)]
  | 33 => [(4,5),(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3),(6,0)]
  | 38 => [(7,1),(8,1)]
  | 39 => [(1,5),(7,5)]
  | 40 => [(0,0),(0,1),(6,4)]
  | 41 => [(1,2),(6,2),(7,2)]
  | 42 => [(7,4),(8,4)]
  | 43 => [(0,0),(6,3)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2),(8,2)]
  | 48 => [(5,0),(5,3),(8,0)]
  | 49 => [(4,5),(7,3),(8,5)]
  | 50 => [(4,2),(7,0)]
  | 51 => [(0,3),(1,0),(6,1)]
  | 52 => [(4,1),(7,1),(8,1)]
  | 53 => [(0,2),(1,5)]
  | 54 => [(1,1),(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(7,4),(8,4)]
  | 59 => [(0,0),(6,3),(6,4)]
  | 60 => [(1,2),(7,2)]
  | 61 => [(1,3),(3,3),(5,0),(5,3),(7,3)]
  | 62 => [(4,5),(5,2),(5,5),(8,5)]
  | 63 => [(7,0),(8,0)]
  | 64 => [(8,3)]
  | 65 => [(5,5),(8,5)]
  | 66 => [(1,0)]
  | 67 => [(2,1),(7,1)]
  | 68 => [(0,2),(1,5),(7,5)]
  | 69 => [(0,3),(1,1),(6,1)]
  | 70 => [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 71 => [(4,4),(5,4),(7,2),(8,4)]
  | 72 => [(1,4),(7,4)]
  | 73 => [(0,5),(1,3),(6,3)]
  | 74 => [(4,4),(7,2),(8,2)]
  | 75 => [(0,0),(4,0),(5,0),(8,0)]
  | 76 => [(3,2),(4,5),(7,3)]
  | 77 => [(4,0),(4,2),(7,0)]
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
  | 89 => [(1,5),(3,5),(5,5),(7,0)]
  | _ => [(0,3),(1,0),(6,1),(8,3)]
def root4Node76Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4),(5,4),(7,4)]
  | 1 => some [(0,0),(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(2,1),(2,3),(4,3)]
  | 7 => some [(0,2),(1,5)]
  | 8 => some [(1,1),(6,1)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(4,1),(5,1),(8,1)]
  | 13 => some [(0,0),(1,4),(6,4)]
  | 14 => some [(0,5),(1,2),(3,2)]
  | 15 => some [(2,0),(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(5,2),(5,5)]
  | 21 => some [(1,5),(7,5)]
  | 22 => some [(0,3),(6,0),(6,1)]
  | 23 => some [(3,1),(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(4,4),(8,4)]
  | 30 => some [(4,5),(7,3)]
  | 31 => some [(4,2),(7,0),(8,2)]
  | 32 => some [(5,0),(5,3),(8,3)]
  | 33 => some [(4,5),(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(7,1),(8,1)]
  | 39 => some [(1,5),(7,5)]
  | 40 => some [(0,0),(0,1),(6,4)]
  | 41 => some [(1,2),(6,2),(7,2)]
  | 42 => some [(7,4),(8,4)]
  | 43 => some [(0,0),(6,3)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3),(8,0)]
  | 49 => some [(4,5),(7,3),(8,5)]
  | 50 => some [(4,2),(7,0)]
  | 51 => some [(0,3),(1,0),(6,1)]
  | 52 => some [(4,1),(7,1),(8,1)]
  | 53 => some [(0,2),(1,5)]
  | 54 => some [(1,1),(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(6,3),(6,4)]
  | 60 => some [(1,2),(7,2)]
  | 61 => some [(1,3),(3,3),(5,0),(5,3),(7,3)]
  | 62 => some [(4,5),(5,2),(5,5),(8,5)]
  | 63 => some [(7,0),(8,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5),(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1),(7,1)]
  | 68 => some [(0,2),(1,5),(7,5)]
  | 69 => some [(0,3),(1,1),(6,1)]
  | 70 => some [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 71 => some [(4,4),(5,4),(7,2),(8,4)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(1,3),(6,3)]
  | 74 => some [(4,4),(7,2),(8,2)]
  | 75 => some [(0,0),(4,0),(5,0),(8,0)]
  | 76 => some [(3,2),(4,5),(7,3)]
  | 77 => some [(4,0),(4,2),(7,0)]
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
  | 89 => some [(1,5),(3,5),(5,5),(7,0)]
  | _ => some [(0,3),(1,0),(6,1),(8,3)]
theorem root4Node76Domains2_fast_eq : root4Node76Domains2 = expandDomains root4Node76Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node76Domains2 v = expandDomains root4Node76Domains2Fast v from by decide) v
theorem root4Node76Step2Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq (by decide)
theorem root4Node76Step2Narrowing_checked :
    checkNarrowing table12 root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkNarrowing_flatten table12Scope [table12Rows0_0,table12Rows0_1,table12Rows0_2,table12Rows0_3,table12Rows0_4,table12Rows0_5,table12Rows1_0,table12Rows1_1,table12Rows1_2,table12Rows1_3,table12Rows1_4,table12Rows1_5,table12Rows2_0,table12Rows2_1,table12Rows2_2,table12Rows2_3,table12Rows2_4,table12Rows2_5,table12Rows3_0,table12Rows3_1,table12Rows3_2,table12Rows3_3,table12Rows3_4,table12Rows3_5,table12Rows4_0,table12Rows4_1,table12Rows4_2,table12Rows4_3,table12Rows4_4,table12Rows4_5,table12Rows5_0,table12Rows5_1,table12Rows5_2,table12Rows5_3,table12Rows5_4,table12Rows5_5,table12Rows6_0,table12Rows6_1,table12Rows6_2,table12Rows6_3,table12Rows6_4,table12Rows6_5,table12Rows7_0,table12Rows7_1,table12Rows7_2,table12Rows7_3,table12Rows7_4,table12Rows7_5,table12Rows8_0,table12Rows8_1,table12Rows8_2,table12Rows8_3,table12Rows8_4,table12Rows8_5]
    root4Node76Domains1 root4Node76Domains2 (by
      simp only [List.all_cons, List.all_nil, root4Node76Step2Chunk0_0_checked, root4Node76Step2Chunk0_1_checked, root4Node76Step2Chunk0_2_checked, root4Node76Step2Chunk0_3_checked, root4Node76Step2Chunk0_4_checked, root4Node76Step2Chunk0_5_checked, root4Node76Step2Chunk1_0_checked, root4Node76Step2Chunk1_1_checked, root4Node76Step2Chunk1_2_checked, root4Node76Step2Chunk1_3_checked, root4Node76Step2Chunk1_4_checked, root4Node76Step2Chunk1_5_checked, root4Node76Step2Chunk2_0_checked, root4Node76Step2Chunk2_1_checked, root4Node76Step2Chunk2_2_checked, root4Node76Step2Chunk2_3_checked, root4Node76Step2Chunk2_4_checked, root4Node76Step2Chunk2_5_checked, root4Node76Step2Chunk3_0_checked, root4Node76Step2Chunk3_1_checked, root4Node76Step2Chunk3_2_checked, root4Node76Step2Chunk3_3_checked, root4Node76Step2Chunk3_4_checked, root4Node76Step2Chunk3_5_checked, root4Node76Step2Chunk4_0_checked, root4Node76Step2Chunk4_1_checked, root4Node76Step2Chunk4_2_checked, root4Node76Step2Chunk4_3_checked, root4Node76Step2Chunk4_4_checked, root4Node76Step2Chunk4_5_checked, root4Node76Step2Chunk5_0_checked, root4Node76Step2Chunk5_1_checked, root4Node76Step2Chunk5_2_checked, root4Node76Step2Chunk5_3_checked, root4Node76Step2Chunk5_4_checked, root4Node76Step2Chunk5_5_checked, root4Node76Step2Chunk6_0_checked, root4Node76Step2Chunk6_1_checked, root4Node76Step2Chunk6_2_checked, root4Node76Step2Chunk6_3_checked, root4Node76Step2Chunk6_4_checked, root4Node76Step2Chunk6_5_checked, root4Node76Step2Chunk7_0_checked, root4Node76Step2Chunk7_1_checked, root4Node76Step2Chunk7_2_checked, root4Node76Step2Chunk7_3_checked, root4Node76Step2Chunk7_4_checked, root4Node76Step2Chunk7_5_checked, root4Node76Step2Chunk8_0_checked, root4Node76Step2Chunk8_1_checked, root4Node76Step2Chunk8_2_checked, root4Node76Step2Chunk8_3_checked, root4Node76Step2Chunk8_4_checked, root4Node76Step2Chunk8_5_checked, Bool.true_and])
theorem root4Node76Step2_checked :
    checkReplacement table12 root4Node76Domains1 root4Node76Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root4Node76Domains1 root4Node76Domains2
    root4Node76Domains1Fast root4Node76Domains2Fast
    root4Node76Domains1_fast_eq root4Node76Domains2_fast_eq
    root4Node76Step2Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
