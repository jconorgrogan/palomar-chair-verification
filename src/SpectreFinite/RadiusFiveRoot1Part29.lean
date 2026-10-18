module

public import SpectreFinite.RadiusFiveRoot1Part28
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable25
public import SpectreFinite.RadiusFiveTable65

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node73Domains0 : Domains 91 State := restrict root1Node72Domains1 71 (5,5)
def root1Node73Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(0,4)]
  | 7 => some [(1,4)]
  | 8 => some [(0,5)]
  | 9 => some [(4,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(3,0)]
  | 14 => some [(2,5)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(8,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(8,3)]
  | 71 => some [(5,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(3,5),(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5),(6,3)]
  | 79 => some [(4,4),(7,2)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(6,3)]
  | 82 => some [(2,2),(2,4)]
  | 83 => some [(1,3),(3,3)]
  | 84 => some [(5,2)]
  | 85 => some [(1,1),(7,1)]
  | 86 => some [(4,1),(7,5)]
  | 87 => some [(0,2),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(0,1),(6,5)]
  | _ => some [(0,4),(6,2)]
theorem root1Node73Domains0_fast_eq : root1Node73Domains0 = expandDomains root1Node73Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node73Domains0 v = expandDomains root1Node73Domains0Fast v from by decide) v
def root1Node73Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(5,5)]
  | 3 => [(7,0)]
  | 4 => [(8,3)]
  | 5 => [(5,5)]
  | 6 => [(0,4)]
  | 7 => [(1,4)]
  | 8 => [(0,5)]
  | 9 => [(4,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(3,0)]
  | 14 => [(2,5)]
  | 15 => [(6,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(4,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(7,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(8,4)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(8,1)]
  | 50 => [(1,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3)]
  | 55 => [(8,2)]
  | 56 => [(8,0)]
  | 57 => [(7,3)]
  | 58 => [(4,2)]
  | 59 => [(5,3)]
  | 60 => [(8,5)]
  | 61 => [(6,1)]
  | 62 => [(8,1)]
  | 63 => [(6,5)]
  | 64 => [(0,4)]
  | 65 => [(5,4)]
  | 66 => [(6,4)]
  | 67 => [(1,2)]
  | 68 => [(7,4)]
  | 69 => [(6,3)]
  | 70 => [(8,3)]
  | 71 => [(5,5)]
  | 72 => [(7,0)]
  | 73 => [(4,3)]
  | 74 => [(3,5)]
  | 75 => [(0,3)]
  | 76 => [(4,1)]
  | 77 => [(0,2)]
  | 78 => [(0,5)]
  | 79 => [(4,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(2,4)]
  | 83 => [(1,3)]
  | 84 => [(5,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(7,1)]
  | 89 => [(6,5)]
  | _ => [(0,4)]
def root1Node73Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(0,4)]
  | 7 => some [(1,4)]
  | 8 => some [(0,5)]
  | 9 => some [(4,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(3,0)]
  | 14 => some [(2,5)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(8,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(8,3)]
  | 71 => some [(5,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(3,5)]
  | 75 => some [(0,3)]
  | 76 => some [(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5)]
  | 79 => some [(4,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(2,4)]
  | 83 => some [(1,3)]
  | 84 => some [(5,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(6,5)]
  | _ => some [(0,4)]
theorem root1Node73Domains1_fast_eq : root1Node73Domains1 = expandDomains root1Node73Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node73Domains1 v = expandDomains root1Node73Domains1Fast v from by decide) v
theorem root1Node73Step1Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq (by decide)
theorem root1Node73Step1Narrowing_checked :
    checkNarrowing table65 root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root1Node73Domains0 root1Node73Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node73Step1Chunk0_0_checked, root1Node73Step1Chunk0_1_checked, root1Node73Step1Chunk0_2_checked, root1Node73Step1Chunk0_3_checked, root1Node73Step1Chunk0_4_checked, root1Node73Step1Chunk0_5_checked, root1Node73Step1Chunk1_0_checked, root1Node73Step1Chunk1_1_checked, root1Node73Step1Chunk1_2_checked, root1Node73Step1Chunk1_3_checked, root1Node73Step1Chunk1_4_checked, root1Node73Step1Chunk1_5_checked, root1Node73Step1Chunk2_0_checked, root1Node73Step1Chunk2_1_checked, root1Node73Step1Chunk2_2_checked, root1Node73Step1Chunk2_3_checked, root1Node73Step1Chunk2_4_checked, root1Node73Step1Chunk2_5_checked, root1Node73Step1Chunk3_0_checked, root1Node73Step1Chunk3_1_checked, root1Node73Step1Chunk3_2_checked, root1Node73Step1Chunk3_3_checked, root1Node73Step1Chunk3_4_checked, root1Node73Step1Chunk3_5_checked, root1Node73Step1Chunk4_0_checked, root1Node73Step1Chunk4_1_checked, root1Node73Step1Chunk4_2_checked, root1Node73Step1Chunk4_3_checked, root1Node73Step1Chunk4_4_checked, root1Node73Step1Chunk4_5_checked, root1Node73Step1Chunk5_0_checked, root1Node73Step1Chunk5_1_checked, root1Node73Step1Chunk5_2_checked, root1Node73Step1Chunk5_3_checked, root1Node73Step1Chunk5_4_checked, root1Node73Step1Chunk5_5_checked, root1Node73Step1Chunk6_0_checked, root1Node73Step1Chunk6_1_checked, root1Node73Step1Chunk6_2_checked, root1Node73Step1Chunk6_3_checked, root1Node73Step1Chunk6_4_checked, root1Node73Step1Chunk6_5_checked, root1Node73Step1Chunk7_0_checked, root1Node73Step1Chunk7_1_checked, root1Node73Step1Chunk7_2_checked, root1Node73Step1Chunk7_3_checked, root1Node73Step1Chunk7_4_checked, root1Node73Step1Chunk7_5_checked, root1Node73Step1Chunk8_0_checked, root1Node73Step1Chunk8_1_checked, root1Node73Step1Chunk8_2_checked, root1Node73Step1Chunk8_3_checked, root1Node73Step1Chunk8_4_checked, root1Node73Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node73Step1_checked :
    checkReplacement table65 root1Node73Domains0 root1Node73Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node73Domains0 root1Node73Domains1
    root1Node73Domains0Fast root1Node73Domains1Fast
    root1Node73Domains0_fast_eq root1Node73Domains1_fast_eq
    root1Node73Step1Narrowing_checked (by decide)
theorem root1Node73Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node73Domains1 (.output 35) = true := by decide
def root1Node74Domains0 : Domains 91 State := restrict root1Node72Domains1 71 (8,5)
def root1Node74Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(0,4)]
  | 7 => some [(1,4)]
  | 8 => some [(0,5)]
  | 9 => some [(4,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(3,0)]
  | 14 => some [(2,5)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(8,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(3,5),(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5),(6,3)]
  | 79 => some [(4,4),(7,2)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(6,3)]
  | 82 => some [(2,2),(2,4)]
  | 83 => some [(1,3),(3,3)]
  | 84 => some [(5,2)]
  | 85 => some [(1,1),(7,1)]
  | 86 => some [(4,1),(7,5)]
  | 87 => some [(0,2),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(0,1),(6,5)]
  | _ => some [(0,4),(6,2)]
theorem root1Node74Domains0_fast_eq : root1Node74Domains0 = expandDomains root1Node74Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node74Domains0 v = expandDomains root1Node74Domains0Fast v from by decide) v
def root1Node74Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(5,5)]
  | 3 => [(7,0)]
  | 4 => [(8,3)]
  | 5 => [(5,5)]
  | 6 => [(0,4)]
  | 7 => [(1,4)]
  | 8 => [(0,5)]
  | 9 => [(4,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(3,0)]
  | 14 => [(2,5)]
  | 15 => [(6,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(4,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(7,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(8,4)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(8,1)]
  | 50 => [(1,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3)]
  | 55 => [(8,2)]
  | 56 => [(8,0)]
  | 57 => [(7,3)]
  | 58 => [(4,2)]
  | 59 => [(5,3)]
  | 60 => [(8,5)]
  | 61 => [(6,1)]
  | 62 => [(8,1)]
  | 63 => [(6,5)]
  | 64 => [(0,4)]
  | 65 => [(5,4)]
  | 66 => [(6,4)]
  | 67 => [(1,2)]
  | 68 => [(7,4)]
  | 69 => [(6,3)]
  | 70 => [(8,3)]
  | 71 => [(8,5)]
  | 72 => [(7,0)]
  | 73 => [(4,3)]
  | 74 => [(7,5)]
  | 75 => [(0,3)]
  | 76 => [(4,1)]
  | 77 => [(0,2)]
  | 78 => [(6,3)]
  | 79 => [(7,2)]
  | 80 => [(7,4)]
  | 81 => [(6,3)]
  | 82 => [(2,2)]
  | 83 => [(3,3)]
  | 84 => [(5,2)]
  | 85 => [(1,1)]
  | 86 => [(4,1)]
  | 87 => [(0,2)]
  | 88 => [(1,1)]
  | 89 => [(0,1)]
  | _ => [(6,2)]
def root1Node74Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(0,4)]
  | 7 => some [(1,4)]
  | 8 => some [(0,5)]
  | 9 => some [(4,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(3,0)]
  | 14 => some [(2,5)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(8,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(6,3)]
  | 82 => some [(2,2)]
  | 83 => some [(3,3)]
  | 84 => some [(5,2)]
  | 85 => some [(1,1)]
  | 86 => some [(4,1)]
  | 87 => some [(0,2)]
  | 88 => some [(1,1)]
  | 89 => some [(0,1)]
  | _ => some [(6,2)]
theorem root1Node74Domains1_fast_eq : root1Node74Domains1 = expandDomains root1Node74Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node74Domains1 v = expandDomains root1Node74Domains1Fast v from by decide) v
theorem root1Node74Step1Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq (by decide)
theorem root1Node74Step1Narrowing_checked :
    checkNarrowing table65 root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root1Node74Domains0 root1Node74Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node74Step1Chunk0_0_checked, root1Node74Step1Chunk0_1_checked, root1Node74Step1Chunk0_2_checked, root1Node74Step1Chunk0_3_checked, root1Node74Step1Chunk0_4_checked, root1Node74Step1Chunk0_5_checked, root1Node74Step1Chunk1_0_checked, root1Node74Step1Chunk1_1_checked, root1Node74Step1Chunk1_2_checked, root1Node74Step1Chunk1_3_checked, root1Node74Step1Chunk1_4_checked, root1Node74Step1Chunk1_5_checked, root1Node74Step1Chunk2_0_checked, root1Node74Step1Chunk2_1_checked, root1Node74Step1Chunk2_2_checked, root1Node74Step1Chunk2_3_checked, root1Node74Step1Chunk2_4_checked, root1Node74Step1Chunk2_5_checked, root1Node74Step1Chunk3_0_checked, root1Node74Step1Chunk3_1_checked, root1Node74Step1Chunk3_2_checked, root1Node74Step1Chunk3_3_checked, root1Node74Step1Chunk3_4_checked, root1Node74Step1Chunk3_5_checked, root1Node74Step1Chunk4_0_checked, root1Node74Step1Chunk4_1_checked, root1Node74Step1Chunk4_2_checked, root1Node74Step1Chunk4_3_checked, root1Node74Step1Chunk4_4_checked, root1Node74Step1Chunk4_5_checked, root1Node74Step1Chunk5_0_checked, root1Node74Step1Chunk5_1_checked, root1Node74Step1Chunk5_2_checked, root1Node74Step1Chunk5_3_checked, root1Node74Step1Chunk5_4_checked, root1Node74Step1Chunk5_5_checked, root1Node74Step1Chunk6_0_checked, root1Node74Step1Chunk6_1_checked, root1Node74Step1Chunk6_2_checked, root1Node74Step1Chunk6_3_checked, root1Node74Step1Chunk6_4_checked, root1Node74Step1Chunk6_5_checked, root1Node74Step1Chunk7_0_checked, root1Node74Step1Chunk7_1_checked, root1Node74Step1Chunk7_2_checked, root1Node74Step1Chunk7_3_checked, root1Node74Step1Chunk7_4_checked, root1Node74Step1Chunk7_5_checked, root1Node74Step1Chunk8_0_checked, root1Node74Step1Chunk8_1_checked, root1Node74Step1Chunk8_2_checked, root1Node74Step1Chunk8_3_checked, root1Node74Step1Chunk8_4_checked, root1Node74Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node74Step1_checked :
    checkReplacement table65 root1Node74Domains0 root1Node74Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node74Domains0 root1Node74Domains1
    root1Node74Domains0Fast root1Node74Domains1Fast
    root1Node74Domains0_fast_eq root1Node74Domains1_fast_eq
    root1Node74Step1Narrowing_checked (by decide)
theorem root1Node74Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node74Domains1 (.output 36) = true := by decide
def root1Node75Domains0 : Domains 91 State := restrict root1Node71Domains1 54 (6,3)
def root1Node75Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(0,4)]
  | 7 => some [(1,4)]
  | 8 => some [(0,5)]
  | 9 => some [(4,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(3,0)]
  | 14 => some [(2,5)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(8,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(4,0),(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(4,1),(8,1)]
  | 63 => some [(0,2),(6,5)]
  | 64 => some [(0,4),(1,1)]
  | 65 => some [(5,1),(5,4)]
  | 66 => some [(0,1),(6,4)]
  | 67 => some [(1,2),(6,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(7,3),(8,3)]
  | 71 => some [(5,2),(5,5),(8,5)]
  | 72 => some [(7,0),(8,0)]
  | 73 => some [(4,3),(8,3)]
  | 74 => some [(3,5),(5,5),(7,5)]
  | 75 => some [(0,3),(1,0)]
  | 76 => some [(2,1),(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5),(6,2),(6,3)]
  | 79 => some [(4,4),(7,2),(8,4)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(6,3)]
  | 82 => some [(2,2),(2,4),(4,4)]
  | 83 => some [(0,0),(1,3),(3,3)]
  | 84 => some [(3,2),(5,2)]
  | 85 => some [(1,1),(7,1)]
  | 86 => some [(4,1),(7,5)]
  | 87 => some [(0,2),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(0,1),(1,5),(6,5)]
  | _ => some [(0,4),(6,1),(6,2)]
theorem root1Node75Domains0_fast_eq : root1Node75Domains0 = expandDomains root1Node75Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node75Domains0 v = expandDomains root1Node75Domains0Fast v from by decide) v
def root1Node75Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(5,5)]
  | 3 => [(7,0)]
  | 4 => [(8,3)]
  | 5 => [(5,5)]
  | 6 => [(0,4)]
  | 7 => [(1,4)]
  | 8 => [(0,5)]
  | 9 => [(4,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(3,0)]
  | 14 => [(2,5)]
  | 15 => [(6,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(4,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(7,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(8,4)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(8,1)]
  | 50 => [(1,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(4,0)]
  | 57 => [(7,3)]
  | 58 => [(4,2)]
  | 59 => [(5,3)]
  | 60 => [(8,5)]
  | 61 => [(6,1)]
  | 62 => [(4,1)]
  | 63 => [(0,2)]
  | 64 => [(1,1)]
  | 65 => [(5,1)]
  | 66 => [(0,1)]
  | 67 => [(6,2)]
  | 68 => [(7,4)]
  | 69 => [(6,3)]
  | 70 => [(7,3)]
  | 71 => [(5,2)]
  | 72 => [(8,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5)]
  | 75 => [(1,0)]
  | 76 => [(2,1)]
  | 77 => [(0,2)]
  | 78 => [(6,2)]
  | 79 => [(8,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(4,4)]
  | 83 => [(0,0)]
  | 84 => [(3,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(7,1)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root1Node75Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(0,4)]
  | 7 => some [(1,4)]
  | 8 => some [(0,5)]
  | 9 => some [(4,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(3,0)]
  | 14 => some [(2,5)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(8,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(4,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(5,1)]
  | 66 => some [(0,1)]
  | 67 => some [(6,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2)]
  | 72 => some [(8,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(1,0)]
  | 76 => some [(2,1)]
  | 77 => some [(0,2)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(0,0)]
  | 84 => some [(3,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root1Node75Domains1_fast_eq : root1Node75Domains1 = expandDomains root1Node75Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node75Domains1 v = expandDomains root1Node75Domains1Fast v from by decide) v
theorem root1Node75Step1Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq (by decide)
theorem root1Node75Step1Narrowing_checked :
    checkNarrowing table65 root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root1Node75Domains0 root1Node75Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node75Step1Chunk0_0_checked, root1Node75Step1Chunk0_1_checked, root1Node75Step1Chunk0_2_checked, root1Node75Step1Chunk0_3_checked, root1Node75Step1Chunk0_4_checked, root1Node75Step1Chunk0_5_checked, root1Node75Step1Chunk1_0_checked, root1Node75Step1Chunk1_1_checked, root1Node75Step1Chunk1_2_checked, root1Node75Step1Chunk1_3_checked, root1Node75Step1Chunk1_4_checked, root1Node75Step1Chunk1_5_checked, root1Node75Step1Chunk2_0_checked, root1Node75Step1Chunk2_1_checked, root1Node75Step1Chunk2_2_checked, root1Node75Step1Chunk2_3_checked, root1Node75Step1Chunk2_4_checked, root1Node75Step1Chunk2_5_checked, root1Node75Step1Chunk3_0_checked, root1Node75Step1Chunk3_1_checked, root1Node75Step1Chunk3_2_checked, root1Node75Step1Chunk3_3_checked, root1Node75Step1Chunk3_4_checked, root1Node75Step1Chunk3_5_checked, root1Node75Step1Chunk4_0_checked, root1Node75Step1Chunk4_1_checked, root1Node75Step1Chunk4_2_checked, root1Node75Step1Chunk4_3_checked, root1Node75Step1Chunk4_4_checked, root1Node75Step1Chunk4_5_checked, root1Node75Step1Chunk5_0_checked, root1Node75Step1Chunk5_1_checked, root1Node75Step1Chunk5_2_checked, root1Node75Step1Chunk5_3_checked, root1Node75Step1Chunk5_4_checked, root1Node75Step1Chunk5_5_checked, root1Node75Step1Chunk6_0_checked, root1Node75Step1Chunk6_1_checked, root1Node75Step1Chunk6_2_checked, root1Node75Step1Chunk6_3_checked, root1Node75Step1Chunk6_4_checked, root1Node75Step1Chunk6_5_checked, root1Node75Step1Chunk7_0_checked, root1Node75Step1Chunk7_1_checked, root1Node75Step1Chunk7_2_checked, root1Node75Step1Chunk7_3_checked, root1Node75Step1Chunk7_4_checked, root1Node75Step1Chunk7_5_checked, root1Node75Step1Chunk8_0_checked, root1Node75Step1Chunk8_1_checked, root1Node75Step1Chunk8_2_checked, root1Node75Step1Chunk8_3_checked, root1Node75Step1Chunk8_4_checked, root1Node75Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node75Step1_checked :
    checkReplacement table65 root1Node75Domains0 root1Node75Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node75Domains0 root1Node75Domains1
    root1Node75Domains0Fast root1Node75Domains1Fast
    root1Node75Domains0_fast_eq root1Node75Domains1_fast_eq
    root1Node75Step1Narrowing_checked (by decide)
theorem root1Node75Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node75Domains1 (.output 37) = true := by decide
def root1Node76Domains0 : Domains 91 State := restrict root1Node58Domains4 3 (8,0)
def root1Node76Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,0),(2,2),(4,0),(4,2)]
  | 1 => some [(3,3),(5,3),(7,3)]
  | 2 => some [(5,2),(5,5),(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(4,3),(7,3),(8,3)]
  | 5 => some [(1,5),(3,5),(4,2),(5,2),(5,5),(8,2)]
  | 6 => some [(0,4),(1,1),(3,1),(5,1)]
  | 7 => some [(0,1),(1,4)]
  | 8 => some [(0,5),(6,2)]
  | 9 => some [(4,4),(8,4)]
  | 10 => some [(1,4),(6,4)]
  | 11 => some [(0,5),(1,2)]
  | 12 => some [(2,0),(2,4),(4,4),(7,4),(8,4)]
  | 13 => some [(3,0),(5,0),(5,3),(8,3)]
  | 14 => some [(2,5),(4,5),(8,5)]
  | 15 => some [(1,0),(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3),(6,0)]
  | 19 => some [(3,1),(7,1),(8,1)]
  | 20 => some [(0,1),(1,5),(6,5),(7,5)]
  | 21 => some [(4,4),(7,4),(8,4)]
  | 22 => some [(0,0),(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(4,2),(8,2)]
  | 27 => some [(5,0),(5,3),(8,0)]
  | 28 => some [(4,5),(7,3),(8,5)]
  | 29 => some [(1,0),(4,2),(7,0),(8,2)]
  | 30 => some [(4,1),(7,1),(8,1)]
  | 31 => some [(0,2),(1,5)]
  | 32 => some [(1,1),(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(7,4),(8,4)]
  | 37 => some [(0,0),(6,3),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(4,0),(7,4),(8,4)]
  | 40 => some [(1,3),(3,3),(5,0),(5,3),(7,3)]
  | 41 => some [(4,5),(5,2),(5,5),(8,5)]
  | 42 => some [(7,0),(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(2,1),(7,1)]
  | 47 => some [(0,2),(1,5),(7,5)]
  | 48 => some [(0,3),(1,1),(6,1)]
  | 49 => some [(4,1),(5,1),(8,1)]
  | 50 => some [(0,1),(0,2),(1,5),(6,5)]
  | 51 => some [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 52 => some [(4,4),(5,4),(7,2),(8,4)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(1,3),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2)]
  | 56 => some [(0,0),(4,0),(5,0),(8,0)]
  | 57 => some [(3,2),(4,5),(7,3)]
  | 58 => some [(4,0),(4,2),(7,0)]
  | 59 => some [(5,3),(7,3),(8,3)]
  | 60 => some [(5,2),(8,5)]
  | 61 => some [(1,1),(4,3),(6,1),(7,1)]
  | 62 => some [(4,1),(7,5),(8,1)]
  | 63 => some [(0,2),(6,0),(6,5)]
  | 64 => some [(0,4),(1,1),(7,1)]
  | 65 => some [(1,5),(5,1),(5,4)]
  | 66 => some [(0,0),(0,1),(6,1),(6,4)]
  | 67 => some [(1,2),(5,1),(6,2),(7,2)]
  | 68 => some [(0,1),(7,4)]
  | 69 => some [(6,2),(6,3)]
  | 70 => some [(1,3),(7,3),(8,3)]
  | 71 => some [(5,2),(5,5),(8,2),(8,5)]
  | 72 => some [(5,0),(7,0),(8,0)]
  | 73 => some [(4,3),(4,5),(8,3)]
  | 74 => some [(1,5),(3,5),(5,5),(7,0),(7,5)]
  | 75 => some [(0,3),(1,0),(6,1),(8,3)]
  | 76 => some [(2,1),(4,1),(8,5)]
  | 77 => some [(0,2),(1,0)]
  | 78 => some [(0,4),(0,5),(1,2),(6,2),(6,3)]
  | 79 => some [(4,4),(5,4),(7,2),(8,4)]
  | 80 => some [(0,0),(1,4),(7,4)]
  | 81 => some [(0,5),(6,3),(7,2)]
  | 82 => some [(2,0),(2,2),(2,4),(4,4),(7,4)]
  | 83 => some [(0,0),(1,3),(3,3),(6,3),(7,3)]
  | 84 => some [(3,2),(5,2),(7,2),(8,2)]
  | 85 => some [(1,1),(4,3),(7,1),(8,1)]
  | 86 => some [(1,5),(4,1),(7,5)]
  | 87 => some [(0,2),(6,0),(6,1)]
  | 88 => some [(1,1),(3,1),(4,1),(7,1),(8,1)]
  | 89 => some [(0,1),(0,2),(1,5),(6,5)]
  | _ => some [(0,4),(1,1),(6,1),(6,2)]
theorem root1Node76Domains0_fast_eq : root1Node76Domains0 = expandDomains root1Node76Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node76Domains0 v = expandDomains root1Node76Domains0Fast v from by decide) v
def root1Node76Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,0),(2,2),(4,0)]
  | 1 => [(3,3),(7,3)]
  | 2 => [(5,2),(8,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3),(8,3)]
  | 5 => [(4,2),(5,2),(5,5),(8,2)]
  | 6 => [(1,1),(3,1),(5,1)]
  | 7 => [(0,1)]
  | 8 => [(6,2)]
  | 9 => [(8,4)]
  | 10 => [(1,4),(6,4)]
  | 11 => [(0,5),(1,2)]
  | 12 => [(4,4),(7,4),(8,4)]
  | 13 => [(5,0),(5,3),(8,3)]
  | 14 => [(4,5),(8,5)]
  | 15 => [(1,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(0,3),(6,0)]
  | 19 => [(7,1),(8,1)]
  | 20 => [(1,5),(6,5),(7,5)]
  | 21 => [(7,4),(8,4)]
  | 22 => [(0,0),(6,3)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(4,2),(8,2)]
  | 27 => [(5,0),(5,3),(8,0)]
  | 28 => [(4,5),(7,3),(8,5)]
  | 29 => [(4,2),(7,0),(8,2)]
  | 30 => [(4,1),(7,1),(8,1)]
  | 31 => [(0,2),(1,5)]
  | 32 => [(1,1),(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(7,4),(8,4)]
  | 37 => [(0,0),(6,3),(6,4)]
  | 38 => [(1,2),(7,2)]
  | 39 => [(4,0),(7,4),(8,4)]
  | 40 => [(1,3),(3,3),(5,0),(5,3),(7,3)]
  | 41 => [(4,5),(5,2),(5,5),(8,5)]
  | 42 => [(7,0),(8,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5),(8,5)]
  | 45 => [(1,0)]
  | 46 => [(2,1),(7,1)]
  | 47 => [(0,2),(1,5),(7,5)]
  | 48 => [(0,3),(1,1),(6,1)]
  | 49 => [(4,1),(5,1),(8,1)]
  | 50 => [(0,1),(0,2),(1,5),(6,5)]
  | 51 => [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 52 => [(4,4),(5,4),(7,2),(8,4)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(0,5),(1,3),(6,3)]
  | 55 => [(4,4),(7,2),(8,2)]
  | 56 => [(0,0),(4,0),(5,0),(8,0)]
  | 57 => [(3,2),(4,5),(7,3)]
  | 58 => [(4,0),(4,2),(7,0)]
  | 59 => [(5,3),(7,3),(8,3)]
  | 60 => [(5,2),(8,5)]
  | 61 => [(1,1),(4,3),(6,1),(7,1)]
  | 62 => [(4,1),(7,5),(8,1)]
  | 63 => [(0,2),(6,0),(6,5)]
  | 64 => [(0,4),(1,1),(7,1)]
  | 65 => [(1,5),(5,1),(5,4)]
  | 66 => [(0,0),(0,1),(6,1),(6,4)]
  | 67 => [(1,2),(5,1),(6,2),(7,2)]
  | 68 => [(0,1),(7,4)]
  | 69 => [(6,2),(6,3)]
  | 70 => [(1,3),(7,3),(8,3)]
  | 71 => [(5,2),(5,5),(8,2),(8,5)]
  | 72 => [(5,0),(7,0),(8,0)]
  | 73 => [(4,3),(4,5),(8,3)]
  | 74 => [(1,5),(3,5),(5,5),(7,0),(7,5)]
  | 75 => [(0,3),(1,0),(6,1),(8,3)]
  | 76 => [(2,1),(4,1),(8,5)]
  | 77 => [(0,2),(1,0)]
  | 78 => [(0,4),(0,5),(1,2),(6,2),(6,3)]
  | 79 => [(4,4),(5,4),(7,2),(8,4)]
  | 80 => [(0,0),(1,4),(7,4)]
  | 81 => [(0,5),(6,3),(7,2)]
  | 82 => [(2,0),(2,2),(2,4),(4,4),(7,4)]
  | 83 => [(0,0),(1,3),(3,3),(6,3),(7,3)]
  | 84 => [(3,2),(5,2),(7,2),(8,2)]
  | 85 => [(1,1),(4,3),(7,1),(8,1)]
  | 86 => [(1,5),(4,1),(7,5)]
  | 87 => [(0,2),(6,0),(6,1)]
  | 88 => [(1,1),(3,1),(4,1),(7,1),(8,1)]
  | 89 => [(0,1),(0,2),(1,5),(6,5)]
  | _ => [(0,4),(1,1),(6,1),(6,2)]
def root1Node76Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,0),(2,2),(4,0)]
  | 1 => some [(3,3),(7,3)]
  | 2 => some [(5,2),(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3),(8,3)]
  | 5 => some [(4,2),(5,2),(5,5),(8,2)]
  | 6 => some [(1,1),(3,1),(5,1)]
  | 7 => some [(0,1)]
  | 8 => some [(6,2)]
  | 9 => some [(8,4)]
  | 10 => some [(1,4),(6,4)]
  | 11 => some [(0,5),(1,2)]
  | 12 => some [(4,4),(7,4),(8,4)]
  | 13 => some [(5,0),(5,3),(8,3)]
  | 14 => some [(4,5),(8,5)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3),(6,0)]
  | 19 => some [(7,1),(8,1)]
  | 20 => some [(1,5),(6,5),(7,5)]
  | 21 => some [(7,4),(8,4)]
  | 22 => some [(0,0),(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(4,2),(8,2)]
  | 27 => some [(5,0),(5,3),(8,0)]
  | 28 => some [(4,5),(7,3),(8,5)]
  | 29 => some [(4,2),(7,0),(8,2)]
  | 30 => some [(4,1),(7,1),(8,1)]
  | 31 => some [(0,2),(1,5)]
  | 32 => some [(1,1),(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(7,4),(8,4)]
  | 37 => some [(0,0),(6,3),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(4,0),(7,4),(8,4)]
  | 40 => some [(1,3),(3,3),(5,0),(5,3),(7,3)]
  | 41 => some [(4,5),(5,2),(5,5),(8,5)]
  | 42 => some [(7,0),(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(2,1),(7,1)]
  | 47 => some [(0,2),(1,5),(7,5)]
  | 48 => some [(0,3),(1,1),(6,1)]
  | 49 => some [(4,1),(5,1),(8,1)]
  | 50 => some [(0,1),(0,2),(1,5),(6,5)]
  | 51 => some [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 52 => some [(4,4),(5,4),(7,2),(8,4)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(1,3),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2)]
  | 56 => some [(0,0),(4,0),(5,0),(8,0)]
  | 57 => some [(3,2),(4,5),(7,3)]
  | 58 => some [(4,0),(4,2),(7,0)]
  | 59 => some [(5,3),(7,3),(8,3)]
  | 60 => some [(5,2),(8,5)]
  | 61 => some [(1,1),(4,3),(6,1),(7,1)]
  | 62 => some [(4,1),(7,5),(8,1)]
  | 63 => some [(0,2),(6,0),(6,5)]
  | 64 => some [(0,4),(1,1),(7,1)]
  | 65 => some [(1,5),(5,1),(5,4)]
  | 66 => some [(0,0),(0,1),(6,1),(6,4)]
  | 67 => some [(1,2),(5,1),(6,2),(7,2)]
  | 68 => some [(0,1),(7,4)]
  | 69 => some [(6,2),(6,3)]
  | 70 => some [(1,3),(7,3),(8,3)]
  | 71 => some [(5,2),(5,5),(8,2),(8,5)]
  | 72 => some [(5,0),(7,0),(8,0)]
  | 73 => some [(4,3),(4,5),(8,3)]
  | 74 => some [(1,5),(3,5),(5,5),(7,0),(7,5)]
  | 75 => some [(0,3),(1,0),(6,1),(8,3)]
  | 76 => some [(2,1),(4,1),(8,5)]
  | 77 => some [(0,2),(1,0)]
  | 78 => some [(0,4),(0,5),(1,2),(6,2),(6,3)]
  | 79 => some [(4,4),(5,4),(7,2),(8,4)]
  | 80 => some [(0,0),(1,4),(7,4)]
  | 81 => some [(0,5),(6,3),(7,2)]
  | 82 => some [(2,0),(2,2),(2,4),(4,4),(7,4)]
  | 83 => some [(0,0),(1,3),(3,3),(6,3),(7,3)]
  | 84 => some [(3,2),(5,2),(7,2),(8,2)]
  | 85 => some [(1,1),(4,3),(7,1),(8,1)]
  | 86 => some [(1,5),(4,1),(7,5)]
  | 87 => some [(0,2),(6,0),(6,1)]
  | 88 => some [(1,1),(3,1),(4,1),(7,1),(8,1)]
  | 89 => some [(0,1),(0,2),(1,5),(6,5)]
  | _ => some [(0,4),(1,1),(6,1),(6,2)]
theorem root1Node76Domains1_fast_eq : root1Node76Domains1 = expandDomains root1Node76Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node76Domains1 v = expandDomains root1Node76Domains1Fast v from by decide) v
theorem root1Node76Step1Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq (by decide)
theorem root1Node76Step1Narrowing_checked :
    checkNarrowing table25 root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkNarrowing_flatten table25Scope [table25Rows0_0,table25Rows0_1,table25Rows0_2,table25Rows0_3,table25Rows0_4,table25Rows0_5,table25Rows1_0,table25Rows1_1,table25Rows1_2,table25Rows1_3,table25Rows1_4,table25Rows1_5,table25Rows2_0,table25Rows2_1,table25Rows2_2,table25Rows2_3,table25Rows2_4,table25Rows2_5,table25Rows3_0,table25Rows3_1,table25Rows3_2,table25Rows3_3,table25Rows3_4,table25Rows3_5,table25Rows4_0,table25Rows4_1,table25Rows4_2,table25Rows4_3,table25Rows4_4,table25Rows4_5,table25Rows5_0,table25Rows5_1,table25Rows5_2,table25Rows5_3,table25Rows5_4,table25Rows5_5,table25Rows6_0,table25Rows6_1,table25Rows6_2,table25Rows6_3,table25Rows6_4,table25Rows6_5,table25Rows7_0,table25Rows7_1,table25Rows7_2,table25Rows7_3,table25Rows7_4,table25Rows7_5,table25Rows8_0,table25Rows8_1,table25Rows8_2,table25Rows8_3,table25Rows8_4,table25Rows8_5]
    root1Node76Domains0 root1Node76Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node76Step1Chunk0_0_checked, root1Node76Step1Chunk0_1_checked, root1Node76Step1Chunk0_2_checked, root1Node76Step1Chunk0_3_checked, root1Node76Step1Chunk0_4_checked, root1Node76Step1Chunk0_5_checked, root1Node76Step1Chunk1_0_checked, root1Node76Step1Chunk1_1_checked, root1Node76Step1Chunk1_2_checked, root1Node76Step1Chunk1_3_checked, root1Node76Step1Chunk1_4_checked, root1Node76Step1Chunk1_5_checked, root1Node76Step1Chunk2_0_checked, root1Node76Step1Chunk2_1_checked, root1Node76Step1Chunk2_2_checked, root1Node76Step1Chunk2_3_checked, root1Node76Step1Chunk2_4_checked, root1Node76Step1Chunk2_5_checked, root1Node76Step1Chunk3_0_checked, root1Node76Step1Chunk3_1_checked, root1Node76Step1Chunk3_2_checked, root1Node76Step1Chunk3_3_checked, root1Node76Step1Chunk3_4_checked, root1Node76Step1Chunk3_5_checked, root1Node76Step1Chunk4_0_checked, root1Node76Step1Chunk4_1_checked, root1Node76Step1Chunk4_2_checked, root1Node76Step1Chunk4_3_checked, root1Node76Step1Chunk4_4_checked, root1Node76Step1Chunk4_5_checked, root1Node76Step1Chunk5_0_checked, root1Node76Step1Chunk5_1_checked, root1Node76Step1Chunk5_2_checked, root1Node76Step1Chunk5_3_checked, root1Node76Step1Chunk5_4_checked, root1Node76Step1Chunk5_5_checked, root1Node76Step1Chunk6_0_checked, root1Node76Step1Chunk6_1_checked, root1Node76Step1Chunk6_2_checked, root1Node76Step1Chunk6_3_checked, root1Node76Step1Chunk6_4_checked, root1Node76Step1Chunk6_5_checked, root1Node76Step1Chunk7_0_checked, root1Node76Step1Chunk7_1_checked, root1Node76Step1Chunk7_2_checked, root1Node76Step1Chunk7_3_checked, root1Node76Step1Chunk7_4_checked, root1Node76Step1Chunk7_5_checked, root1Node76Step1Chunk8_0_checked, root1Node76Step1Chunk8_1_checked, root1Node76Step1Chunk8_2_checked, root1Node76Step1Chunk8_3_checked, root1Node76Step1Chunk8_4_checked, root1Node76Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node76Step1_checked :
    checkReplacement table25 root1Node76Domains0 root1Node76Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node76Domains0 root1Node76Domains1
    root1Node76Domains0Fast root1Node76Domains1Fast
    root1Node76Domains0_fast_eq root1Node76Domains1_fast_eq
    root1Node76Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
