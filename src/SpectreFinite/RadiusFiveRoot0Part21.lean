module

public import SpectreFinite.RadiusFiveRoot0Part20
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable34
public import SpectreFinite.RadiusFiveTable36
public import SpectreFinite.RadiusFiveTable52
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node47Domains0 : Domains 91 State := restrict root0Node45Domains0 60 (8,1)
def root0Node47Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,1)]
  | 5 => some [(6,5)]
  | 6 => some [(7,2)]
  | 7 => some [(4,0)]
  | 8 => some [(7,3)]
  | 9 => some [(8,2)]
  | 10 => some [(5,0)]
  | 11 => some [(4,5)]
  | 12 => some [(7,0)]
  | 13 => some [(6,1)]
  | 14 => some [(5,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(7,0)]
  | 22 => some [(8,3)]
  | 23 => some [(8,5)]
  | 24 => some [(1,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(8,1)]
  | 29 => some [(6,5)]
  | 30 => some [(7,2)]
  | 31 => some [(7,4)]
  | 32 => some [(1,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(8,3)]
  | 38 => some [(8,5)]
  | 39 => some [(7,0)]
  | 40 => some [(6,1)]
  | 41 => some [(8,1)]
  | 42 => some [(6,5)]
  | 43 => some [(0,4)]
  | 44 => some [(5,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(6,3)]
  | 49 => some [(7,2)]
  | 50 => some [(7,4)]
  | 51 => some [(8,3)]
  | 52 => some [(5,5)]
  | 53 => some [(7,0)]
  | 54 => some [(4,3)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(4,1)]
  | 58 => some [(0,2)]
  | 59 => some [(1,1)]
  | 60 => some [(8,1)]
  | 61 => some [(0,5)]
  | 62 => some [(4,4)]
  | 63 => some [(1,4)]
  | 64 => some [(0,5)]
  | 65 => some [(2,0)]
  | 66 => some [(7,3)]
  | 67 => some [(5,2)]
  | 68 => some [(8,0)]
  | 69 => some [(7,3),(8,3)]
  | 70 => some [(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(6,0)]
  | 73 => some [(3,1)]
  | 74 => some [(0,1)]
  | 75 => some [(6,2)]
  | 76 => some [(8,4)]
  | 77 => some [(1,4),(6,4)]
  | 78 => some [(7,3)]
  | 79 => some [(8,2)]
  | 80 => some [(5,0)]
  | 81 => some [(4,5)]
  | 82 => some [(1,0)]
  | 83 => some [(7,1)]
  | 84 => some [(7,5)]
  | 85 => some [(1,2)]
  | 86 => some [(8,4)]
  | 87 => some [(0,0)]
  | 88 => some [(7,2)]
  | 89 => some [(4,0)]
  | _ => some [(7,3)]
theorem root0Node47Domains0_fast_eq : root0Node47Domains0 = expandDomains root0Node47Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node47Domains0 v = expandDomains root0Node47Domains0Fast v from by decide) v
def root0Node47Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(6,0)]
  | 4 => [(7,1)]
  | 5 => [(6,5)]
  | 6 => [(7,2)]
  | 7 => [(4,0)]
  | 8 => [(7,3)]
  | 9 => [(8,2)]
  | 10 => [(5,0)]
  | 11 => [(4,5)]
  | 12 => [(7,0)]
  | 13 => [(6,1)]
  | 14 => [(5,1)]
  | 15 => [(0,1)]
  | 16 => [(6,2)]
  | 17 => [(8,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(7,4)]
  | 21 => [(7,0)]
  | 22 => [(8,3)]
  | 23 => [(8,5)]
  | 24 => [(1,0)]
  | 25 => [(7,1)]
  | 26 => [(1,5)]
  | 27 => [(6,1)]
  | 28 => [(8,1)]
  | 29 => [(6,5)]
  | 30 => [(7,2)]
  | 31 => [(7,4)]
  | 32 => [(1,3)]
  | 33 => [(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(7,0)]
  | 37 => [(8,3)]
  | 38 => [(8,5)]
  | 39 => [(7,0)]
  | 40 => [(6,1)]
  | 41 => [(8,1)]
  | 42 => [(6,5)]
  | 43 => [(0,4)]
  | 44 => [(5,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(7,4)]
  | 48 => [(6,3)]
  | 49 => [(7,2)]
  | 50 => [(7,4)]
  | 51 => [(8,3)]
  | 52 => [(5,5)]
  | 53 => [(7,0)]
  | 54 => [(4,3)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(4,1)]
  | 58 => [(0,2)]
  | 59 => [(1,1)]
  | 60 => [(8,1)]
  | 61 => [(0,5)]
  | 62 => [(4,4)]
  | 63 => [(1,4)]
  | 64 => [(0,5)]
  | 65 => [(2,0)]
  | 66 => [(7,3)]
  | 67 => [(5,2)]
  | 68 => [(8,0)]
  | 69 => [(8,3)]
  | 70 => [(7,1)]
  | 71 => [(7,5)]
  | 72 => [(6,0)]
  | 73 => [(3,1)]
  | 74 => [(0,1)]
  | 75 => [(6,2)]
  | 76 => [(8,4)]
  | 77 => [(1,4)]
  | 78 => [(7,3)]
  | 79 => [(8,2)]
  | 80 => [(5,0)]
  | 81 => [(4,5)]
  | 82 => [(1,0)]
  | 83 => [(7,1)]
  | 84 => [(7,5)]
  | 85 => [(1,2)]
  | 86 => [(8,4)]
  | 87 => [(0,0)]
  | 88 => [(7,2)]
  | 89 => [(4,0)]
  | _ => [(7,3)]
def root0Node47Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,1)]
  | 5 => some [(6,5)]
  | 6 => some [(7,2)]
  | 7 => some [(4,0)]
  | 8 => some [(7,3)]
  | 9 => some [(8,2)]
  | 10 => some [(5,0)]
  | 11 => some [(4,5)]
  | 12 => some [(7,0)]
  | 13 => some [(6,1)]
  | 14 => some [(5,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(7,0)]
  | 22 => some [(8,3)]
  | 23 => some [(8,5)]
  | 24 => some [(1,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(8,1)]
  | 29 => some [(6,5)]
  | 30 => some [(7,2)]
  | 31 => some [(7,4)]
  | 32 => some [(1,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(8,3)]
  | 38 => some [(8,5)]
  | 39 => some [(7,0)]
  | 40 => some [(6,1)]
  | 41 => some [(8,1)]
  | 42 => some [(6,5)]
  | 43 => some [(0,4)]
  | 44 => some [(5,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(6,3)]
  | 49 => some [(7,2)]
  | 50 => some [(7,4)]
  | 51 => some [(8,3)]
  | 52 => some [(5,5)]
  | 53 => some [(7,0)]
  | 54 => some [(4,3)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(4,1)]
  | 58 => some [(0,2)]
  | 59 => some [(1,1)]
  | 60 => some [(8,1)]
  | 61 => some [(0,5)]
  | 62 => some [(4,4)]
  | 63 => some [(1,4)]
  | 64 => some [(0,5)]
  | 65 => some [(2,0)]
  | 66 => some [(7,3)]
  | 67 => some [(5,2)]
  | 68 => some [(8,0)]
  | 69 => some [(8,3)]
  | 70 => some [(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(6,0)]
  | 73 => some [(3,1)]
  | 74 => some [(0,1)]
  | 75 => some [(6,2)]
  | 76 => some [(8,4)]
  | 77 => some [(1,4)]
  | 78 => some [(7,3)]
  | 79 => some [(8,2)]
  | 80 => some [(5,0)]
  | 81 => some [(4,5)]
  | 82 => some [(1,0)]
  | 83 => some [(7,1)]
  | 84 => some [(7,5)]
  | 85 => some [(1,2)]
  | 86 => some [(8,4)]
  | 87 => some [(0,0)]
  | 88 => some [(7,2)]
  | 89 => some [(4,0)]
  | _ => some [(7,3)]
theorem root0Node47Domains1_fast_eq : root0Node47Domains1 = expandDomains root0Node47Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node47Domains1 v = expandDomains root0Node47Domains1Fast v from by decide) v
theorem root0Node47Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq (by decide)
theorem root0Node47Step1Narrowing_checked :
    checkNarrowing table36 root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root0Node47Domains0 root0Node47Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node47Step1Chunk0_0_checked, root0Node47Step1Chunk0_1_checked, root0Node47Step1Chunk0_2_checked, root0Node47Step1Chunk0_3_checked, root0Node47Step1Chunk0_4_checked, root0Node47Step1Chunk0_5_checked, root0Node47Step1Chunk1_0_checked, root0Node47Step1Chunk1_1_checked, root0Node47Step1Chunk1_2_checked, root0Node47Step1Chunk1_3_checked, root0Node47Step1Chunk1_4_checked, root0Node47Step1Chunk1_5_checked, root0Node47Step1Chunk2_0_checked, root0Node47Step1Chunk2_1_checked, root0Node47Step1Chunk2_2_checked, root0Node47Step1Chunk2_3_checked, root0Node47Step1Chunk2_4_checked, root0Node47Step1Chunk2_5_checked, root0Node47Step1Chunk3_0_checked, root0Node47Step1Chunk3_1_checked, root0Node47Step1Chunk3_2_checked, root0Node47Step1Chunk3_3_checked, root0Node47Step1Chunk3_4_checked, root0Node47Step1Chunk3_5_checked, root0Node47Step1Chunk4_0_checked, root0Node47Step1Chunk4_1_checked, root0Node47Step1Chunk4_2_checked, root0Node47Step1Chunk4_3_checked, root0Node47Step1Chunk4_4_checked, root0Node47Step1Chunk4_5_checked, root0Node47Step1Chunk5_0_checked, root0Node47Step1Chunk5_1_checked, root0Node47Step1Chunk5_2_checked, root0Node47Step1Chunk5_3_checked, root0Node47Step1Chunk5_4_checked, root0Node47Step1Chunk5_5_checked, root0Node47Step1Chunk6_0_checked, root0Node47Step1Chunk6_1_checked, root0Node47Step1Chunk6_2_checked, root0Node47Step1Chunk6_3_checked, root0Node47Step1Chunk6_4_checked, root0Node47Step1Chunk6_5_checked, root0Node47Step1Chunk7_0_checked, root0Node47Step1Chunk7_1_checked, root0Node47Step1Chunk7_2_checked, root0Node47Step1Chunk7_3_checked, root0Node47Step1Chunk7_4_checked, root0Node47Step1Chunk7_5_checked, root0Node47Step1Chunk8_0_checked, root0Node47Step1Chunk8_1_checked, root0Node47Step1Chunk8_2_checked, root0Node47Step1Chunk8_3_checked, root0Node47Step1Chunk8_4_checked, root0Node47Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node47Step1_checked :
    checkReplacement table36 root0Node47Domains0 root0Node47Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node47Domains0 root0Node47Domains1
    root0Node47Domains0Fast root0Node47Domains1Fast
    root0Node47Domains0_fast_eq root0Node47Domains1_fast_eq
    root0Node47Step1Narrowing_checked (by decide)
theorem root0Node47Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node47Domains1 (.output 23) = true := by decide
def root0Node48Domains0 : Domains 91 State := restrict root0Node26Domains2 32 (7,3)
def root0Node48Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0),(6,5)]
  | 1 => some [(0,4),(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 3 => some [(0,0),(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 4 => some [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 5 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 6 => some [(1,2),(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 7 => some [(4,0),(7,0),(8,0)]
  | 8 => some [(4,3),(7,3),(8,3)]
  | 9 => some [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 10 => some [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 11 => some [(2,1),(2,5),(4,1),(4,5)]
  | 12 => some [(0,2),(1,0),(6,0),(7,0)]
  | 13 => some [(0,3),(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 14 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 15 => some [(0,1),(1,4),(7,4)]
  | 16 => some [(0,5),(6,2),(6,3)]
  | 17 => some [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 18 => some [(0,0),(1,3),(3,3),(7,3)]
  | 19 => some [(3,2),(5,2),(7,2)]
  | 20 => some [(4,0),(7,4),(8,0)]
  | 21 => some [(0,2),(1,0),(4,2),(6,0),(7,0)]
  | 22 => some [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 23 => some [(4,1),(7,5),(8,5)]
  | 24 => some [(0,2),(1,0),(6,0)]
  | 25 => some [(1,1),(3,1),(7,1)]
  | 26 => some [(0,1),(1,5),(6,5)]
  | 27 => some [(0,4),(6,1),(6,2)]
  | 28 => some [(5,1),(5,4),(8,1),(8,4)]
  | 29 => some [(0,1),(1,4),(6,4),(6,5)]
  | 30 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 31 => some [(4,0),(7,4),(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(5,2),(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(1,0),(7,0)]
  | 37 => some [(4,3),(7,1),(8,3)]
  | 38 => some [(7,5),(8,5)]
  | 39 => some [(0,3),(1,0),(6,0),(7,0)]
  | 40 => some [(0,3),(0,4),(1,1),(6,1),(6,2)]
  | 41 => some [(5,1),(5,4),(8,1),(8,4)]
  | 42 => some [(0,1),(6,4),(6,5)]
  | 43 => some [(0,4),(1,2),(6,2)]
  | 44 => some [(5,4),(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0),(7,4)]
  | 48 => some [(1,3),(6,3),(7,3)]
  | 49 => some [(4,2),(7,2),(8,2)]
  | 50 => some [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 51 => some [(4,3),(5,3),(7,1),(8,3)]
  | 52 => some [(5,5),(7,5),(8,5)]
  | 53 => some [(0,3),(1,0),(7,0)]
  | 54 => some [(4,3),(7,1),(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(4,1),(5,1),(8,1)]
  | 58 => some [(0,1),(0,2),(6,5)]
  | 59 => some [(0,4),(1,1),(6,2)]
  | 60 => some [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(8,1),(8,4)]
  | 61 => some [(0,5),(1,3),(7,3)]
  | 62 => some [(4,2),(4,4),(8,2)]
  | 63 => some [(1,4),(5,0),(5,3)]
  | 64 => some [(0,5),(4,5),(5,5),(8,5)]
  | 65 => some [(2,0),(7,0)]
  | 66 => some [(7,3),(8,3)]
  | 67 => some [(5,2),(5,5),(8,5)]
  | 68 => some [(1,0),(3,0),(7,0),(8,0)]
  | 69 => some [(2,1),(2,3),(2,5),(4,3),(7,1),(7,3),(8,3)]
  | 70 => some [(0,4),(1,2),(6,2),(7,1)]
  | 71 => some [(1,4),(3,4),(5,4),(7,4),(7,5)]
  | 72 => some [(0,0),(0,5),(6,0),(6,3)]
  | 73 => some [(3,1),(4,4),(7,2)]
  | 74 => some [(0,1),(1,4),(7,4)]
  | 75 => some [(0,5),(1,3),(6,2),(6,3)]
  | 76 => some [(4,4),(7,2),(8,2),(8,4)]
  | 77 => some [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 78 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,3)]
  | 79 => some [(0,2),(1,5),(6,0),(8,2)]
  | 80 => some [(1,1),(5,0),(6,1),(7,1)]
  | 81 => some [(4,1),(4,5),(7,5),(8,1)]
  | 82 => some [(0,2),(1,0),(6,0),(6,5)]
  | 83 => some [(0,4),(1,1),(7,1)]
  | 84 => some [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 85 => some [(0,5),(1,2),(3,2),(5,2),(6,2),(7,2)]
  | 86 => some [(2,0),(4,0),(8,0),(8,4)]
  | 87 => some [(0,0),(7,3),(8,3)]
  | 88 => some [(5,2),(5,5),(7,2),(8,2)]
  | 89 => some [(4,0),(5,0),(7,0),(8,0)]
  | _ => some [(4,3),(4,5),(7,3),(8,3)]
theorem root0Node48Domains0_fast_eq : root0Node48Domains0 = expandDomains root0Node48Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node48Domains0 v = expandDomains root0Node48Domains0Fast v from by decide) v
def root0Node48Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,2),(1,5),(6,5)]
  | 1 => [(0,4),(1,1),(6,1)]
  | 2 => [(5,1),(5,4),(8,1)]
  | 3 => [(0,0),(0,1),(6,4),(6,5)]
  | 4 => [(0,4),(1,2),(6,2),(7,2)]
  | 5 => [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 6 => [(5,2),(5,5),(8,5)]
  | 7 => [(7,0),(8,0)]
  | 8 => [(4,3),(8,3)]
  | 9 => [(1,5),(3,5),(5,5),(7,5)]
  | 10 => [(0,3),(1,0),(3,0),(6,1)]
  | 11 => [(2,1),(2,5),(4,1)]
  | 12 => [(0,2),(1,0),(6,0),(7,0)]
  | 13 => [(0,5),(6,2),(6,3)]
  | 14 => [(4,4),(7,2),(8,4)]
  | 15 => [(1,4),(7,4)]
  | 16 => [(0,5),(6,3)]
  | 17 => [(2,0),(2,2),(2,4),(4,4)]
  | 18 => [(0,0),(1,3),(3,3),(7,3)]
  | 19 => [(3,2),(5,2),(7,2)]
  | 20 => [(4,0),(7,4),(8,0)]
  | 21 => [(0,2),(1,0),(6,0)]
  | 22 => [(1,1),(7,1)]
  | 23 => [(4,1),(7,5)]
  | 24 => [(0,2),(6,0)]
  | 25 => [(1,1),(3,1),(7,1)]
  | 26 => [(0,1),(1,5),(6,5)]
  | 27 => [(0,4),(6,1),(6,2)]
  | 28 => [(5,1),(5,4),(8,4)]
  | 29 => [(0,1),(1,4),(6,4),(6,5)]
  | 30 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 31 => [(4,0),(8,0)]
  | 32 => [(7,3)]
  | 33 => [(5,2),(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(1,0),(7,0)]
  | 37 => [(4,3),(7,1),(8,3)]
  | 38 => [(7,5),(8,5)]
  | 39 => [(0,3),(1,0),(6,0),(7,0)]
  | 40 => [(0,3),(0,4),(1,1),(6,1),(6,2)]
  | 41 => [(5,1),(5,4),(8,4)]
  | 42 => [(0,1),(6,4)]
  | 43 => [(1,2),(6,2)]
  | 44 => [(8,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(4,0),(7,4)]
  | 48 => [(1,3),(7,3)]
  | 49 => [(4,2),(7,2),(8,2)]
  | 50 => [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 51 => [(4,3),(5,3),(7,1),(8,3)]
  | 52 => [(7,5),(8,5)]
  | 53 => [(0,3),(1,0)]
  | 54 => [(7,1),(8,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(5,1),(8,1)]
  | 58 => [(0,1),(6,5)]
  | 59 => [(0,4),(1,1),(6,2)]
  | 60 => [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(8,1),(8,4)]
  | 61 => [(0,5),(1,3),(7,3)]
  | 62 => [(4,2),(8,2)]
  | 63 => [(5,0),(5,3)]
  | 64 => [(4,5),(5,5),(8,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(5,5),(8,5)]
  | 68 => [(1,0),(3,0),(7,0),(8,0)]
  | 69 => [(2,1),(2,3),(2,5),(4,3),(7,1),(7,3),(8,3)]
  | 70 => [(0,4),(1,2),(6,2),(7,1)]
  | 71 => [(1,4),(3,4),(5,4),(7,4)]
  | 72 => [(0,0),(0,5),(6,3)]
  | 73 => [(4,4),(7,2)]
  | 74 => [(1,4),(7,4)]
  | 75 => [(0,5),(1,3),(6,3)]
  | 76 => [(4,4),(7,2),(8,2),(8,4)]
  | 77 => [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 78 => [(2,1),(2,3),(2,5),(4,1),(4,3),(7,3)]
  | 79 => [(0,2),(1,5),(6,0),(8,2)]
  | 80 => [(1,1),(5,0),(6,1),(7,1)]
  | 81 => [(4,1),(4,5),(7,5),(8,1)]
  | 82 => [(0,2),(1,0),(6,0),(6,5)]
  | 83 => [(0,4),(1,1),(7,1)]
  | 84 => [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 85 => [(0,5),(1,2),(3,2),(5,2),(6,2),(7,2)]
  | 86 => [(2,0),(4,0),(8,0),(8,4)]
  | 87 => [(0,0),(7,3),(8,3)]
  | 88 => [(5,2),(5,5),(7,2),(8,2)]
  | 89 => [(4,0),(5,0),(7,0),(8,0)]
  | _ => [(4,3),(4,5),(7,3),(8,3)]
def root0Node48Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5),(6,5)]
  | 1 => some [(0,4),(1,1),(6,1)]
  | 2 => some [(5,1),(5,4),(8,1)]
  | 3 => some [(0,0),(0,1),(6,4),(6,5)]
  | 4 => some [(0,4),(1,2),(6,2),(7,2)]
  | 5 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 6 => some [(5,2),(5,5),(8,5)]
  | 7 => some [(7,0),(8,0)]
  | 8 => some [(4,3),(8,3)]
  | 9 => some [(1,5),(3,5),(5,5),(7,5)]
  | 10 => some [(0,3),(1,0),(3,0),(6,1)]
  | 11 => some [(2,1),(2,5),(4,1)]
  | 12 => some [(0,2),(1,0),(6,0),(7,0)]
  | 13 => some [(0,5),(6,2),(6,3)]
  | 14 => some [(4,4),(7,2),(8,4)]
  | 15 => some [(1,4),(7,4)]
  | 16 => some [(0,5),(6,3)]
  | 17 => some [(2,0),(2,2),(2,4),(4,4)]
  | 18 => some [(0,0),(1,3),(3,3),(7,3)]
  | 19 => some [(3,2),(5,2),(7,2)]
  | 20 => some [(4,0),(7,4),(8,0)]
  | 21 => some [(0,2),(1,0),(6,0)]
  | 22 => some [(1,1),(7,1)]
  | 23 => some [(4,1),(7,5)]
  | 24 => some [(0,2),(6,0)]
  | 25 => some [(1,1),(3,1),(7,1)]
  | 26 => some [(0,1),(1,5),(6,5)]
  | 27 => some [(0,4),(6,1),(6,2)]
  | 28 => some [(5,1),(5,4),(8,4)]
  | 29 => some [(0,1),(1,4),(6,4),(6,5)]
  | 30 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 31 => some [(4,0),(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(5,2),(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(1,0),(7,0)]
  | 37 => some [(4,3),(7,1),(8,3)]
  | 38 => some [(7,5),(8,5)]
  | 39 => some [(0,3),(1,0),(6,0),(7,0)]
  | 40 => some [(0,3),(0,4),(1,1),(6,1),(6,2)]
  | 41 => some [(5,1),(5,4),(8,4)]
  | 42 => some [(0,1),(6,4)]
  | 43 => some [(1,2),(6,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0),(7,4)]
  | 48 => some [(1,3),(7,3)]
  | 49 => some [(4,2),(7,2),(8,2)]
  | 50 => some [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 51 => some [(4,3),(5,3),(7,1),(8,3)]
  | 52 => some [(7,5),(8,5)]
  | 53 => some [(0,3),(1,0)]
  | 54 => some [(7,1),(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1),(8,1)]
  | 58 => some [(0,1),(6,5)]
  | 59 => some [(0,4),(1,1),(6,2)]
  | 60 => some [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(8,1),(8,4)]
  | 61 => some [(0,5),(1,3),(7,3)]
  | 62 => some [(4,2),(8,2)]
  | 63 => some [(5,0),(5,3)]
  | 64 => some [(4,5),(5,5),(8,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(5,5),(8,5)]
  | 68 => some [(1,0),(3,0),(7,0),(8,0)]
  | 69 => some [(2,1),(2,3),(2,5),(4,3),(7,1),(7,3),(8,3)]
  | 70 => some [(0,4),(1,2),(6,2),(7,1)]
  | 71 => some [(1,4),(3,4),(5,4),(7,4)]
  | 72 => some [(0,0),(0,5),(6,3)]
  | 73 => some [(4,4),(7,2)]
  | 74 => some [(1,4),(7,4)]
  | 75 => some [(0,5),(1,3),(6,3)]
  | 76 => some [(4,4),(7,2),(8,2),(8,4)]
  | 77 => some [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 78 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,3)]
  | 79 => some [(0,2),(1,5),(6,0),(8,2)]
  | 80 => some [(1,1),(5,0),(6,1),(7,1)]
  | 81 => some [(4,1),(4,5),(7,5),(8,1)]
  | 82 => some [(0,2),(1,0),(6,0),(6,5)]
  | 83 => some [(0,4),(1,1),(7,1)]
  | 84 => some [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 85 => some [(0,5),(1,2),(3,2),(5,2),(6,2),(7,2)]
  | 86 => some [(2,0),(4,0),(8,0),(8,4)]
  | 87 => some [(0,0),(7,3),(8,3)]
  | 88 => some [(5,2),(5,5),(7,2),(8,2)]
  | 89 => some [(4,0),(5,0),(7,0),(8,0)]
  | _ => some [(4,3),(4,5),(7,3),(8,3)]
theorem root0Node48Domains1_fast_eq : root0Node48Domains1 = expandDomains root0Node48Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node48Domains1 v = expandDomains root0Node48Domains1Fast v from by decide) v
theorem root0Node48Step1Chunk0_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_0⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk0_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_1⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk0_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_2⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk0_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_3⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk0_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_4⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk0_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_5⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk1_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_0⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk1_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_1⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk1_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_2⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk1_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_3⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk1_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_4⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk1_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_5⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk2_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_0⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk2_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_1⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk2_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_2⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk2_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_3⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk2_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_4⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk2_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_5⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk3_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_0⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk3_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_1⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk3_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_2⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk3_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_3⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk3_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_4⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk3_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_5⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk4_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_0⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk4_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_1⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk4_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_2⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk4_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_3⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk4_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_4⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk4_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_5⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk5_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_0⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk5_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_1⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk5_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_2⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk5_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_3⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk5_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_4⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk5_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_5⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk6_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows6_0⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk6_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows6_1⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk6_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows6_2⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk6_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows6_3⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk6_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows6_4⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk6_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows6_5⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk7_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows7_0⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk7_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows7_1⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk7_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows7_2⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk7_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows7_3⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk7_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows7_4⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk7_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows7_5⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk8_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_0⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk8_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_1⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk8_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_2⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk8_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_3⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk8_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_4⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Chunk8_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_5⟩
      root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq (by decide)
theorem root0Node48Step1Narrowing_checked :
    checkNarrowing table34 root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkNarrowing_flatten table34Scope [table34Rows0_0,table34Rows0_1,table34Rows0_2,table34Rows0_3,table34Rows0_4,table34Rows0_5,table34Rows1_0,table34Rows1_1,table34Rows1_2,table34Rows1_3,table34Rows1_4,table34Rows1_5,table34Rows2_0,table34Rows2_1,table34Rows2_2,table34Rows2_3,table34Rows2_4,table34Rows2_5,table34Rows3_0,table34Rows3_1,table34Rows3_2,table34Rows3_3,table34Rows3_4,table34Rows3_5,table34Rows4_0,table34Rows4_1,table34Rows4_2,table34Rows4_3,table34Rows4_4,table34Rows4_5,table34Rows5_0,table34Rows5_1,table34Rows5_2,table34Rows5_3,table34Rows5_4,table34Rows5_5,table34Rows6_0,table34Rows6_1,table34Rows6_2,table34Rows6_3,table34Rows6_4,table34Rows6_5,table34Rows7_0,table34Rows7_1,table34Rows7_2,table34Rows7_3,table34Rows7_4,table34Rows7_5,table34Rows8_0,table34Rows8_1,table34Rows8_2,table34Rows8_3,table34Rows8_4,table34Rows8_5]
    root0Node48Domains0 root0Node48Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node48Step1Chunk0_0_checked, root0Node48Step1Chunk0_1_checked, root0Node48Step1Chunk0_2_checked, root0Node48Step1Chunk0_3_checked, root0Node48Step1Chunk0_4_checked, root0Node48Step1Chunk0_5_checked, root0Node48Step1Chunk1_0_checked, root0Node48Step1Chunk1_1_checked, root0Node48Step1Chunk1_2_checked, root0Node48Step1Chunk1_3_checked, root0Node48Step1Chunk1_4_checked, root0Node48Step1Chunk1_5_checked, root0Node48Step1Chunk2_0_checked, root0Node48Step1Chunk2_1_checked, root0Node48Step1Chunk2_2_checked, root0Node48Step1Chunk2_3_checked, root0Node48Step1Chunk2_4_checked, root0Node48Step1Chunk2_5_checked, root0Node48Step1Chunk3_0_checked, root0Node48Step1Chunk3_1_checked, root0Node48Step1Chunk3_2_checked, root0Node48Step1Chunk3_3_checked, root0Node48Step1Chunk3_4_checked, root0Node48Step1Chunk3_5_checked, root0Node48Step1Chunk4_0_checked, root0Node48Step1Chunk4_1_checked, root0Node48Step1Chunk4_2_checked, root0Node48Step1Chunk4_3_checked, root0Node48Step1Chunk4_4_checked, root0Node48Step1Chunk4_5_checked, root0Node48Step1Chunk5_0_checked, root0Node48Step1Chunk5_1_checked, root0Node48Step1Chunk5_2_checked, root0Node48Step1Chunk5_3_checked, root0Node48Step1Chunk5_4_checked, root0Node48Step1Chunk5_5_checked, root0Node48Step1Chunk6_0_checked, root0Node48Step1Chunk6_1_checked, root0Node48Step1Chunk6_2_checked, root0Node48Step1Chunk6_3_checked, root0Node48Step1Chunk6_4_checked, root0Node48Step1Chunk6_5_checked, root0Node48Step1Chunk7_0_checked, root0Node48Step1Chunk7_1_checked, root0Node48Step1Chunk7_2_checked, root0Node48Step1Chunk7_3_checked, root0Node48Step1Chunk7_4_checked, root0Node48Step1Chunk7_5_checked, root0Node48Step1Chunk8_0_checked, root0Node48Step1Chunk8_1_checked, root0Node48Step1Chunk8_2_checked, root0Node48Step1Chunk8_3_checked, root0Node48Step1Chunk8_4_checked, root0Node48Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node48Step1_checked :
    checkReplacement table34 root0Node48Domains0 root0Node48Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node48Domains0 root0Node48Domains1
    root0Node48Domains0Fast root0Node48Domains1Fast
    root0Node48Domains0_fast_eq root0Node48Domains1_fast_eq
    root0Node48Step1Narrowing_checked (by decide)
def root0Node48Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,2),(1,5),(6,5)]
  | 1 => [(0,4),(1,1),(6,1)]
  | 2 => [(5,1),(5,4),(8,1)]
  | 3 => [(0,0),(0,1),(6,4),(6,5)]
  | 4 => [(0,4),(1,2),(6,2),(7,2)]
  | 5 => [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 6 => [(5,2),(5,5),(8,5)]
  | 7 => [(7,0),(8,0)]
  | 8 => [(4,3),(8,3)]
  | 9 => [(1,5),(3,5),(5,5),(7,5)]
  | 10 => [(0,3),(1,0),(3,0),(6,1)]
  | 11 => [(2,1),(2,5),(4,1)]
  | 12 => [(0,2),(1,0),(6,0),(7,0)]
  | 13 => [(0,5),(6,2),(6,3)]
  | 14 => [(4,4),(7,2),(8,4)]
  | 15 => [(1,4),(7,4)]
  | 16 => [(0,5),(6,3)]
  | 17 => [(2,0),(2,2),(2,4),(4,4)]
  | 18 => [(0,0),(1,3),(3,3),(7,3)]
  | 19 => [(3,2),(5,2),(7,2)]
  | 20 => [(4,0),(8,0)]
  | 21 => [(0,2),(1,0),(6,0)]
  | 22 => [(1,1),(7,1)]
  | 23 => [(4,1),(7,5)]
  | 24 => [(0,2),(6,0)]
  | 25 => [(1,1),(3,1),(7,1)]
  | 26 => [(0,1),(1,5),(6,5)]
  | 27 => [(0,4),(6,1),(6,2)]
  | 28 => [(5,1),(5,4),(8,4)]
  | 29 => [(0,1),(1,4),(6,4)]
  | 30 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 31 => [(4,0),(8,0)]
  | 32 => [(7,3)]
  | 33 => [(5,2),(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(1,0),(7,0)]
  | 37 => [(4,3),(7,1),(8,3)]
  | 38 => [(7,5),(8,5)]
  | 39 => [(0,3),(1,0),(6,0)]
  | 40 => [(0,3),(0,4),(1,1),(6,1),(6,2)]
  | 41 => [(5,1),(5,4),(8,4)]
  | 42 => [(0,1),(6,4)]
  | 43 => [(1,2),(6,2)]
  | 44 => [(8,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(4,0),(7,4)]
  | 48 => [(1,3),(7,3)]
  | 49 => [(4,2),(8,2)]
  | 50 => [(5,0),(5,3),(8,0)]
  | 51 => [(4,3),(5,3),(7,1),(8,3)]
  | 52 => [(7,5),(8,5)]
  | 53 => [(0,3),(1,0)]
  | 54 => [(7,1),(8,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(5,1),(8,1)]
  | 58 => [(0,1),(6,5)]
  | 59 => [(0,4),(6,2)]
  | 60 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 61 => [(0,5),(1,3),(7,3)]
  | 62 => [(4,2),(8,2)]
  | 63 => [(5,0),(5,3)]
  | 64 => [(4,5),(5,5),(8,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(5,5),(8,5)]
  | 68 => [(1,0),(3,0),(7,0)]
  | 69 => [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 70 => [(0,4),(1,2),(6,2),(7,1)]
  | 71 => [(1,4),(3,4),(5,4),(7,4)]
  | 72 => [(0,0),(0,5),(6,3)]
  | 73 => [(4,4),(7,2)]
  | 74 => [(1,4),(7,4)]
  | 75 => [(0,5),(1,3),(6,3)]
  | 76 => [(4,4),(7,2),(8,2)]
  | 77 => [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 78 => [(2,1),(2,3),(2,5),(4,1),(4,3),(7,3)]
  | 79 => [(0,2),(1,5),(6,0),(8,2)]
  | 80 => [(1,1),(6,1),(7,1)]
  | 81 => [(4,1),(7,5),(8,1)]
  | 82 => [(0,2),(6,0),(6,5)]
  | 83 => [(0,4),(1,1),(7,1)]
  | 84 => [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 85 => [(0,5),(1,2),(3,2),(5,2),(6,2),(7,2)]
  | 86 => [(2,0),(4,0),(8,0),(8,4)]
  | 87 => [(7,3),(8,3)]
  | 88 => [(5,2),(5,5),(8,2)]
  | 89 => [(5,0),(7,0),(8,0)]
  | _ => [(4,3),(4,5),(7,3),(8,3)]
def root0Node48Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5),(6,5)]
  | 1 => some [(0,4),(1,1),(6,1)]
  | 2 => some [(5,1),(5,4),(8,1)]
  | 3 => some [(0,0),(0,1),(6,4),(6,5)]
  | 4 => some [(0,4),(1,2),(6,2),(7,2)]
  | 5 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 6 => some [(5,2),(5,5),(8,5)]
  | 7 => some [(7,0),(8,0)]
  | 8 => some [(4,3),(8,3)]
  | 9 => some [(1,5),(3,5),(5,5),(7,5)]
  | 10 => some [(0,3),(1,0),(3,0),(6,1)]
  | 11 => some [(2,1),(2,5),(4,1)]
  | 12 => some [(0,2),(1,0),(6,0),(7,0)]
  | 13 => some [(0,5),(6,2),(6,3)]
  | 14 => some [(4,4),(7,2),(8,4)]
  | 15 => some [(1,4),(7,4)]
  | 16 => some [(0,5),(6,3)]
  | 17 => some [(2,0),(2,2),(2,4),(4,4)]
  | 18 => some [(0,0),(1,3),(3,3),(7,3)]
  | 19 => some [(3,2),(5,2),(7,2)]
  | 20 => some [(4,0),(8,0)]
  | 21 => some [(0,2),(1,0),(6,0)]
  | 22 => some [(1,1),(7,1)]
  | 23 => some [(4,1),(7,5)]
  | 24 => some [(0,2),(6,0)]
  | 25 => some [(1,1),(3,1),(7,1)]
  | 26 => some [(0,1),(1,5),(6,5)]
  | 27 => some [(0,4),(6,1),(6,2)]
  | 28 => some [(5,1),(5,4),(8,4)]
  | 29 => some [(0,1),(1,4),(6,4)]
  | 30 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 31 => some [(4,0),(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(5,2),(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(1,0),(7,0)]
  | 37 => some [(4,3),(7,1),(8,3)]
  | 38 => some [(7,5),(8,5)]
  | 39 => some [(0,3),(1,0),(6,0)]
  | 40 => some [(0,3),(0,4),(1,1),(6,1),(6,2)]
  | 41 => some [(5,1),(5,4),(8,4)]
  | 42 => some [(0,1),(6,4)]
  | 43 => some [(1,2),(6,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0),(7,4)]
  | 48 => some [(1,3),(7,3)]
  | 49 => some [(4,2),(8,2)]
  | 50 => some [(5,0),(5,3),(8,0)]
  | 51 => some [(4,3),(5,3),(7,1),(8,3)]
  | 52 => some [(7,5),(8,5)]
  | 53 => some [(0,3),(1,0)]
  | 54 => some [(7,1),(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1),(8,1)]
  | 58 => some [(0,1),(6,5)]
  | 59 => some [(0,4),(6,2)]
  | 60 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 61 => some [(0,5),(1,3),(7,3)]
  | 62 => some [(4,2),(8,2)]
  | 63 => some [(5,0),(5,3)]
  | 64 => some [(4,5),(5,5),(8,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(5,5),(8,5)]
  | 68 => some [(1,0),(3,0),(7,0)]
  | 69 => some [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 70 => some [(0,4),(1,2),(6,2),(7,1)]
  | 71 => some [(1,4),(3,4),(5,4),(7,4)]
  | 72 => some [(0,0),(0,5),(6,3)]
  | 73 => some [(4,4),(7,2)]
  | 74 => some [(1,4),(7,4)]
  | 75 => some [(0,5),(1,3),(6,3)]
  | 76 => some [(4,4),(7,2),(8,2)]
  | 77 => some [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 78 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,3)]
  | 79 => some [(0,2),(1,5),(6,0),(8,2)]
  | 80 => some [(1,1),(6,1),(7,1)]
  | 81 => some [(4,1),(7,5),(8,1)]
  | 82 => some [(0,2),(6,0),(6,5)]
  | 83 => some [(0,4),(1,1),(7,1)]
  | 84 => some [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 85 => some [(0,5),(1,2),(3,2),(5,2),(6,2),(7,2)]
  | 86 => some [(2,0),(4,0),(8,0),(8,4)]
  | 87 => some [(7,3),(8,3)]
  | 88 => some [(5,2),(5,5),(8,2)]
  | 89 => some [(5,0),(7,0),(8,0)]
  | _ => some [(4,3),(4,5),(7,3),(8,3)]
theorem root0Node48Domains2_fast_eq : root0Node48Domains2 = expandDomains root0Node48Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node48Domains2 v = expandDomains root0Node48Domains2Fast v from by decide) v
theorem root0Node48Step2Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq (by decide)
theorem root0Node48Step2Narrowing_checked :
    checkNarrowing table57 root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root0Node48Domains1 root0Node48Domains2 (by
      simp only [List.all_cons, List.all_nil, root0Node48Step2Chunk0_0_checked, root0Node48Step2Chunk0_1_checked, root0Node48Step2Chunk0_2_checked, root0Node48Step2Chunk0_3_checked, root0Node48Step2Chunk0_4_checked, root0Node48Step2Chunk0_5_checked, root0Node48Step2Chunk1_0_checked, root0Node48Step2Chunk1_1_checked, root0Node48Step2Chunk1_2_checked, root0Node48Step2Chunk1_3_checked, root0Node48Step2Chunk1_4_checked, root0Node48Step2Chunk1_5_checked, root0Node48Step2Chunk2_0_checked, root0Node48Step2Chunk2_1_checked, root0Node48Step2Chunk2_2_checked, root0Node48Step2Chunk2_3_checked, root0Node48Step2Chunk2_4_checked, root0Node48Step2Chunk2_5_checked, root0Node48Step2Chunk3_0_checked, root0Node48Step2Chunk3_1_checked, root0Node48Step2Chunk3_2_checked, root0Node48Step2Chunk3_3_checked, root0Node48Step2Chunk3_4_checked, root0Node48Step2Chunk3_5_checked, root0Node48Step2Chunk4_0_checked, root0Node48Step2Chunk4_1_checked, root0Node48Step2Chunk4_2_checked, root0Node48Step2Chunk4_3_checked, root0Node48Step2Chunk4_4_checked, root0Node48Step2Chunk4_5_checked, root0Node48Step2Chunk5_0_checked, root0Node48Step2Chunk5_1_checked, root0Node48Step2Chunk5_2_checked, root0Node48Step2Chunk5_3_checked, root0Node48Step2Chunk5_4_checked, root0Node48Step2Chunk5_5_checked, root0Node48Step2Chunk6_0_checked, root0Node48Step2Chunk6_1_checked, root0Node48Step2Chunk6_2_checked, root0Node48Step2Chunk6_3_checked, root0Node48Step2Chunk6_4_checked, root0Node48Step2Chunk6_5_checked, root0Node48Step2Chunk7_0_checked, root0Node48Step2Chunk7_1_checked, root0Node48Step2Chunk7_2_checked, root0Node48Step2Chunk7_3_checked, root0Node48Step2Chunk7_4_checked, root0Node48Step2Chunk7_5_checked, root0Node48Step2Chunk8_0_checked, root0Node48Step2Chunk8_1_checked, root0Node48Step2Chunk8_2_checked, root0Node48Step2Chunk8_3_checked, root0Node48Step2Chunk8_4_checked, root0Node48Step2Chunk8_5_checked, Bool.true_and])
theorem root0Node48Step2_checked :
    checkReplacement table57 root0Node48Domains1 root0Node48Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root0Node48Domains1 root0Node48Domains2
    root0Node48Domains1Fast root0Node48Domains2Fast
    root0Node48Domains1_fast_eq root0Node48Domains2_fast_eq
    root0Node48Step2Narrowing_checked (by decide)
def root0Node48Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,2),(1,5),(6,5)]
  | 1 => [(0,4),(1,1),(6,1)]
  | 2 => [(5,1),(5,4),(8,1)]
  | 3 => [(0,0),(0,1),(6,4),(6,5)]
  | 4 => [(0,4),(1,2),(6,2),(7,2)]
  | 5 => [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 6 => [(5,2),(5,5),(8,5)]
  | 7 => [(7,0),(8,0)]
  | 8 => [(4,3),(8,3)]
  | 9 => [(1,5),(3,5),(5,5),(7,5)]
  | 10 => [(0,3),(1,0),(3,0),(6,1)]
  | 11 => [(2,1),(2,5),(4,1)]
  | 12 => [(0,2),(1,0),(6,0),(7,0)]
  | 13 => [(0,5),(6,2),(6,3)]
  | 14 => [(4,4),(7,2),(8,4)]
  | 15 => [(1,4),(7,4)]
  | 16 => [(0,5),(6,3)]
  | 17 => [(2,0),(2,2),(2,4),(4,4)]
  | 18 => [(0,0),(1,3),(3,3),(7,3)]
  | 19 => [(3,2),(5,2),(7,2)]
  | 20 => [(4,0),(8,0)]
  | 21 => [(0,2),(1,0),(6,0)]
  | 22 => [(1,1),(7,1)]
  | 23 => [(4,1),(7,5)]
  | 24 => [(0,2),(6,0)]
  | 25 => [(1,1),(3,1),(7,1)]
  | 26 => [(0,1),(1,5),(6,5)]
  | 27 => [(0,4),(6,1),(6,2)]
  | 28 => [(5,1),(5,4),(8,4)]
  | 29 => [(0,1),(1,4),(6,4)]
  | 30 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 31 => [(4,0),(8,0)]
  | 32 => [(7,3)]
  | 33 => [(5,2),(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(1,0),(7,0)]
  | 37 => [(4,3),(7,1),(8,3)]
  | 38 => [(7,5),(8,5)]
  | 39 => [(0,3),(1,0),(6,0)]
  | 40 => [(0,3),(0,4),(6,1),(6,2)]
  | 41 => [(5,1),(5,4),(8,4)]
  | 42 => [(0,1),(6,4)]
  | 43 => [(1,2),(6,2)]
  | 44 => [(8,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(4,0),(7,4)]
  | 48 => [(1,3),(7,3)]
  | 49 => [(4,2),(8,2)]
  | 50 => [(5,0),(5,3),(8,0)]
  | 51 => [(4,3),(5,3),(7,1),(8,3)]
  | 52 => [(7,5),(8,5)]
  | 53 => [(0,3),(1,0)]
  | 54 => [(7,1),(8,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(5,1),(8,1)]
  | 58 => [(0,1),(6,5)]
  | 59 => [(0,4),(6,2)]
  | 60 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 61 => [(1,3),(7,3)]
  | 62 => [(4,2),(8,2)]
  | 63 => [(5,0),(5,3)]
  | 64 => [(4,5),(5,5),(8,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(5,5),(8,5)]
  | 68 => [(1,0),(3,0),(7,0)]
  | 69 => [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 70 => [(0,4),(1,2),(6,2)]
  | 71 => [(1,4),(3,4),(5,4),(7,4)]
  | 72 => [(0,0),(0,5),(6,3)]
  | 73 => [(4,4),(7,2)]
  | 74 => [(1,4),(7,4)]
  | 75 => [(0,5),(1,3),(6,3)]
  | 76 => [(4,4),(7,2),(8,2)]
  | 77 => [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 78 => [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 79 => [(0,2),(1,5),(6,0)]
  | 80 => [(1,1),(6,1),(7,1)]
  | 81 => [(4,1),(7,5),(8,1)]
  | 82 => [(0,2),(6,0),(6,5)]
  | 83 => [(0,4),(1,1),(7,1)]
  | 84 => [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 85 => [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 86 => [(2,0),(4,0),(8,0)]
  | 87 => [(7,3),(8,3)]
  | 88 => [(5,2),(5,5),(8,2)]
  | 89 => [(5,0),(7,0),(8,0)]
  | _ => [(4,3),(4,5),(7,3),(8,3)]
def root0Node48Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5),(6,5)]
  | 1 => some [(0,4),(1,1),(6,1)]
  | 2 => some [(5,1),(5,4),(8,1)]
  | 3 => some [(0,0),(0,1),(6,4),(6,5)]
  | 4 => some [(0,4),(1,2),(6,2),(7,2)]
  | 5 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 6 => some [(5,2),(5,5),(8,5)]
  | 7 => some [(7,0),(8,0)]
  | 8 => some [(4,3),(8,3)]
  | 9 => some [(1,5),(3,5),(5,5),(7,5)]
  | 10 => some [(0,3),(1,0),(3,0),(6,1)]
  | 11 => some [(2,1),(2,5),(4,1)]
  | 12 => some [(0,2),(1,0),(6,0),(7,0)]
  | 13 => some [(0,5),(6,2),(6,3)]
  | 14 => some [(4,4),(7,2),(8,4)]
  | 15 => some [(1,4),(7,4)]
  | 16 => some [(0,5),(6,3)]
  | 17 => some [(2,0),(2,2),(2,4),(4,4)]
  | 18 => some [(0,0),(1,3),(3,3),(7,3)]
  | 19 => some [(3,2),(5,2),(7,2)]
  | 20 => some [(4,0),(8,0)]
  | 21 => some [(0,2),(1,0),(6,0)]
  | 22 => some [(1,1),(7,1)]
  | 23 => some [(4,1),(7,5)]
  | 24 => some [(0,2),(6,0)]
  | 25 => some [(1,1),(3,1),(7,1)]
  | 26 => some [(0,1),(1,5),(6,5)]
  | 27 => some [(0,4),(6,1),(6,2)]
  | 28 => some [(5,1),(5,4),(8,4)]
  | 29 => some [(0,1),(1,4),(6,4)]
  | 30 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 31 => some [(4,0),(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(5,2),(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(1,0),(7,0)]
  | 37 => some [(4,3),(7,1),(8,3)]
  | 38 => some [(7,5),(8,5)]
  | 39 => some [(0,3),(1,0),(6,0)]
  | 40 => some [(0,3),(0,4),(6,1),(6,2)]
  | 41 => some [(5,1),(5,4),(8,4)]
  | 42 => some [(0,1),(6,4)]
  | 43 => some [(1,2),(6,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0),(7,4)]
  | 48 => some [(1,3),(7,3)]
  | 49 => some [(4,2),(8,2)]
  | 50 => some [(5,0),(5,3),(8,0)]
  | 51 => some [(4,3),(5,3),(7,1),(8,3)]
  | 52 => some [(7,5),(8,5)]
  | 53 => some [(0,3),(1,0)]
  | 54 => some [(7,1),(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1),(8,1)]
  | 58 => some [(0,1),(6,5)]
  | 59 => some [(0,4),(6,2)]
  | 60 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 61 => some [(1,3),(7,3)]
  | 62 => some [(4,2),(8,2)]
  | 63 => some [(5,0),(5,3)]
  | 64 => some [(4,5),(5,5),(8,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(5,5),(8,5)]
  | 68 => some [(1,0),(3,0),(7,0)]
  | 69 => some [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 70 => some [(0,4),(1,2),(6,2)]
  | 71 => some [(1,4),(3,4),(5,4),(7,4)]
  | 72 => some [(0,0),(0,5),(6,3)]
  | 73 => some [(4,4),(7,2)]
  | 74 => some [(1,4),(7,4)]
  | 75 => some [(0,5),(1,3),(6,3)]
  | 76 => some [(4,4),(7,2),(8,2)]
  | 77 => some [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 78 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 79 => some [(0,2),(1,5),(6,0)]
  | 80 => some [(1,1),(6,1),(7,1)]
  | 81 => some [(4,1),(7,5),(8,1)]
  | 82 => some [(0,2),(6,0),(6,5)]
  | 83 => some [(0,4),(1,1),(7,1)]
  | 84 => some [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 85 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 86 => some [(2,0),(4,0),(8,0)]
  | 87 => some [(7,3),(8,3)]
  | 88 => some [(5,2),(5,5),(8,2)]
  | 89 => some [(5,0),(7,0),(8,0)]
  | _ => some [(4,3),(4,5),(7,3),(8,3)]
theorem root0Node48Domains3_fast_eq : root0Node48Domains3 = expandDomains root0Node48Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node48Domains3 v = expandDomains root0Node48Domains3Fast v from by decide) v
theorem root0Node48Step3Chunk0_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_0⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk0_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_1⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk0_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_2⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk0_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_3⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk0_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_4⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk0_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_5⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk1_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_0⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk1_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_1⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk1_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_2⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk1_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_3⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk1_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_4⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk1_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_5⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk2_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_0⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk2_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_1⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk2_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_2⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk2_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_3⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk2_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_4⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk2_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_5⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk3_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_0⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk3_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_1⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk3_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_2⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk3_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_3⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk3_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_4⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk3_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_5⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk4_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_0⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk4_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_1⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk4_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_2⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk4_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_3⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk4_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_4⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk4_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_5⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk5_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_0⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk5_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_1⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk5_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_2⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk5_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_3⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk5_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_4⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk5_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_5⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk6_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_0⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk6_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_1⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk6_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_2⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk6_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_3⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk6_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_4⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk6_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_5⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk7_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_0⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk7_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_1⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk7_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_2⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk7_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_3⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk7_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_4⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk7_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_5⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk8_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_0⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk8_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_1⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk8_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_2⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk8_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_3⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk8_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_4⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Chunk8_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_5⟩
      root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq (by decide)
theorem root0Node48Step3Narrowing_checked :
    checkNarrowing table52 root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkNarrowing_flatten table52Scope [table52Rows0_0,table52Rows0_1,table52Rows0_2,table52Rows0_3,table52Rows0_4,table52Rows0_5,table52Rows1_0,table52Rows1_1,table52Rows1_2,table52Rows1_3,table52Rows1_4,table52Rows1_5,table52Rows2_0,table52Rows2_1,table52Rows2_2,table52Rows2_3,table52Rows2_4,table52Rows2_5,table52Rows3_0,table52Rows3_1,table52Rows3_2,table52Rows3_3,table52Rows3_4,table52Rows3_5,table52Rows4_0,table52Rows4_1,table52Rows4_2,table52Rows4_3,table52Rows4_4,table52Rows4_5,table52Rows5_0,table52Rows5_1,table52Rows5_2,table52Rows5_3,table52Rows5_4,table52Rows5_5,table52Rows6_0,table52Rows6_1,table52Rows6_2,table52Rows6_3,table52Rows6_4,table52Rows6_5,table52Rows7_0,table52Rows7_1,table52Rows7_2,table52Rows7_3,table52Rows7_4,table52Rows7_5,table52Rows8_0,table52Rows8_1,table52Rows8_2,table52Rows8_3,table52Rows8_4,table52Rows8_5]
    root0Node48Domains2 root0Node48Domains3 (by
      simp only [List.all_cons, List.all_nil, root0Node48Step3Chunk0_0_checked, root0Node48Step3Chunk0_1_checked, root0Node48Step3Chunk0_2_checked, root0Node48Step3Chunk0_3_checked, root0Node48Step3Chunk0_4_checked, root0Node48Step3Chunk0_5_checked, root0Node48Step3Chunk1_0_checked, root0Node48Step3Chunk1_1_checked, root0Node48Step3Chunk1_2_checked, root0Node48Step3Chunk1_3_checked, root0Node48Step3Chunk1_4_checked, root0Node48Step3Chunk1_5_checked, root0Node48Step3Chunk2_0_checked, root0Node48Step3Chunk2_1_checked, root0Node48Step3Chunk2_2_checked, root0Node48Step3Chunk2_3_checked, root0Node48Step3Chunk2_4_checked, root0Node48Step3Chunk2_5_checked, root0Node48Step3Chunk3_0_checked, root0Node48Step3Chunk3_1_checked, root0Node48Step3Chunk3_2_checked, root0Node48Step3Chunk3_3_checked, root0Node48Step3Chunk3_4_checked, root0Node48Step3Chunk3_5_checked, root0Node48Step3Chunk4_0_checked, root0Node48Step3Chunk4_1_checked, root0Node48Step3Chunk4_2_checked, root0Node48Step3Chunk4_3_checked, root0Node48Step3Chunk4_4_checked, root0Node48Step3Chunk4_5_checked, root0Node48Step3Chunk5_0_checked, root0Node48Step3Chunk5_1_checked, root0Node48Step3Chunk5_2_checked, root0Node48Step3Chunk5_3_checked, root0Node48Step3Chunk5_4_checked, root0Node48Step3Chunk5_5_checked, root0Node48Step3Chunk6_0_checked, root0Node48Step3Chunk6_1_checked, root0Node48Step3Chunk6_2_checked, root0Node48Step3Chunk6_3_checked, root0Node48Step3Chunk6_4_checked, root0Node48Step3Chunk6_5_checked, root0Node48Step3Chunk7_0_checked, root0Node48Step3Chunk7_1_checked, root0Node48Step3Chunk7_2_checked, root0Node48Step3Chunk7_3_checked, root0Node48Step3Chunk7_4_checked, root0Node48Step3Chunk7_5_checked, root0Node48Step3Chunk8_0_checked, root0Node48Step3Chunk8_1_checked, root0Node48Step3Chunk8_2_checked, root0Node48Step3Chunk8_3_checked, root0Node48Step3Chunk8_4_checked, root0Node48Step3Chunk8_5_checked, Bool.true_and])
theorem root0Node48Step3_checked :
    checkReplacement table52 root0Node48Domains2 root0Node48Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root0Node48Domains2 root0Node48Domains3
    root0Node48Domains2Fast root0Node48Domains3Fast
    root0Node48Domains2_fast_eq root0Node48Domains3_fast_eq
    root0Node48Step3Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
