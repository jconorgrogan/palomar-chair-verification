module

public import SpectreFinite.RadiusFiveRoot0Part38
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable51
public import SpectreFinite.RadiusFiveTable52
public import SpectreFinite.RadiusFiveTable56
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node91Domains0 : Domains 91 State := restrict root0Node89Domains2 84 (8,1)
def root0Node91Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(3,5)]
  | 10 => some [(0,3)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5)]
  | 14 => some [(4,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(2,4)]
  | 18 => some [(1,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(6,5)]
  | 27 => some [(0,4)]
  | 28 => some [(5,4)]
  | 29 => some [(1,4)]
  | 30 => some [(7,2)]
  | 31 => some [(4,0)]
  | 32 => some [(7,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(4,3)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(6,1)]
  | 41 => some [(5,1)]
  | 42 => some [(0,1)]
  | 43 => some [(6,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(1,3)]
  | 49 => some [(8,2)]
  | 50 => some [(8,0)]
  | 51 => some [(8,3)]
  | 52 => some [(8,5)]
  | 53 => some [(1,0)]
  | 54 => some [(7,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(8,1)]
  | 58 => some [(6,5)]
  | 59 => some [(0,4)]
  | 60 => some [(5,4)]
  | 61 => some [(1,3)]
  | 62 => some [(8,2)]
  | 63 => some [(5,0)]
  | 64 => some [(4,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(7,0)]
  | 69 => some [(4,3)]
  | 70 => some [(0,4)]
  | 71 => some [(5,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(6,3)]
  | 76 => some [(7,2)]
  | 77 => some [(7,4)]
  | 78 => some [(4,3)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(4,1)]
  | 82 => some [(0,2)]
  | 83 => some [(1,1)]
  | 84 => some [(8,1)]
  | 85 => some [(0,5)]
  | 86 => some [(2,0)]
  | 87 => some [(7,3)]
  | 88 => some [(5,2)]
  | 89 => some [(8,0)]
  | _ => some [(7,3),(8,3)]
theorem root0Node91Domains0_fast_eq : root0Node91Domains0 = expandDomains root0Node91Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node91Domains0 v = expandDomains root0Node91Domains0Fast v from by decide) v
def root0Node91Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(5,5)]
  | 7 => [(7,0)]
  | 8 => [(4,3)]
  | 9 => [(3,5)]
  | 10 => [(0,3)]
  | 11 => [(4,1)]
  | 12 => [(0,2)]
  | 13 => [(0,5)]
  | 14 => [(4,4)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(2,4)]
  | 18 => [(1,3)]
  | 19 => [(5,2)]
  | 20 => [(8,0)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(7,1)]
  | 26 => [(6,5)]
  | 27 => [(0,4)]
  | 28 => [(5,4)]
  | 29 => [(1,4)]
  | 30 => [(7,2)]
  | 31 => [(4,0)]
  | 32 => [(7,3)]
  | 33 => [(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(7,0)]
  | 37 => [(4,3)]
  | 38 => [(7,5)]
  | 39 => [(6,0)]
  | 40 => [(6,1)]
  | 41 => [(5,1)]
  | 42 => [(0,1)]
  | 43 => [(6,2)]
  | 44 => [(8,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(7,4)]
  | 48 => [(1,3)]
  | 49 => [(8,2)]
  | 50 => [(8,0)]
  | 51 => [(8,3)]
  | 52 => [(8,5)]
  | 53 => [(1,0)]
  | 54 => [(7,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(8,1)]
  | 58 => [(6,5)]
  | 59 => [(0,4)]
  | 60 => [(5,4)]
  | 61 => [(1,3)]
  | 62 => [(8,2)]
  | 63 => [(5,0)]
  | 64 => [(4,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(8,5)]
  | 68 => [(7,0)]
  | 69 => [(4,3)]
  | 70 => [(0,4)]
  | 71 => [(5,4)]
  | 72 => [(0,0)]
  | 73 => [(7,2)]
  | 74 => [(7,4)]
  | 75 => [(6,3)]
  | 76 => [(7,2)]
  | 77 => [(7,4)]
  | 78 => [(4,3)]
  | 79 => [(1,5)]
  | 80 => [(6,1)]
  | 81 => [(4,1)]
  | 82 => [(0,2)]
  | 83 => [(1,1)]
  | 84 => [(8,1)]
  | 85 => [(0,5)]
  | 86 => [(2,0)]
  | 87 => [(7,3)]
  | 88 => [(5,2)]
  | 89 => [(8,0)]
  | _ => [(8,3)]
def root0Node91Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(3,5)]
  | 10 => some [(0,3)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5)]
  | 14 => some [(4,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(2,4)]
  | 18 => some [(1,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(6,5)]
  | 27 => some [(0,4)]
  | 28 => some [(5,4)]
  | 29 => some [(1,4)]
  | 30 => some [(7,2)]
  | 31 => some [(4,0)]
  | 32 => some [(7,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(4,3)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(6,1)]
  | 41 => some [(5,1)]
  | 42 => some [(0,1)]
  | 43 => some [(6,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(1,3)]
  | 49 => some [(8,2)]
  | 50 => some [(8,0)]
  | 51 => some [(8,3)]
  | 52 => some [(8,5)]
  | 53 => some [(1,0)]
  | 54 => some [(7,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(8,1)]
  | 58 => some [(6,5)]
  | 59 => some [(0,4)]
  | 60 => some [(5,4)]
  | 61 => some [(1,3)]
  | 62 => some [(8,2)]
  | 63 => some [(5,0)]
  | 64 => some [(4,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(7,0)]
  | 69 => some [(4,3)]
  | 70 => some [(0,4)]
  | 71 => some [(5,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(6,3)]
  | 76 => some [(7,2)]
  | 77 => some [(7,4)]
  | 78 => some [(4,3)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(4,1)]
  | 82 => some [(0,2)]
  | 83 => some [(1,1)]
  | 84 => some [(8,1)]
  | 85 => some [(0,5)]
  | 86 => some [(2,0)]
  | 87 => some [(7,3)]
  | 88 => some [(5,2)]
  | 89 => some [(8,0)]
  | _ => some [(8,3)]
theorem root0Node91Domains1_fast_eq : root0Node91Domains1 = expandDomains root0Node91Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node91Domains1 v = expandDomains root0Node91Domains1Fast v from by decide) v
theorem root0Node91Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq (by decide)
theorem root0Node91Step1Narrowing_checked :
    checkNarrowing table56 root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root0Node91Domains0 root0Node91Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node91Step1Chunk0_0_checked, root0Node91Step1Chunk0_1_checked, root0Node91Step1Chunk0_2_checked, root0Node91Step1Chunk0_3_checked, root0Node91Step1Chunk0_4_checked, root0Node91Step1Chunk0_5_checked, root0Node91Step1Chunk1_0_checked, root0Node91Step1Chunk1_1_checked, root0Node91Step1Chunk1_2_checked, root0Node91Step1Chunk1_3_checked, root0Node91Step1Chunk1_4_checked, root0Node91Step1Chunk1_5_checked, root0Node91Step1Chunk2_0_checked, root0Node91Step1Chunk2_1_checked, root0Node91Step1Chunk2_2_checked, root0Node91Step1Chunk2_3_checked, root0Node91Step1Chunk2_4_checked, root0Node91Step1Chunk2_5_checked, root0Node91Step1Chunk3_0_checked, root0Node91Step1Chunk3_1_checked, root0Node91Step1Chunk3_2_checked, root0Node91Step1Chunk3_3_checked, root0Node91Step1Chunk3_4_checked, root0Node91Step1Chunk3_5_checked, root0Node91Step1Chunk4_0_checked, root0Node91Step1Chunk4_1_checked, root0Node91Step1Chunk4_2_checked, root0Node91Step1Chunk4_3_checked, root0Node91Step1Chunk4_4_checked, root0Node91Step1Chunk4_5_checked, root0Node91Step1Chunk5_0_checked, root0Node91Step1Chunk5_1_checked, root0Node91Step1Chunk5_2_checked, root0Node91Step1Chunk5_3_checked, root0Node91Step1Chunk5_4_checked, root0Node91Step1Chunk5_5_checked, root0Node91Step1Chunk6_0_checked, root0Node91Step1Chunk6_1_checked, root0Node91Step1Chunk6_2_checked, root0Node91Step1Chunk6_3_checked, root0Node91Step1Chunk6_4_checked, root0Node91Step1Chunk6_5_checked, root0Node91Step1Chunk7_0_checked, root0Node91Step1Chunk7_1_checked, root0Node91Step1Chunk7_2_checked, root0Node91Step1Chunk7_3_checked, root0Node91Step1Chunk7_4_checked, root0Node91Step1Chunk7_5_checked, root0Node91Step1Chunk8_0_checked, root0Node91Step1Chunk8_1_checked, root0Node91Step1Chunk8_2_checked, root0Node91Step1Chunk8_3_checked, root0Node91Step1Chunk8_4_checked, root0Node91Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node91Step1_checked :
    checkReplacement table56 root0Node91Domains0 root0Node91Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node91Domains0 root0Node91Domains1
    root0Node91Domains0Fast root0Node91Domains1Fast
    root0Node91Domains0_fast_eq root0Node91Domains1_fast_eq
    root0Node91Step1Narrowing_checked (by decide)
theorem root0Node91Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node91Domains1 (.output 44) = true := by decide
def root0Node92Domains0 : Domains 91 State := restrict root0Node88Domains1 30 (8,2)
def root0Node92Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(3,5)]
  | 10 => some [(0,3)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5)]
  | 14 => some [(4,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(2,4)]
  | 18 => some [(1,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(6,5)]
  | 27 => some [(0,4)]
  | 28 => some [(5,4)]
  | 29 => some [(1,4)]
  | 30 => some [(8,2)]
  | 31 => some [(4,0),(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(4,3)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(0,4),(6,1),(6,2)]
  | 41 => some [(5,1),(5,4),(8,4)]
  | 42 => some [(0,1),(6,4)]
  | 43 => some [(1,2),(6,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(1,3)]
  | 49 => some [(8,2)]
  | 50 => some [(5,0),(8,0)]
  | 51 => some [(4,3),(7,1),(8,3)]
  | 52 => some [(7,5),(8,5)]
  | 53 => some [(0,3),(1,0)]
  | 54 => some [(7,1),(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(8,1)]
  | 58 => some [(6,5)]
  | 59 => some [(0,4)]
  | 60 => some [(5,4)]
  | 61 => some [(1,3),(7,3)]
  | 62 => some [(4,2),(8,2)]
  | 63 => some [(5,0),(5,3)]
  | 64 => some [(4,5),(5,5),(8,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(5,5),(8,5)]
  | 68 => some [(7,0)]
  | 69 => some [(4,3)]
  | 70 => some [(0,4),(6,2)]
  | 71 => some [(1,4),(3,4),(5,4),(7,4)]
  | 72 => some [(0,0),(0,5),(6,3)]
  | 73 => some [(4,4),(7,2)]
  | 74 => some [(1,4),(7,4)]
  | 75 => some [(0,5),(6,3)]
  | 76 => some [(4,4),(7,2)]
  | 77 => some [(1,4),(7,4)]
  | 78 => some [(2,1),(2,3),(2,5),(4,3)]
  | 79 => some [(0,2),(1,5),(6,0)]
  | 80 => some [(1,1),(6,1),(7,1)]
  | 81 => some [(4,1),(7,5)]
  | 82 => some [(0,2),(6,0)]
  | 83 => some [(1,1),(7,1)]
  | 84 => some [(4,1),(7,5),(8,1)]
  | 85 => some [(0,5),(1,2),(3,2),(7,2)]
  | 86 => some [(2,0),(4,0)]
  | 87 => some [(7,3)]
  | 88 => some [(5,2),(8,2)]
  | 89 => some [(8,0)]
  | _ => some [(7,3),(8,3)]
theorem root0Node92Domains0_fast_eq : root0Node92Domains0 = expandDomains root0Node92Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node92Domains0 v = expandDomains root0Node92Domains0Fast v from by decide) v
def root0Node92Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(5,5)]
  | 7 => [(7,0)]
  | 8 => [(4,3)]
  | 9 => [(3,5)]
  | 10 => [(0,3)]
  | 11 => [(4,1)]
  | 12 => [(0,2)]
  | 13 => [(0,5)]
  | 14 => [(4,4)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(2,4)]
  | 18 => [(1,3)]
  | 19 => [(5,2)]
  | 20 => [(8,0)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(7,1)]
  | 26 => [(6,5)]
  | 27 => [(0,4)]
  | 28 => [(5,4)]
  | 29 => [(1,4)]
  | 30 => [(8,2)]
  | 31 => [(8,0)]
  | 32 => [(7,3)]
  | 33 => [(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(7,0)]
  | 37 => [(4,3)]
  | 38 => [(7,5)]
  | 39 => [(6,0)]
  | 40 => [(0,4),(6,2)]
  | 41 => [(5,4),(8,4)]
  | 42 => [(6,4)]
  | 43 => [(1,2)]
  | 44 => [(8,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(7,4)]
  | 48 => [(1,3)]
  | 49 => [(8,2)]
  | 50 => [(5,0),(8,0)]
  | 51 => [(4,3),(7,1)]
  | 52 => [(7,5)]
  | 53 => [(0,3)]
  | 54 => [(8,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(8,1)]
  | 58 => [(6,5)]
  | 59 => [(0,4)]
  | 60 => [(5,4)]
  | 61 => [(1,3),(7,3)]
  | 62 => [(4,2)]
  | 63 => [(5,3)]
  | 64 => [(5,5),(8,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(5,5),(8,5)]
  | 68 => [(7,0)]
  | 69 => [(4,3)]
  | 70 => [(0,4),(6,2)]
  | 71 => [(1,4),(3,4),(7,4)]
  | 72 => [(0,5),(6,3)]
  | 73 => [(4,4),(7,2)]
  | 74 => [(1,4),(7,4)]
  | 75 => [(0,5),(6,3)]
  | 76 => [(4,4),(7,2)]
  | 77 => [(1,4),(7,4)]
  | 78 => [(2,1),(2,3),(2,5)]
  | 79 => [(0,2),(6,0)]
  | 80 => [(1,1),(7,1)]
  | 81 => [(4,1),(7,5)]
  | 82 => [(0,2),(6,0)]
  | 83 => [(1,1),(7,1)]
  | 84 => [(4,1),(7,5),(8,1)]
  | 85 => [(1,2),(3,2),(7,2)]
  | 86 => [(4,0)]
  | 87 => [(7,3)]
  | 88 => [(5,2),(8,2)]
  | 89 => [(8,0)]
  | _ => [(7,3),(8,3)]
def root0Node92Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(3,5)]
  | 10 => some [(0,3)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5)]
  | 14 => some [(4,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(2,4)]
  | 18 => some [(1,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(6,5)]
  | 27 => some [(0,4)]
  | 28 => some [(5,4)]
  | 29 => some [(1,4)]
  | 30 => some [(8,2)]
  | 31 => some [(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(4,3)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(0,4),(6,2)]
  | 41 => some [(5,4),(8,4)]
  | 42 => some [(6,4)]
  | 43 => some [(1,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(1,3)]
  | 49 => some [(8,2)]
  | 50 => some [(5,0),(8,0)]
  | 51 => some [(4,3),(7,1)]
  | 52 => some [(7,5)]
  | 53 => some [(0,3)]
  | 54 => some [(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(8,1)]
  | 58 => some [(6,5)]
  | 59 => some [(0,4)]
  | 60 => some [(5,4)]
  | 61 => some [(1,3),(7,3)]
  | 62 => some [(4,2)]
  | 63 => some [(5,3)]
  | 64 => some [(5,5),(8,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(5,5),(8,5)]
  | 68 => some [(7,0)]
  | 69 => some [(4,3)]
  | 70 => some [(0,4),(6,2)]
  | 71 => some [(1,4),(3,4),(7,4)]
  | 72 => some [(0,5),(6,3)]
  | 73 => some [(4,4),(7,2)]
  | 74 => some [(1,4),(7,4)]
  | 75 => some [(0,5),(6,3)]
  | 76 => some [(4,4),(7,2)]
  | 77 => some [(1,4),(7,4)]
  | 78 => some [(2,1),(2,3),(2,5)]
  | 79 => some [(0,2),(6,0)]
  | 80 => some [(1,1),(7,1)]
  | 81 => some [(4,1),(7,5)]
  | 82 => some [(0,2),(6,0)]
  | 83 => some [(1,1),(7,1)]
  | 84 => some [(4,1),(7,5),(8,1)]
  | 85 => some [(1,2),(3,2),(7,2)]
  | 86 => some [(4,0)]
  | 87 => some [(7,3)]
  | 88 => some [(5,2),(8,2)]
  | 89 => some [(8,0)]
  | _ => some [(7,3),(8,3)]
theorem root0Node92Domains1_fast_eq : root0Node92Domains1 = expandDomains root0Node92Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node92Domains1 v = expandDomains root0Node92Domains1Fast v from by decide) v
theorem root0Node92Step1Chunk0_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_0⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk0_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_1⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk0_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_2⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk0_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_3⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk0_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_4⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk0_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_5⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk1_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_0⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk1_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_1⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk1_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_2⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk1_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_3⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk1_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_4⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk1_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_5⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk2_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_0⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk2_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_1⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk2_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_2⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk2_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_3⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk2_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_4⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk2_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_5⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk3_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_0⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk3_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_1⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk3_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_2⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk3_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_3⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk3_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_4⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk3_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_5⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk4_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_0⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk4_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_1⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk4_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_2⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk4_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_3⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk4_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_4⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk4_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_5⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk5_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_0⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk5_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_1⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk5_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_2⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk5_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_3⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk5_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_4⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk5_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_5⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk6_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_0⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk6_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_1⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk6_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_2⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk6_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_3⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk6_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_4⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk6_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_5⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk7_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_0⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk7_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_1⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk7_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_2⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk7_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_3⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk7_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_4⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk7_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_5⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk8_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_0⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk8_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_1⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk8_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_2⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk8_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_3⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk8_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_4⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Chunk8_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_5⟩
      root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq (by decide)
theorem root0Node92Step1Narrowing_checked :
    checkNarrowing table52 root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkNarrowing_flatten table52Scope [table52Rows0_0,table52Rows0_1,table52Rows0_2,table52Rows0_3,table52Rows0_4,table52Rows0_5,table52Rows1_0,table52Rows1_1,table52Rows1_2,table52Rows1_3,table52Rows1_4,table52Rows1_5,table52Rows2_0,table52Rows2_1,table52Rows2_2,table52Rows2_3,table52Rows2_4,table52Rows2_5,table52Rows3_0,table52Rows3_1,table52Rows3_2,table52Rows3_3,table52Rows3_4,table52Rows3_5,table52Rows4_0,table52Rows4_1,table52Rows4_2,table52Rows4_3,table52Rows4_4,table52Rows4_5,table52Rows5_0,table52Rows5_1,table52Rows5_2,table52Rows5_3,table52Rows5_4,table52Rows5_5,table52Rows6_0,table52Rows6_1,table52Rows6_2,table52Rows6_3,table52Rows6_4,table52Rows6_5,table52Rows7_0,table52Rows7_1,table52Rows7_2,table52Rows7_3,table52Rows7_4,table52Rows7_5,table52Rows8_0,table52Rows8_1,table52Rows8_2,table52Rows8_3,table52Rows8_4,table52Rows8_5]
    root0Node92Domains0 root0Node92Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node92Step1Chunk0_0_checked, root0Node92Step1Chunk0_1_checked, root0Node92Step1Chunk0_2_checked, root0Node92Step1Chunk0_3_checked, root0Node92Step1Chunk0_4_checked, root0Node92Step1Chunk0_5_checked, root0Node92Step1Chunk1_0_checked, root0Node92Step1Chunk1_1_checked, root0Node92Step1Chunk1_2_checked, root0Node92Step1Chunk1_3_checked, root0Node92Step1Chunk1_4_checked, root0Node92Step1Chunk1_5_checked, root0Node92Step1Chunk2_0_checked, root0Node92Step1Chunk2_1_checked, root0Node92Step1Chunk2_2_checked, root0Node92Step1Chunk2_3_checked, root0Node92Step1Chunk2_4_checked, root0Node92Step1Chunk2_5_checked, root0Node92Step1Chunk3_0_checked, root0Node92Step1Chunk3_1_checked, root0Node92Step1Chunk3_2_checked, root0Node92Step1Chunk3_3_checked, root0Node92Step1Chunk3_4_checked, root0Node92Step1Chunk3_5_checked, root0Node92Step1Chunk4_0_checked, root0Node92Step1Chunk4_1_checked, root0Node92Step1Chunk4_2_checked, root0Node92Step1Chunk4_3_checked, root0Node92Step1Chunk4_4_checked, root0Node92Step1Chunk4_5_checked, root0Node92Step1Chunk5_0_checked, root0Node92Step1Chunk5_1_checked, root0Node92Step1Chunk5_2_checked, root0Node92Step1Chunk5_3_checked, root0Node92Step1Chunk5_4_checked, root0Node92Step1Chunk5_5_checked, root0Node92Step1Chunk6_0_checked, root0Node92Step1Chunk6_1_checked, root0Node92Step1Chunk6_2_checked, root0Node92Step1Chunk6_3_checked, root0Node92Step1Chunk6_4_checked, root0Node92Step1Chunk6_5_checked, root0Node92Step1Chunk7_0_checked, root0Node92Step1Chunk7_1_checked, root0Node92Step1Chunk7_2_checked, root0Node92Step1Chunk7_3_checked, root0Node92Step1Chunk7_4_checked, root0Node92Step1Chunk7_5_checked, root0Node92Step1Chunk8_0_checked, root0Node92Step1Chunk8_1_checked, root0Node92Step1Chunk8_2_checked, root0Node92Step1Chunk8_3_checked, root0Node92Step1Chunk8_4_checked, root0Node92Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node92Step1_checked :
    checkReplacement table52 root0Node92Domains0 root0Node92Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node92Domains0 root0Node92Domains1
    root0Node92Domains0Fast root0Node92Domains1Fast
    root0Node92Domains0_fast_eq root0Node92Domains1_fast_eq
    root0Node92Step1Narrowing_checked (by decide)
def root0Node93Domains0 : Domains 91 State := restrict root0Node92Domains1 40 (0,4)
def root0Node93Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(3,5)]
  | 10 => some [(0,3)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5)]
  | 14 => some [(4,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(2,4)]
  | 18 => some [(1,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(6,5)]
  | 27 => some [(0,4)]
  | 28 => some [(5,4)]
  | 29 => some [(1,4)]
  | 30 => some [(8,2)]
  | 31 => some [(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(4,3)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(0,4)]
  | 41 => some [(5,4),(8,4)]
  | 42 => some [(6,4)]
  | 43 => some [(1,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(1,3)]
  | 49 => some [(8,2)]
  | 50 => some [(5,0),(8,0)]
  | 51 => some [(4,3),(7,1)]
  | 52 => some [(7,5)]
  | 53 => some [(0,3)]
  | 54 => some [(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(8,1)]
  | 58 => some [(6,5)]
  | 59 => some [(0,4)]
  | 60 => some [(5,4)]
  | 61 => some [(1,3),(7,3)]
  | 62 => some [(4,2)]
  | 63 => some [(5,3)]
  | 64 => some [(5,5),(8,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(5,5),(8,5)]
  | 68 => some [(7,0)]
  | 69 => some [(4,3)]
  | 70 => some [(0,4),(6,2)]
  | 71 => some [(1,4),(3,4),(7,4)]
  | 72 => some [(0,5),(6,3)]
  | 73 => some [(4,4),(7,2)]
  | 74 => some [(1,4),(7,4)]
  | 75 => some [(0,5),(6,3)]
  | 76 => some [(4,4),(7,2)]
  | 77 => some [(1,4),(7,4)]
  | 78 => some [(2,1),(2,3),(2,5)]
  | 79 => some [(0,2),(6,0)]
  | 80 => some [(1,1),(7,1)]
  | 81 => some [(4,1),(7,5)]
  | 82 => some [(0,2),(6,0)]
  | 83 => some [(1,1),(7,1)]
  | 84 => some [(4,1),(7,5),(8,1)]
  | 85 => some [(1,2),(3,2),(7,2)]
  | 86 => some [(4,0)]
  | 87 => some [(7,3)]
  | 88 => some [(5,2),(8,2)]
  | 89 => some [(8,0)]
  | _ => some [(7,3),(8,3)]
theorem root0Node93Domains0_fast_eq : root0Node93Domains0 = expandDomains root0Node93Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node93Domains0 v = expandDomains root0Node93Domains0Fast v from by decide) v
def root0Node93Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(5,5)]
  | 7 => [(7,0)]
  | 8 => [(4,3)]
  | 9 => [(3,5)]
  | 10 => [(0,3)]
  | 11 => [(4,1)]
  | 12 => [(0,2)]
  | 13 => [(0,5)]
  | 14 => [(4,4)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(2,4)]
  | 18 => [(1,3)]
  | 19 => [(5,2)]
  | 20 => [(8,0)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(7,1)]
  | 26 => [(6,5)]
  | 27 => [(0,4)]
  | 28 => [(5,4)]
  | 29 => [(1,4)]
  | 30 => [(8,2)]
  | 31 => [(8,0)]
  | 32 => [(7,3)]
  | 33 => [(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(7,0)]
  | 37 => [(4,3)]
  | 38 => [(7,5)]
  | 39 => [(6,0)]
  | 40 => [(0,4)]
  | 41 => [(5,4)]
  | 42 => [(6,4)]
  | 43 => [(1,2)]
  | 44 => [(8,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(7,4)]
  | 48 => [(1,3)]
  | 49 => [(8,2)]
  | 50 => [(5,0),(8,0)]
  | 51 => [(4,3)]
  | 52 => [(7,5)]
  | 53 => [(0,3)]
  | 54 => [(8,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(8,1)]
  | 58 => [(6,5)]
  | 59 => [(0,4)]
  | 60 => [(5,4)]
  | 61 => [(1,3)]
  | 62 => [(4,2)]
  | 63 => [(5,3)]
  | 64 => [(5,5),(8,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(5,5),(8,5)]
  | 68 => [(7,0)]
  | 69 => [(4,3)]
  | 70 => [(0,4)]
  | 71 => [(1,4),(3,4)]
  | 72 => [(0,5),(6,3)]
  | 73 => [(4,4),(7,2)]
  | 74 => [(1,4),(7,4)]
  | 75 => [(0,5),(6,3)]
  | 76 => [(4,4),(7,2)]
  | 77 => [(1,4),(7,4)]
  | 78 => [(2,3),(2,5)]
  | 79 => [(0,2),(6,0)]
  | 80 => [(1,1),(7,1)]
  | 81 => [(4,1),(7,5)]
  | 82 => [(0,2),(6,0)]
  | 83 => [(1,1),(7,1)]
  | 84 => [(4,1),(7,5),(8,1)]
  | 85 => [(1,2),(7,2)]
  | 86 => [(4,0)]
  | 87 => [(7,3)]
  | 88 => [(5,2),(8,2)]
  | 89 => [(8,0)]
  | _ => [(7,3),(8,3)]
def root0Node93Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(3,5)]
  | 10 => some [(0,3)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5)]
  | 14 => some [(4,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(2,4)]
  | 18 => some [(1,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(6,5)]
  | 27 => some [(0,4)]
  | 28 => some [(5,4)]
  | 29 => some [(1,4)]
  | 30 => some [(8,2)]
  | 31 => some [(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(4,3)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(0,4)]
  | 41 => some [(5,4)]
  | 42 => some [(6,4)]
  | 43 => some [(1,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(1,3)]
  | 49 => some [(8,2)]
  | 50 => some [(5,0),(8,0)]
  | 51 => some [(4,3)]
  | 52 => some [(7,5)]
  | 53 => some [(0,3)]
  | 54 => some [(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(8,1)]
  | 58 => some [(6,5)]
  | 59 => some [(0,4)]
  | 60 => some [(5,4)]
  | 61 => some [(1,3)]
  | 62 => some [(4,2)]
  | 63 => some [(5,3)]
  | 64 => some [(5,5),(8,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(5,5),(8,5)]
  | 68 => some [(7,0)]
  | 69 => some [(4,3)]
  | 70 => some [(0,4)]
  | 71 => some [(1,4),(3,4)]
  | 72 => some [(0,5),(6,3)]
  | 73 => some [(4,4),(7,2)]
  | 74 => some [(1,4),(7,4)]
  | 75 => some [(0,5),(6,3)]
  | 76 => some [(4,4),(7,2)]
  | 77 => some [(1,4),(7,4)]
  | 78 => some [(2,3),(2,5)]
  | 79 => some [(0,2),(6,0)]
  | 80 => some [(1,1),(7,1)]
  | 81 => some [(4,1),(7,5)]
  | 82 => some [(0,2),(6,0)]
  | 83 => some [(1,1),(7,1)]
  | 84 => some [(4,1),(7,5),(8,1)]
  | 85 => some [(1,2),(7,2)]
  | 86 => some [(4,0)]
  | 87 => some [(7,3)]
  | 88 => some [(5,2),(8,2)]
  | 89 => some [(8,0)]
  | _ => some [(7,3),(8,3)]
theorem root0Node93Domains1_fast_eq : root0Node93Domains1 = expandDomains root0Node93Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node93Domains1 v = expandDomains root0Node93Domains1Fast v from by decide) v
theorem root0Node93Step1Chunk0_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_0⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk0_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_1⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk0_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_2⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk0_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_3⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk0_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_4⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk0_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_5⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk1_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_0⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk1_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_1⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk1_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_2⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk1_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_3⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk1_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_4⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk1_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_5⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk2_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_0⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk2_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_1⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk2_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_2⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk2_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_3⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk2_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_4⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk2_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_5⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk3_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_0⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk3_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_1⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk3_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_2⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk3_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_3⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk3_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_4⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk3_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_5⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk4_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_0⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk4_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_1⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk4_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_2⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk4_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_3⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk4_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_4⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk4_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_5⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk5_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_0⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk5_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_1⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk5_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_2⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk5_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_3⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk5_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_4⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk5_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_5⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk6_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_0⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk6_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_1⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk6_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_2⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk6_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_3⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk6_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_4⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk6_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_5⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk7_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_0⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk7_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_1⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk7_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_2⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk7_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_3⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk7_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_4⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk7_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_5⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk8_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_0⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk8_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_1⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk8_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_2⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk8_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_3⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk8_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_4⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Chunk8_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_5⟩
      root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq (by decide)
theorem root0Node93Step1Narrowing_checked :
    checkNarrowing table51 root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkNarrowing_flatten table51Scope [table51Rows0_0,table51Rows0_1,table51Rows0_2,table51Rows0_3,table51Rows0_4,table51Rows0_5,table51Rows1_0,table51Rows1_1,table51Rows1_2,table51Rows1_3,table51Rows1_4,table51Rows1_5,table51Rows2_0,table51Rows2_1,table51Rows2_2,table51Rows2_3,table51Rows2_4,table51Rows2_5,table51Rows3_0,table51Rows3_1,table51Rows3_2,table51Rows3_3,table51Rows3_4,table51Rows3_5,table51Rows4_0,table51Rows4_1,table51Rows4_2,table51Rows4_3,table51Rows4_4,table51Rows4_5,table51Rows5_0,table51Rows5_1,table51Rows5_2,table51Rows5_3,table51Rows5_4,table51Rows5_5,table51Rows6_0,table51Rows6_1,table51Rows6_2,table51Rows6_3,table51Rows6_4,table51Rows6_5,table51Rows7_0,table51Rows7_1,table51Rows7_2,table51Rows7_3,table51Rows7_4,table51Rows7_5,table51Rows8_0,table51Rows8_1,table51Rows8_2,table51Rows8_3,table51Rows8_4,table51Rows8_5]
    root0Node93Domains0 root0Node93Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node93Step1Chunk0_0_checked, root0Node93Step1Chunk0_1_checked, root0Node93Step1Chunk0_2_checked, root0Node93Step1Chunk0_3_checked, root0Node93Step1Chunk0_4_checked, root0Node93Step1Chunk0_5_checked, root0Node93Step1Chunk1_0_checked, root0Node93Step1Chunk1_1_checked, root0Node93Step1Chunk1_2_checked, root0Node93Step1Chunk1_3_checked, root0Node93Step1Chunk1_4_checked, root0Node93Step1Chunk1_5_checked, root0Node93Step1Chunk2_0_checked, root0Node93Step1Chunk2_1_checked, root0Node93Step1Chunk2_2_checked, root0Node93Step1Chunk2_3_checked, root0Node93Step1Chunk2_4_checked, root0Node93Step1Chunk2_5_checked, root0Node93Step1Chunk3_0_checked, root0Node93Step1Chunk3_1_checked, root0Node93Step1Chunk3_2_checked, root0Node93Step1Chunk3_3_checked, root0Node93Step1Chunk3_4_checked, root0Node93Step1Chunk3_5_checked, root0Node93Step1Chunk4_0_checked, root0Node93Step1Chunk4_1_checked, root0Node93Step1Chunk4_2_checked, root0Node93Step1Chunk4_3_checked, root0Node93Step1Chunk4_4_checked, root0Node93Step1Chunk4_5_checked, root0Node93Step1Chunk5_0_checked, root0Node93Step1Chunk5_1_checked, root0Node93Step1Chunk5_2_checked, root0Node93Step1Chunk5_3_checked, root0Node93Step1Chunk5_4_checked, root0Node93Step1Chunk5_5_checked, root0Node93Step1Chunk6_0_checked, root0Node93Step1Chunk6_1_checked, root0Node93Step1Chunk6_2_checked, root0Node93Step1Chunk6_3_checked, root0Node93Step1Chunk6_4_checked, root0Node93Step1Chunk6_5_checked, root0Node93Step1Chunk7_0_checked, root0Node93Step1Chunk7_1_checked, root0Node93Step1Chunk7_2_checked, root0Node93Step1Chunk7_3_checked, root0Node93Step1Chunk7_4_checked, root0Node93Step1Chunk7_5_checked, root0Node93Step1Chunk8_0_checked, root0Node93Step1Chunk8_1_checked, root0Node93Step1Chunk8_2_checked, root0Node93Step1Chunk8_3_checked, root0Node93Step1Chunk8_4_checked, root0Node93Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node93Step1_checked :
    checkReplacement table51 root0Node93Domains0 root0Node93Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node93Domains0 root0Node93Domains1
    root0Node93Domains0Fast root0Node93Domains1Fast
    root0Node93Domains0_fast_eq root0Node93Domains1_fast_eq
    root0Node93Step1Narrowing_checked (by decide)
def root0Node94Domains0 : Domains 91 State := restrict root0Node93Domains1 50 (5,0)
def root0Node94Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(3,5)]
  | 10 => some [(0,3)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5)]
  | 14 => some [(4,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(2,4)]
  | 18 => some [(1,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(6,5)]
  | 27 => some [(0,4)]
  | 28 => some [(5,4)]
  | 29 => some [(1,4)]
  | 30 => some [(8,2)]
  | 31 => some [(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(4,3)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(0,4)]
  | 41 => some [(5,4)]
  | 42 => some [(6,4)]
  | 43 => some [(1,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(1,3)]
  | 49 => some [(8,2)]
  | 50 => some [(5,0)]
  | 51 => some [(4,3)]
  | 52 => some [(7,5)]
  | 53 => some [(0,3)]
  | 54 => some [(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(8,1)]
  | 58 => some [(6,5)]
  | 59 => some [(0,4)]
  | 60 => some [(5,4)]
  | 61 => some [(1,3)]
  | 62 => some [(4,2)]
  | 63 => some [(5,3)]
  | 64 => some [(5,5),(8,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(5,5),(8,5)]
  | 68 => some [(7,0)]
  | 69 => some [(4,3)]
  | 70 => some [(0,4)]
  | 71 => some [(1,4),(3,4)]
  | 72 => some [(0,5),(6,3)]
  | 73 => some [(4,4),(7,2)]
  | 74 => some [(1,4),(7,4)]
  | 75 => some [(0,5),(6,3)]
  | 76 => some [(4,4),(7,2)]
  | 77 => some [(1,4),(7,4)]
  | 78 => some [(2,3),(2,5)]
  | 79 => some [(0,2),(6,0)]
  | 80 => some [(1,1),(7,1)]
  | 81 => some [(4,1),(7,5)]
  | 82 => some [(0,2),(6,0)]
  | 83 => some [(1,1),(7,1)]
  | 84 => some [(4,1),(7,5),(8,1)]
  | 85 => some [(1,2),(7,2)]
  | 86 => some [(4,0)]
  | 87 => some [(7,3)]
  | 88 => some [(5,2),(8,2)]
  | 89 => some [(8,0)]
  | _ => some [(7,3),(8,3)]
theorem root0Node94Domains0_fast_eq : root0Node94Domains0 = expandDomains root0Node94Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node94Domains0 v = expandDomains root0Node94Domains0Fast v from by decide) v
def root0Node94Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(5,5)]
  | 7 => [(7,0)]
  | 8 => [(4,3)]
  | 9 => [(3,5)]
  | 10 => [(0,3)]
  | 11 => [(4,1)]
  | 12 => [(0,2)]
  | 13 => [(0,5)]
  | 14 => [(4,4)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(2,4)]
  | 18 => [(1,3)]
  | 19 => [(5,2)]
  | 20 => [(8,0)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(7,1)]
  | 26 => [(6,5)]
  | 27 => [(0,4)]
  | 28 => [(5,4)]
  | 29 => [(1,4)]
  | 30 => [(8,2)]
  | 31 => [(8,0)]
  | 32 => [(7,3)]
  | 33 => [(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(7,0)]
  | 37 => [(4,3)]
  | 38 => [(7,5)]
  | 39 => [(6,0)]
  | 40 => [(0,4)]
  | 41 => [(5,4)]
  | 42 => [(6,4)]
  | 43 => [(1,2)]
  | 44 => [(8,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(7,4)]
  | 48 => [(1,3)]
  | 49 => [(8,2)]
  | 50 => [(5,0)]
  | 51 => [(4,3)]
  | 52 => [(7,5)]
  | 53 => [(0,3)]
  | 54 => [(8,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(8,1)]
  | 58 => [(6,5)]
  | 59 => [(0,4)]
  | 60 => [(5,4)]
  | 61 => [(1,3)]
  | 62 => [(4,2)]
  | 63 => [(5,3)]
  | 64 => [(5,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(5,5)]
  | 68 => [(7,0)]
  | 69 => [(4,3)]
  | 70 => [(0,4)]
  | 71 => [(1,4),(3,4)]
  | 72 => [(0,5)]
  | 73 => [(4,4)]
  | 74 => [(1,4)]
  | 75 => [(0,5)]
  | 76 => [(4,4)]
  | 77 => [(1,4)]
  | 78 => [(2,3),(2,5)]
  | 79 => [(0,2),(6,0)]
  | 80 => [(7,1)]
  | 81 => [(7,5)]
  | 82 => [(6,0)]
  | 83 => [(7,1)]
  | 84 => [(7,5)]
  | 85 => [(1,2),(7,2)]
  | 86 => [(4,0)]
  | 87 => [(7,3)]
  | 88 => [(8,2)]
  | 89 => [(8,0)]
  | _ => [(7,3)]
def root0Node94Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(3,5)]
  | 10 => some [(0,3)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5)]
  | 14 => some [(4,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(2,4)]
  | 18 => some [(1,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(6,5)]
  | 27 => some [(0,4)]
  | 28 => some [(5,4)]
  | 29 => some [(1,4)]
  | 30 => some [(8,2)]
  | 31 => some [(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(4,3)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(0,4)]
  | 41 => some [(5,4)]
  | 42 => some [(6,4)]
  | 43 => some [(1,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(1,3)]
  | 49 => some [(8,2)]
  | 50 => some [(5,0)]
  | 51 => some [(4,3)]
  | 52 => some [(7,5)]
  | 53 => some [(0,3)]
  | 54 => some [(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(8,1)]
  | 58 => some [(6,5)]
  | 59 => some [(0,4)]
  | 60 => some [(5,4)]
  | 61 => some [(1,3)]
  | 62 => some [(4,2)]
  | 63 => some [(5,3)]
  | 64 => some [(5,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(5,5)]
  | 68 => some [(7,0)]
  | 69 => some [(4,3)]
  | 70 => some [(0,4)]
  | 71 => some [(1,4),(3,4)]
  | 72 => some [(0,5)]
  | 73 => some [(4,4)]
  | 74 => some [(1,4)]
  | 75 => some [(0,5)]
  | 76 => some [(4,4)]
  | 77 => some [(1,4)]
  | 78 => some [(2,3),(2,5)]
  | 79 => some [(0,2),(6,0)]
  | 80 => some [(7,1)]
  | 81 => some [(7,5)]
  | 82 => some [(6,0)]
  | 83 => some [(7,1)]
  | 84 => some [(7,5)]
  | 85 => some [(1,2),(7,2)]
  | 86 => some [(4,0)]
  | 87 => some [(7,3)]
  | 88 => some [(8,2)]
  | 89 => some [(8,0)]
  | _ => some [(7,3)]
theorem root0Node94Domains1_fast_eq : root0Node94Domains1 = expandDomains root0Node94Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node94Domains1 v = expandDomains root0Node94Domains1Fast v from by decide) v
theorem root0Node94Step1Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq (by decide)
theorem root0Node94Step1Narrowing_checked :
    checkNarrowing table57 root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root0Node94Domains0 root0Node94Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node94Step1Chunk0_0_checked, root0Node94Step1Chunk0_1_checked, root0Node94Step1Chunk0_2_checked, root0Node94Step1Chunk0_3_checked, root0Node94Step1Chunk0_4_checked, root0Node94Step1Chunk0_5_checked, root0Node94Step1Chunk1_0_checked, root0Node94Step1Chunk1_1_checked, root0Node94Step1Chunk1_2_checked, root0Node94Step1Chunk1_3_checked, root0Node94Step1Chunk1_4_checked, root0Node94Step1Chunk1_5_checked, root0Node94Step1Chunk2_0_checked, root0Node94Step1Chunk2_1_checked, root0Node94Step1Chunk2_2_checked, root0Node94Step1Chunk2_3_checked, root0Node94Step1Chunk2_4_checked, root0Node94Step1Chunk2_5_checked, root0Node94Step1Chunk3_0_checked, root0Node94Step1Chunk3_1_checked, root0Node94Step1Chunk3_2_checked, root0Node94Step1Chunk3_3_checked, root0Node94Step1Chunk3_4_checked, root0Node94Step1Chunk3_5_checked, root0Node94Step1Chunk4_0_checked, root0Node94Step1Chunk4_1_checked, root0Node94Step1Chunk4_2_checked, root0Node94Step1Chunk4_3_checked, root0Node94Step1Chunk4_4_checked, root0Node94Step1Chunk4_5_checked, root0Node94Step1Chunk5_0_checked, root0Node94Step1Chunk5_1_checked, root0Node94Step1Chunk5_2_checked, root0Node94Step1Chunk5_3_checked, root0Node94Step1Chunk5_4_checked, root0Node94Step1Chunk5_5_checked, root0Node94Step1Chunk6_0_checked, root0Node94Step1Chunk6_1_checked, root0Node94Step1Chunk6_2_checked, root0Node94Step1Chunk6_3_checked, root0Node94Step1Chunk6_4_checked, root0Node94Step1Chunk6_5_checked, root0Node94Step1Chunk7_0_checked, root0Node94Step1Chunk7_1_checked, root0Node94Step1Chunk7_2_checked, root0Node94Step1Chunk7_3_checked, root0Node94Step1Chunk7_4_checked, root0Node94Step1Chunk7_5_checked, root0Node94Step1Chunk8_0_checked, root0Node94Step1Chunk8_1_checked, root0Node94Step1Chunk8_2_checked, root0Node94Step1Chunk8_3_checked, root0Node94Step1Chunk8_4_checked, root0Node94Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node94Step1_checked :
    checkReplacement table57 root0Node94Domains0 root0Node94Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node94Domains0 root0Node94Domains1
    root0Node94Domains0Fast root0Node94Domains1Fast
    root0Node94Domains0_fast_eq root0Node94Domains1_fast_eq
    root0Node94Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
