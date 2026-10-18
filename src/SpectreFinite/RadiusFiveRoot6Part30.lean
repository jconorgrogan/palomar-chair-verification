module

public import SpectreFinite.RadiusFiveRoot6Part29
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable12
public import SpectreFinite.RadiusFiveTable44
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node71Domains0 : Domains 91 State := restrict root6Node67Domains2 29 (3,5)
def root6Node71Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(8,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(2,4)]
  | 22 => some [(1,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(3,5)]
  | 30 => some [(7,1)]
  | 31 => some [(6,5)]
  | 32 => some [(0,4)]
  | 33 => some [(5,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,0),(2,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(4,3)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(3,1),(7,1)]
  | 50 => some [(0,1),(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,1)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(5,5),(8,5)]
  | 85 => some [(1,1)]
  | 86 => some [(8,1)]
  | 87 => some [(6,5)]
  | 88 => some [(0,4)]
  | 89 => some [(1,4),(3,4)]
  | _ => some [(0,5),(6,3)]
theorem root6Node71Domains0_fast_eq : root6Node71Domains0 = expandDomains root6Node71Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node71Domains0 v = expandDomains root6Node71Domains0Fast v from by decide) v
def root6Node71Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(8,3)]
  | 5 => [(8,5)]
  | 6 => [(1,2)]
  | 7 => [(7,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(1,3)]
  | 12 => [(8,2)]
  | 13 => [(0,3)]
  | 14 => [(4,1)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(8,1)]
  | 18 => [(6,5)]
  | 19 => [(0,4)]
  | 20 => [(5,4)]
  | 21 => [(2,4)]
  | 22 => [(1,3)]
  | 23 => [(5,2)]
  | 24 => [(8,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(4,3)]
  | 29 => [(3,5)]
  | 30 => [(7,1)]
  | 31 => [(6,5)]
  | 32 => [(0,4)]
  | 33 => [(5,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(2,4)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(4,3)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(7,1)]
  | 50 => [(6,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3)]
  | 55 => [(8,2)]
  | 56 => [(8,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(6,1)]
  | 62 => [(8,1)]
  | 63 => [(6,5)]
  | 64 => [(0,4)]
  | 65 => [(5,4)]
  | 66 => [(6,4)]
  | 67 => [(1,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0)]
  | 70 => [(8,3)]
  | 71 => [(8,5)]
  | 72 => [(7,0)]
  | 73 => [(4,3)]
  | 74 => [(7,5)]
  | 75 => [(0,3)]
  | 76 => [(8,1)]
  | 77 => [(1,5)]
  | 78 => [(6,3)]
  | 79 => [(7,2)]
  | 80 => [(7,4)]
  | 81 => [(1,3)]
  | 82 => [(4,2)]
  | 83 => [(5,3)]
  | 84 => [(5,5),(8,5)]
  | 85 => [(1,1)]
  | 86 => [(8,1)]
  | 87 => [(6,5)]
  | 88 => [(0,4)]
  | 89 => [(1,4),(3,4)]
  | _ => [(0,5),(6,3)]
def root6Node71Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(8,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(2,4)]
  | 22 => some [(1,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(3,5)]
  | 30 => some [(7,1)]
  | 31 => some [(6,5)]
  | 32 => some [(0,4)]
  | 33 => some [(5,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(4,3)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,1)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(5,5),(8,5)]
  | 85 => some [(1,1)]
  | 86 => some [(8,1)]
  | 87 => some [(6,5)]
  | 88 => some [(0,4)]
  | 89 => some [(1,4),(3,4)]
  | _ => some [(0,5),(6,3)]
theorem root6Node71Domains1_fast_eq : root6Node71Domains1 = expandDomains root6Node71Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node71Domains1 v = expandDomains root6Node71Domains1Fast v from by decide) v
theorem root6Node71Step1Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq (by decide)
theorem root6Node71Step1Narrowing_checked :
    checkNarrowing table12 root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkNarrowing_flatten table12Scope [table12Rows0_0,table12Rows0_1,table12Rows0_2,table12Rows0_3,table12Rows0_4,table12Rows0_5,table12Rows1_0,table12Rows1_1,table12Rows1_2,table12Rows1_3,table12Rows1_4,table12Rows1_5,table12Rows2_0,table12Rows2_1,table12Rows2_2,table12Rows2_3,table12Rows2_4,table12Rows2_5,table12Rows3_0,table12Rows3_1,table12Rows3_2,table12Rows3_3,table12Rows3_4,table12Rows3_5,table12Rows4_0,table12Rows4_1,table12Rows4_2,table12Rows4_3,table12Rows4_4,table12Rows4_5,table12Rows5_0,table12Rows5_1,table12Rows5_2,table12Rows5_3,table12Rows5_4,table12Rows5_5,table12Rows6_0,table12Rows6_1,table12Rows6_2,table12Rows6_3,table12Rows6_4,table12Rows6_5,table12Rows7_0,table12Rows7_1,table12Rows7_2,table12Rows7_3,table12Rows7_4,table12Rows7_5,table12Rows8_0,table12Rows8_1,table12Rows8_2,table12Rows8_3,table12Rows8_4,table12Rows8_5]
    root6Node71Domains0 root6Node71Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node71Step1Chunk0_0_checked, root6Node71Step1Chunk0_1_checked, root6Node71Step1Chunk0_2_checked, root6Node71Step1Chunk0_3_checked, root6Node71Step1Chunk0_4_checked, root6Node71Step1Chunk0_5_checked, root6Node71Step1Chunk1_0_checked, root6Node71Step1Chunk1_1_checked, root6Node71Step1Chunk1_2_checked, root6Node71Step1Chunk1_3_checked, root6Node71Step1Chunk1_4_checked, root6Node71Step1Chunk1_5_checked, root6Node71Step1Chunk2_0_checked, root6Node71Step1Chunk2_1_checked, root6Node71Step1Chunk2_2_checked, root6Node71Step1Chunk2_3_checked, root6Node71Step1Chunk2_4_checked, root6Node71Step1Chunk2_5_checked, root6Node71Step1Chunk3_0_checked, root6Node71Step1Chunk3_1_checked, root6Node71Step1Chunk3_2_checked, root6Node71Step1Chunk3_3_checked, root6Node71Step1Chunk3_4_checked, root6Node71Step1Chunk3_5_checked, root6Node71Step1Chunk4_0_checked, root6Node71Step1Chunk4_1_checked, root6Node71Step1Chunk4_2_checked, root6Node71Step1Chunk4_3_checked, root6Node71Step1Chunk4_4_checked, root6Node71Step1Chunk4_5_checked, root6Node71Step1Chunk5_0_checked, root6Node71Step1Chunk5_1_checked, root6Node71Step1Chunk5_2_checked, root6Node71Step1Chunk5_3_checked, root6Node71Step1Chunk5_4_checked, root6Node71Step1Chunk5_5_checked, root6Node71Step1Chunk6_0_checked, root6Node71Step1Chunk6_1_checked, root6Node71Step1Chunk6_2_checked, root6Node71Step1Chunk6_3_checked, root6Node71Step1Chunk6_4_checked, root6Node71Step1Chunk6_5_checked, root6Node71Step1Chunk7_0_checked, root6Node71Step1Chunk7_1_checked, root6Node71Step1Chunk7_2_checked, root6Node71Step1Chunk7_3_checked, root6Node71Step1Chunk7_4_checked, root6Node71Step1Chunk7_5_checked, root6Node71Step1Chunk8_0_checked, root6Node71Step1Chunk8_1_checked, root6Node71Step1Chunk8_2_checked, root6Node71Step1Chunk8_3_checked, root6Node71Step1Chunk8_4_checked, root6Node71Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node71Step1_checked :
    checkReplacement table12 root6Node71Domains0 root6Node71Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node71Domains0 root6Node71Domains1
    root6Node71Domains0Fast root6Node71Domains1Fast
    root6Node71Domains0_fast_eq root6Node71Domains1_fast_eq
    root6Node71Step1Narrowing_checked (by decide)
def root6Node72Domains0 : Domains 91 State := restrict root6Node71Domains1 84 (5,5)
def root6Node72Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(8,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(2,4)]
  | 22 => some [(1,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(3,5)]
  | 30 => some [(7,1)]
  | 31 => some [(6,5)]
  | 32 => some [(0,4)]
  | 33 => some [(5,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(4,3)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,1)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(5,5)]
  | 85 => some [(1,1)]
  | 86 => some [(8,1)]
  | 87 => some [(6,5)]
  | 88 => some [(0,4)]
  | 89 => some [(1,4),(3,4)]
  | _ => some [(0,5),(6,3)]
theorem root6Node72Domains0_fast_eq : root6Node72Domains0 = expandDomains root6Node72Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node72Domains0 v = expandDomains root6Node72Domains0Fast v from by decide) v
def root6Node72Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(8,3)]
  | 5 => [(8,5)]
  | 6 => [(1,2)]
  | 7 => [(7,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(1,3)]
  | 12 => [(8,2)]
  | 13 => [(0,3)]
  | 14 => [(4,1)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(8,1)]
  | 18 => [(6,5)]
  | 19 => [(0,4)]
  | 20 => [(5,4)]
  | 21 => [(2,4)]
  | 22 => [(1,3)]
  | 23 => [(5,2)]
  | 24 => [(8,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(4,3)]
  | 29 => [(3,5)]
  | 30 => [(7,1)]
  | 31 => [(6,5)]
  | 32 => [(0,4)]
  | 33 => [(5,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(2,4)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(4,3)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(7,1)]
  | 50 => [(6,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3)]
  | 55 => [(8,2)]
  | 56 => [(8,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(6,1)]
  | 62 => [(8,1)]
  | 63 => [(6,5)]
  | 64 => [(0,4)]
  | 65 => [(5,4)]
  | 66 => [(6,4)]
  | 67 => [(1,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0)]
  | 70 => [(8,3)]
  | 71 => [(8,5)]
  | 72 => [(7,0)]
  | 73 => [(4,3)]
  | 74 => [(7,5)]
  | 75 => [(0,3)]
  | 76 => [(8,1)]
  | 77 => [(1,5)]
  | 78 => [(6,3)]
  | 79 => [(7,2)]
  | 80 => [(7,4)]
  | 81 => [(1,3)]
  | 82 => [(4,2)]
  | 83 => [(5,3)]
  | 84 => [(5,5)]
  | 85 => [(1,1)]
  | 86 => [(8,1)]
  | 87 => [(6,5)]
  | 88 => [(0,4)]
  | 89 => [(1,4)]
  | _ => [(0,5)]
def root6Node72Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(8,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(2,4)]
  | 22 => some [(1,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(3,5)]
  | 30 => some [(7,1)]
  | 31 => some [(6,5)]
  | 32 => some [(0,4)]
  | 33 => some [(5,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(4,3)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,1)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(5,5)]
  | 85 => some [(1,1)]
  | 86 => some [(8,1)]
  | 87 => some [(6,5)]
  | 88 => some [(0,4)]
  | 89 => some [(1,4)]
  | _ => some [(0,5)]
theorem root6Node72Domains1_fast_eq : root6Node72Domains1 = expandDomains root6Node72Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node72Domains1 v = expandDomains root6Node72Domains1Fast v from by decide) v
theorem root6Node72Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq (by decide)
theorem root6Node72Step1Narrowing_checked :
    checkNarrowing table56 root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root6Node72Domains0 root6Node72Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node72Step1Chunk0_0_checked, root6Node72Step1Chunk0_1_checked, root6Node72Step1Chunk0_2_checked, root6Node72Step1Chunk0_3_checked, root6Node72Step1Chunk0_4_checked, root6Node72Step1Chunk0_5_checked, root6Node72Step1Chunk1_0_checked, root6Node72Step1Chunk1_1_checked, root6Node72Step1Chunk1_2_checked, root6Node72Step1Chunk1_3_checked, root6Node72Step1Chunk1_4_checked, root6Node72Step1Chunk1_5_checked, root6Node72Step1Chunk2_0_checked, root6Node72Step1Chunk2_1_checked, root6Node72Step1Chunk2_2_checked, root6Node72Step1Chunk2_3_checked, root6Node72Step1Chunk2_4_checked, root6Node72Step1Chunk2_5_checked, root6Node72Step1Chunk3_0_checked, root6Node72Step1Chunk3_1_checked, root6Node72Step1Chunk3_2_checked, root6Node72Step1Chunk3_3_checked, root6Node72Step1Chunk3_4_checked, root6Node72Step1Chunk3_5_checked, root6Node72Step1Chunk4_0_checked, root6Node72Step1Chunk4_1_checked, root6Node72Step1Chunk4_2_checked, root6Node72Step1Chunk4_3_checked, root6Node72Step1Chunk4_4_checked, root6Node72Step1Chunk4_5_checked, root6Node72Step1Chunk5_0_checked, root6Node72Step1Chunk5_1_checked, root6Node72Step1Chunk5_2_checked, root6Node72Step1Chunk5_3_checked, root6Node72Step1Chunk5_4_checked, root6Node72Step1Chunk5_5_checked, root6Node72Step1Chunk6_0_checked, root6Node72Step1Chunk6_1_checked, root6Node72Step1Chunk6_2_checked, root6Node72Step1Chunk6_3_checked, root6Node72Step1Chunk6_4_checked, root6Node72Step1Chunk6_5_checked, root6Node72Step1Chunk7_0_checked, root6Node72Step1Chunk7_1_checked, root6Node72Step1Chunk7_2_checked, root6Node72Step1Chunk7_3_checked, root6Node72Step1Chunk7_4_checked, root6Node72Step1Chunk7_5_checked, root6Node72Step1Chunk8_0_checked, root6Node72Step1Chunk8_1_checked, root6Node72Step1Chunk8_2_checked, root6Node72Step1Chunk8_3_checked, root6Node72Step1Chunk8_4_checked, root6Node72Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node72Step1_checked :
    checkReplacement table56 root6Node72Domains0 root6Node72Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node72Domains0 root6Node72Domains1
    root6Node72Domains0Fast root6Node72Domains1Fast
    root6Node72Domains0_fast_eq root6Node72Domains1_fast_eq
    root6Node72Step1Narrowing_checked (by decide)
theorem root6Node72Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node72Domains1 (.output 35) = true := by decide
def root6Node73Domains0 : Domains 91 State := restrict root6Node71Domains1 84 (8,5)
def root6Node73Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(8,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(2,4)]
  | 22 => some [(1,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(3,5)]
  | 30 => some [(7,1)]
  | 31 => some [(6,5)]
  | 32 => some [(0,4)]
  | 33 => some [(5,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(4,3)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,1)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(8,5)]
  | 85 => some [(1,1)]
  | 86 => some [(8,1)]
  | 87 => some [(6,5)]
  | 88 => some [(0,4)]
  | 89 => some [(1,4),(3,4)]
  | _ => some [(0,5),(6,3)]
theorem root6Node73Domains0_fast_eq : root6Node73Domains0 = expandDomains root6Node73Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node73Domains0 v = expandDomains root6Node73Domains0Fast v from by decide) v
def root6Node73Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(8,3)]
  | 5 => [(8,5)]
  | 6 => [(1,2)]
  | 7 => [(7,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(1,3)]
  | 12 => [(8,2)]
  | 13 => [(0,3)]
  | 14 => [(4,1)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(8,1)]
  | 18 => [(6,5)]
  | 19 => [(0,4)]
  | 20 => [(5,4)]
  | 21 => [(2,4)]
  | 22 => [(1,3)]
  | 23 => [(5,2)]
  | 24 => [(8,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(4,3)]
  | 29 => [(3,5)]
  | 30 => [(7,1)]
  | 31 => [(6,5)]
  | 32 => [(0,4)]
  | 33 => [(5,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(2,4)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(4,3)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(7,1)]
  | 50 => [(6,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3)]
  | 55 => [(8,2)]
  | 56 => [(8,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(6,1)]
  | 62 => [(8,1)]
  | 63 => [(6,5)]
  | 64 => [(0,4)]
  | 65 => [(5,4)]
  | 66 => [(6,4)]
  | 67 => [(1,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0)]
  | 70 => [(8,3)]
  | 71 => [(8,5)]
  | 72 => [(7,0)]
  | 73 => [(4,3)]
  | 74 => [(7,5)]
  | 75 => [(0,3)]
  | 76 => [(8,1)]
  | 77 => [(1,5)]
  | 78 => [(6,3)]
  | 79 => [(7,2)]
  | 80 => [(7,4)]
  | 81 => [(1,3)]
  | 82 => [(4,2)]
  | 83 => [(5,3)]
  | 84 => [(8,5)]
  | 85 => [(1,1)]
  | 86 => [(8,1)]
  | 87 => [(6,5)]
  | 88 => [(0,4)]
  | 89 => [(3,4)]
  | _ => [(6,3)]
def root6Node73Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(8,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(2,4)]
  | 22 => some [(1,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(3,5)]
  | 30 => some [(7,1)]
  | 31 => some [(6,5)]
  | 32 => some [(0,4)]
  | 33 => some [(5,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(4,3)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,1)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(8,5)]
  | 85 => some [(1,1)]
  | 86 => some [(8,1)]
  | 87 => some [(6,5)]
  | 88 => some [(0,4)]
  | 89 => some [(3,4)]
  | _ => some [(6,3)]
theorem root6Node73Domains1_fast_eq : root6Node73Domains1 = expandDomains root6Node73Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node73Domains1 v = expandDomains root6Node73Domains1Fast v from by decide) v
theorem root6Node73Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Narrowing_checked :
    checkNarrowing table56 root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root6Node73Domains0 root6Node73Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node73Step1Chunk0_0_checked, root6Node73Step1Chunk0_1_checked, root6Node73Step1Chunk0_2_checked, root6Node73Step1Chunk0_3_checked, root6Node73Step1Chunk0_4_checked, root6Node73Step1Chunk0_5_checked, root6Node73Step1Chunk1_0_checked, root6Node73Step1Chunk1_1_checked, root6Node73Step1Chunk1_2_checked, root6Node73Step1Chunk1_3_checked, root6Node73Step1Chunk1_4_checked, root6Node73Step1Chunk1_5_checked, root6Node73Step1Chunk2_0_checked, root6Node73Step1Chunk2_1_checked, root6Node73Step1Chunk2_2_checked, root6Node73Step1Chunk2_3_checked, root6Node73Step1Chunk2_4_checked, root6Node73Step1Chunk2_5_checked, root6Node73Step1Chunk3_0_checked, root6Node73Step1Chunk3_1_checked, root6Node73Step1Chunk3_2_checked, root6Node73Step1Chunk3_3_checked, root6Node73Step1Chunk3_4_checked, root6Node73Step1Chunk3_5_checked, root6Node73Step1Chunk4_0_checked, root6Node73Step1Chunk4_1_checked, root6Node73Step1Chunk4_2_checked, root6Node73Step1Chunk4_3_checked, root6Node73Step1Chunk4_4_checked, root6Node73Step1Chunk4_5_checked, root6Node73Step1Chunk5_0_checked, root6Node73Step1Chunk5_1_checked, root6Node73Step1Chunk5_2_checked, root6Node73Step1Chunk5_3_checked, root6Node73Step1Chunk5_4_checked, root6Node73Step1Chunk5_5_checked, root6Node73Step1Chunk6_0_checked, root6Node73Step1Chunk6_1_checked, root6Node73Step1Chunk6_2_checked, root6Node73Step1Chunk6_3_checked, root6Node73Step1Chunk6_4_checked, root6Node73Step1Chunk6_5_checked, root6Node73Step1Chunk7_0_checked, root6Node73Step1Chunk7_1_checked, root6Node73Step1Chunk7_2_checked, root6Node73Step1Chunk7_3_checked, root6Node73Step1Chunk7_4_checked, root6Node73Step1Chunk7_5_checked, root6Node73Step1Chunk8_0_checked, root6Node73Step1Chunk8_1_checked, root6Node73Step1Chunk8_2_checked, root6Node73Step1Chunk8_3_checked, root6Node73Step1Chunk8_4_checked, root6Node73Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node73Step1_checked :
    checkReplacement table56 root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq
    root6Node73Step1Narrowing_checked (by decide)
theorem root6Node73Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node73Domains1 (.output 36) = true := by decide
def root6Node74Domains0 : Domains 91 State := restrict root6Node14Domains4 6 (7,2)
def root6Node74Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2),(5,2),(7,0),(8,2)]
  | 1 => some [(4,3),(5,0),(5,3),(8,3)]
  | 2 => some [(4,5),(7,5),(8,5)]
  | 3 => some [(1,0),(6,0),(7,0)]
  | 4 => some [(4,3),(7,1),(8,3)]
  | 5 => some [(1,5),(7,5),(8,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4),(8,4)]
  | 8 => some [(0,0),(1,3),(6,3)]
  | 9 => some [(7,2),(8,2)]
  | 10 => some [(4,0),(5,0),(7,4),(8,0)]
  | 11 => some [(1,3),(4,5),(7,3)]
  | 12 => some [(4,2),(7,0),(8,2)]
  | 13 => some [(0,3),(1,1),(6,1)]
  | 14 => some [(4,1),(8,1)]
  | 15 => some [(0,2),(1,5),(6,5)]
  | 16 => some [(0,4),(1,1),(6,1)]
  | 17 => some [(5,1),(5,4),(8,1)]
  | 18 => some [(0,0),(0,1),(6,4),(6,5)]
  | 19 => some [(0,4),(1,2),(6,2),(7,2)]
  | 20 => some [(1,4),(3,4),(5,4),(7,4)]
  | 21 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(7,0),(8,0)]
  | 22 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 23 => some [(5,2),(5,5)]
  | 24 => some [(7,0),(8,0)]
  | 25 => some [(4,3),(8,3)]
  | 26 => some [(1,5),(3,5),(5,5)]
  | 27 => some [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 28 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 29 => some [(0,2),(1,5),(3,5),(6,0)]
  | 30 => some [(0,4),(1,1),(3,1),(4,4),(5,1),(5,4),(7,1),(8,4)]
  | 31 => some [(0,1),(1,4),(6,5)]
  | 32 => some [(0,4),(0,5),(6,2)]
  | 33 => some [(4,4),(5,4),(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0),(2,4),(4,4)]
  | 37 => some [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 38 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 39 => some [(2,0),(2,4),(4,0),(8,0)]
  | 40 => some [(3,0),(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 41 => some [(2,5),(4,5),(7,5),(8,5)]
  | 42 => some [(1,0),(6,0),(7,0)]
  | 43 => some [(4,3),(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1),(7,1)]
  | 47 => some [(0,1),(1,5),(6,5),(7,5)]
  | 48 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 49 => some [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 50 => some [(0,1),(1,4),(6,4),(6,5)]
  | 51 => some [(0,0),(1,3),(7,3)]
  | 52 => some [(7,2),(8,2)]
  | 53 => some [(4,0),(7,4),(8,0)]
  | 54 => some [(1,3),(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0),(8,0)]
  | 57 => some [(4,5),(7,3)]
  | 58 => some [(1,0),(4,2),(7,0),(8,2)]
  | 59 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 60 => some [(4,5),(7,5),(8,5)]
  | 61 => some [(0,4),(6,1),(6,2)]
  | 62 => some [(5,1),(5,4),(8,1),(8,4)]
  | 63 => some [(0,1),(6,4),(6,5)]
  | 64 => some [(0,4),(1,2),(6,2)]
  | 65 => some [(5,4),(8,4)]
  | 66 => some [(0,0),(6,4)]
  | 67 => some [(1,2),(7,2)]
  | 68 => some [(4,0),(7,4),(8,4)]
  | 69 => some [(0,0),(1,3),(6,3),(7,3)]
  | 70 => some [(4,3),(7,1),(8,3)]
  | 71 => some [(5,5),(7,5),(8,5)]
  | 72 => some [(0,3),(1,0),(7,0)]
  | 73 => some [(4,3),(7,1),(8,1)]
  | 74 => some [(1,5),(3,5),(7,5)]
  | 75 => some [(0,3),(6,1)]
  | 76 => some [(4,1),(5,1),(8,1)]
  | 77 => some [(0,1),(0,2),(1,5),(6,5)]
  | 78 => some [(0,5),(1,3),(6,3),(7,3)]
  | 79 => some [(4,2),(4,4),(7,2),(8,2)]
  | 80 => some [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 81 => some [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 82 => some [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | 83 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 84 => some [(5,2),(5,5),(8,5)]
  | 85 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 86 => some [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(7,5),(8,1)]
  | 87 => some [(0,0),(0,1),(0,2),(0,5),(6,0),(6,3),(6,4),(6,5)]
  | 88 => some [(0,4),(1,1),(1,2),(3,1),(4,4),(6,2),(7,1),(7,2)]
  | 89 => some [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => some [(0,4),(0,5),(1,3),(6,2),(6,3)]
theorem root6Node74Domains0_fast_eq : root6Node74Domains0 = expandDomains root6Node74Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node74Domains0 v = expandDomains root6Node74Domains0Fast v from by decide) v
def root6Node74Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2),(5,2),(7,0),(8,2)]
  | 1 => [(4,3),(5,0),(5,3),(8,3)]
  | 2 => [(4,5),(7,5),(8,5)]
  | 3 => [(1,0),(6,0),(7,0)]
  | 4 => [(4,3),(7,1),(8,3)]
  | 5 => [(1,5),(7,5),(8,5)]
  | 6 => [(7,2)]
  | 7 => [(7,4)]
  | 8 => [(1,3),(6,3)]
  | 9 => [(7,2),(8,2)]
  | 10 => [(4,0),(5,0),(7,4),(8,0)]
  | 11 => [(1,3),(4,5),(7,3)]
  | 12 => [(4,2),(7,0),(8,2)]
  | 13 => [(1,1),(6,1)]
  | 14 => [(4,1),(8,1)]
  | 15 => [(0,2),(6,5)]
  | 16 => [(0,4),(1,1)]
  | 17 => [(5,1),(5,4),(8,1)]
  | 18 => [(0,0),(0,1),(6,4),(6,5)]
  | 19 => [(0,4),(1,2),(6,2),(7,2)]
  | 20 => [(1,4),(3,4),(5,4),(7,4)]
  | 21 => [(2,0),(4,0),(7,0),(8,0)]
  | 22 => [(7,3),(8,3)]
  | 23 => [(5,2),(5,5)]
  | 24 => [(7,0),(8,0)]
  | 25 => [(4,3),(8,3)]
  | 26 => [(1,5),(3,5),(5,5)]
  | 27 => [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 28 => [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 29 => [(0,2),(1,5),(3,5),(6,0)]
  | 30 => [(3,1),(4,4),(5,1),(5,4),(8,4)]
  | 31 => [(0,1),(1,4)]
  | 32 => [(0,5),(6,2)]
  | 33 => [(4,4),(8,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,0),(2,4),(4,4)]
  | 37 => [(0,0),(1,3),(6,4),(7,3)]
  | 38 => [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 39 => [(2,0),(2,4),(4,0),(8,0)]
  | 40 => [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 41 => [(4,5),(7,5),(8,5)]
  | 42 => [(1,0),(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(3,1),(7,1)]
  | 47 => [(0,1),(1,5),(6,5),(7,5)]
  | 48 => [(0,3),(0,4),(6,1),(6,2)]
  | 49 => [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 50 => [(0,1),(1,4),(6,4),(6,5)]
  | 51 => [(0,0),(1,3),(7,3)]
  | 52 => [(7,2),(8,2)]
  | 53 => [(4,0),(8,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0),(8,0)]
  | 57 => [(4,5),(7,3)]
  | 58 => [(1,0),(4,2),(7,0)]
  | 59 => [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 60 => [(4,5),(7,5),(8,5)]
  | 61 => [(0,4),(6,1),(6,2)]
  | 62 => [(5,1),(5,4),(8,4)]
  | 63 => [(0,1),(6,4)]
  | 64 => [(1,2),(6,2)]
  | 65 => [(8,4)]
  | 66 => [(0,0),(6,4)]
  | 67 => [(1,2),(7,2)]
  | 68 => [(4,0),(7,4),(8,4)]
  | 69 => [(0,0),(1,3),(6,3),(7,3)]
  | 70 => [(4,3),(7,1),(8,3)]
  | 71 => [(7,5),(8,5)]
  | 72 => [(0,3),(1,0)]
  | 73 => [(7,1),(8,1)]
  | 74 => [(1,5),(7,5)]
  | 75 => [(0,3),(6,1)]
  | 76 => [(4,1),(5,1),(8,1)]
  | 77 => [(0,1),(0,2),(1,5),(6,5)]
  | 78 => [(1,3),(6,3),(7,3)]
  | 79 => [(4,2),(7,2),(8,2)]
  | 80 => [(4,0),(5,0),(5,3),(8,0)]
  | 81 => [(4,5),(5,5),(7,3),(8,5)]
  | 82 => [(4,2),(7,0)]
  | 83 => [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 84 => [(5,2),(5,5),(8,5)]
  | 85 => [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 86 => [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(7,5),(8,1)]
  | 87 => [(0,0),(0,1),(0,2),(0,5),(6,0),(6,3),(6,4),(6,5)]
  | 88 => [(0,4),(1,1),(1,2),(3,1),(4,4),(6,2),(7,1),(7,2)]
  | 89 => [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => [(0,4),(0,5),(1,3),(6,2),(6,3)]
def root6Node74Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2),(5,2),(7,0),(8,2)]
  | 1 => some [(4,3),(5,0),(5,3),(8,3)]
  | 2 => some [(4,5),(7,5),(8,5)]
  | 3 => some [(1,0),(6,0),(7,0)]
  | 4 => some [(4,3),(7,1),(8,3)]
  | 5 => some [(1,5),(7,5),(8,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3),(6,3)]
  | 9 => some [(7,2),(8,2)]
  | 10 => some [(4,0),(5,0),(7,4),(8,0)]
  | 11 => some [(1,3),(4,5),(7,3)]
  | 12 => some [(4,2),(7,0),(8,2)]
  | 13 => some [(1,1),(6,1)]
  | 14 => some [(4,1),(8,1)]
  | 15 => some [(0,2),(6,5)]
  | 16 => some [(0,4),(1,1)]
  | 17 => some [(5,1),(5,4),(8,1)]
  | 18 => some [(0,0),(0,1),(6,4),(6,5)]
  | 19 => some [(0,4),(1,2),(6,2),(7,2)]
  | 20 => some [(1,4),(3,4),(5,4),(7,4)]
  | 21 => some [(2,0),(4,0),(7,0),(8,0)]
  | 22 => some [(7,3),(8,3)]
  | 23 => some [(5,2),(5,5)]
  | 24 => some [(7,0),(8,0)]
  | 25 => some [(4,3),(8,3)]
  | 26 => some [(1,5),(3,5),(5,5)]
  | 27 => some [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 28 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 29 => some [(0,2),(1,5),(3,5),(6,0)]
  | 30 => some [(3,1),(4,4),(5,1),(5,4),(8,4)]
  | 31 => some [(0,1),(1,4)]
  | 32 => some [(0,5),(6,2)]
  | 33 => some [(4,4),(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0),(2,4),(4,4)]
  | 37 => some [(0,0),(1,3),(6,4),(7,3)]
  | 38 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 39 => some [(2,0),(2,4),(4,0),(8,0)]
  | 40 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 41 => some [(4,5),(7,5),(8,5)]
  | 42 => some [(1,0),(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1),(7,1)]
  | 47 => some [(0,1),(1,5),(6,5),(7,5)]
  | 48 => some [(0,3),(0,4),(6,1),(6,2)]
  | 49 => some [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 50 => some [(0,1),(1,4),(6,4),(6,5)]
  | 51 => some [(0,0),(1,3),(7,3)]
  | 52 => some [(7,2),(8,2)]
  | 53 => some [(4,0),(8,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0),(8,0)]
  | 57 => some [(4,5),(7,3)]
  | 58 => some [(1,0),(4,2),(7,0)]
  | 59 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 60 => some [(4,5),(7,5),(8,5)]
  | 61 => some [(0,4),(6,1),(6,2)]
  | 62 => some [(5,1),(5,4),(8,4)]
  | 63 => some [(0,1),(6,4)]
  | 64 => some [(1,2),(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0),(6,4)]
  | 67 => some [(1,2),(7,2)]
  | 68 => some [(4,0),(7,4),(8,4)]
  | 69 => some [(0,0),(1,3),(6,3),(7,3)]
  | 70 => some [(4,3),(7,1),(8,3)]
  | 71 => some [(7,5),(8,5)]
  | 72 => some [(0,3),(1,0)]
  | 73 => some [(7,1),(8,1)]
  | 74 => some [(1,5),(7,5)]
  | 75 => some [(0,3),(6,1)]
  | 76 => some [(4,1),(5,1),(8,1)]
  | 77 => some [(0,1),(0,2),(1,5),(6,5)]
  | 78 => some [(1,3),(6,3),(7,3)]
  | 79 => some [(4,2),(7,2),(8,2)]
  | 80 => some [(4,0),(5,0),(5,3),(8,0)]
  | 81 => some [(4,5),(5,5),(7,3),(8,5)]
  | 82 => some [(4,2),(7,0)]
  | 83 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 84 => some [(5,2),(5,5),(8,5)]
  | 85 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 86 => some [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(7,5),(8,1)]
  | 87 => some [(0,0),(0,1),(0,2),(0,5),(6,0),(6,3),(6,4),(6,5)]
  | 88 => some [(0,4),(1,1),(1,2),(3,1),(4,4),(6,2),(7,1),(7,2)]
  | 89 => some [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => some [(0,4),(0,5),(1,3),(6,2),(6,3)]
theorem root6Node74Domains1_fast_eq : root6Node74Domains1 = expandDomains root6Node74Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node74Domains1 v = expandDomains root6Node74Domains1Fast v from by decide) v
theorem root6Node74Step1Chunk0_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_0⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk0_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_1⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk0_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_2⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk0_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_3⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk0_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_4⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk0_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_5⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk1_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_0⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk1_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_1⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk1_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_2⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk1_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_3⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk1_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_4⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk1_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_5⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk2_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_0⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk2_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_1⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk2_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_2⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk2_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_3⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk2_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_4⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk2_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_5⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk3_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_0⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk3_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_1⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk3_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_2⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk3_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_3⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk3_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_4⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk3_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_5⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk4_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_0⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk4_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_1⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk4_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_2⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk4_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_3⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk4_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_4⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk4_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_5⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk5_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_0⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk5_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_1⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk5_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_2⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk5_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_3⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk5_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_4⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk5_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_5⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk6_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_0⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk6_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_1⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk6_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_2⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk6_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_3⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk6_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_4⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk6_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_5⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk7_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_0⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk7_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_1⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk7_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_2⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk7_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_3⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk7_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_4⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk7_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_5⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk8_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_0⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk8_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_1⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk8_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_2⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk8_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_3⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk8_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_4⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Chunk8_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_5⟩
      root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq (by decide)
theorem root6Node74Step1Narrowing_checked :
    checkNarrowing table44 root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkNarrowing_flatten table44Scope [table44Rows0_0,table44Rows0_1,table44Rows0_2,table44Rows0_3,table44Rows0_4,table44Rows0_5,table44Rows1_0,table44Rows1_1,table44Rows1_2,table44Rows1_3,table44Rows1_4,table44Rows1_5,table44Rows2_0,table44Rows2_1,table44Rows2_2,table44Rows2_3,table44Rows2_4,table44Rows2_5,table44Rows3_0,table44Rows3_1,table44Rows3_2,table44Rows3_3,table44Rows3_4,table44Rows3_5,table44Rows4_0,table44Rows4_1,table44Rows4_2,table44Rows4_3,table44Rows4_4,table44Rows4_5,table44Rows5_0,table44Rows5_1,table44Rows5_2,table44Rows5_3,table44Rows5_4,table44Rows5_5,table44Rows6_0,table44Rows6_1,table44Rows6_2,table44Rows6_3,table44Rows6_4,table44Rows6_5,table44Rows7_0,table44Rows7_1,table44Rows7_2,table44Rows7_3,table44Rows7_4,table44Rows7_5,table44Rows8_0,table44Rows8_1,table44Rows8_2,table44Rows8_3,table44Rows8_4,table44Rows8_5]
    root6Node74Domains0 root6Node74Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node74Step1Chunk0_0_checked, root6Node74Step1Chunk0_1_checked, root6Node74Step1Chunk0_2_checked, root6Node74Step1Chunk0_3_checked, root6Node74Step1Chunk0_4_checked, root6Node74Step1Chunk0_5_checked, root6Node74Step1Chunk1_0_checked, root6Node74Step1Chunk1_1_checked, root6Node74Step1Chunk1_2_checked, root6Node74Step1Chunk1_3_checked, root6Node74Step1Chunk1_4_checked, root6Node74Step1Chunk1_5_checked, root6Node74Step1Chunk2_0_checked, root6Node74Step1Chunk2_1_checked, root6Node74Step1Chunk2_2_checked, root6Node74Step1Chunk2_3_checked, root6Node74Step1Chunk2_4_checked, root6Node74Step1Chunk2_5_checked, root6Node74Step1Chunk3_0_checked, root6Node74Step1Chunk3_1_checked, root6Node74Step1Chunk3_2_checked, root6Node74Step1Chunk3_3_checked, root6Node74Step1Chunk3_4_checked, root6Node74Step1Chunk3_5_checked, root6Node74Step1Chunk4_0_checked, root6Node74Step1Chunk4_1_checked, root6Node74Step1Chunk4_2_checked, root6Node74Step1Chunk4_3_checked, root6Node74Step1Chunk4_4_checked, root6Node74Step1Chunk4_5_checked, root6Node74Step1Chunk5_0_checked, root6Node74Step1Chunk5_1_checked, root6Node74Step1Chunk5_2_checked, root6Node74Step1Chunk5_3_checked, root6Node74Step1Chunk5_4_checked, root6Node74Step1Chunk5_5_checked, root6Node74Step1Chunk6_0_checked, root6Node74Step1Chunk6_1_checked, root6Node74Step1Chunk6_2_checked, root6Node74Step1Chunk6_3_checked, root6Node74Step1Chunk6_4_checked, root6Node74Step1Chunk6_5_checked, root6Node74Step1Chunk7_0_checked, root6Node74Step1Chunk7_1_checked, root6Node74Step1Chunk7_2_checked, root6Node74Step1Chunk7_3_checked, root6Node74Step1Chunk7_4_checked, root6Node74Step1Chunk7_5_checked, root6Node74Step1Chunk8_0_checked, root6Node74Step1Chunk8_1_checked, root6Node74Step1Chunk8_2_checked, root6Node74Step1Chunk8_3_checked, root6Node74Step1Chunk8_4_checked, root6Node74Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node74Step1_checked :
    checkReplacement table44 root6Node74Domains0 root6Node74Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node74Domains0 root6Node74Domains1
    root6Node74Domains0Fast root6Node74Domains1Fast
    root6Node74Domains0_fast_eq root6Node74Domains1_fast_eq
    root6Node74Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
