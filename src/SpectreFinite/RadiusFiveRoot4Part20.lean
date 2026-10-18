module

public import SpectreFinite.RadiusFiveRoot4Part19
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable13
public import SpectreFinite.RadiusFiveTable5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node50Domains0 : Domains 91 State := restrict root4Node49Domains1 30 (4,5)
def root4Node50Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(4,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(7,4)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(6,5)]
  | 40 => some [(0,0),(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(6,3)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(1,1),(6,1)]
  | 52 => some [(4,1)]
  | 53 => some [(0,2)]
  | 54 => some [(1,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(7,3)]
  | 62 => some [(5,2)]
  | 63 => some [(8,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(6,2)]
  | 71 => some [(8,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(4,4)]
  | 75 => some [(0,0)]
  | 76 => some [(3,2)]
  | 77 => some [(4,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(7,1)]
  | 82 => some [(1,5)]
  | 83 => some [(6,1)]
  | 84 => some [(5,1)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(7,0)]
  | _ => some [(8,3)]
theorem root4Node50Domains0_fast_eq : root4Node50Domains0 = expandDomains root4Node50Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node50Domains0 v = expandDomains root4Node50Domains0Fast v from by decide) v
def root4Node50Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,4)]
  | 6 => [(4,5)]
  | 7 => [(1,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(6,0)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(0,0)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(7,4)]
  | 30 => [(4,5)]
  | 31 => [(7,0)]
  | 32 => [(8,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(8,1)]
  | 39 => [(6,5)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(6,3)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(7,0)]
  | 51 => [(6,1)]
  | 52 => [(4,1)]
  | 53 => [(0,2)]
  | 54 => [(1,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(7,3)]
  | 62 => [(5,2)]
  | 63 => [(8,0)]
  | 64 => [(8,3)]
  | 65 => [(5,5)]
  | 66 => [(1,0)]
  | 67 => [(2,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(6,2)]
  | 71 => [(8,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(4,4)]
  | 75 => [(0,0)]
  | 76 => [(3,2)]
  | 77 => [(4,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(7,1)]
  | 82 => [(1,5)]
  | 83 => [(6,1)]
  | 84 => [(5,1)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(7,0)]
  | _ => [(8,3)]
def root4Node50Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(4,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(7,4)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(6,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(6,3)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(4,1)]
  | 53 => some [(0,2)]
  | 54 => some [(1,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(7,3)]
  | 62 => some [(5,2)]
  | 63 => some [(8,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(6,2)]
  | 71 => some [(8,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(4,4)]
  | 75 => some [(0,0)]
  | 76 => some [(3,2)]
  | 77 => some [(4,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(7,1)]
  | 82 => some [(1,5)]
  | 83 => some [(6,1)]
  | 84 => some [(5,1)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(7,0)]
  | _ => some [(8,3)]
theorem root4Node50Domains1_fast_eq : root4Node50Domains1 = expandDomains root4Node50Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node50Domains1 v = expandDomains root4Node50Domains1Fast v from by decide) v
theorem root4Node50Step1Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq (by decide)
theorem root4Node50Step1Narrowing_checked :
    checkNarrowing table13 root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkNarrowing_flatten table13Scope [table13Rows0_0,table13Rows0_1,table13Rows0_2,table13Rows0_3,table13Rows0_4,table13Rows0_5,table13Rows1_0,table13Rows1_1,table13Rows1_2,table13Rows1_3,table13Rows1_4,table13Rows1_5,table13Rows2_0,table13Rows2_1,table13Rows2_2,table13Rows2_3,table13Rows2_4,table13Rows2_5,table13Rows3_0,table13Rows3_1,table13Rows3_2,table13Rows3_3,table13Rows3_4,table13Rows3_5,table13Rows4_0,table13Rows4_1,table13Rows4_2,table13Rows4_3,table13Rows4_4,table13Rows4_5,table13Rows5_0,table13Rows5_1,table13Rows5_2,table13Rows5_3,table13Rows5_4,table13Rows5_5,table13Rows6_0,table13Rows6_1,table13Rows6_2,table13Rows6_3,table13Rows6_4,table13Rows6_5,table13Rows7_0,table13Rows7_1,table13Rows7_2,table13Rows7_3,table13Rows7_4,table13Rows7_5,table13Rows8_0,table13Rows8_1,table13Rows8_2,table13Rows8_3,table13Rows8_4,table13Rows8_5]
    root4Node50Domains0 root4Node50Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node50Step1Chunk0_0_checked, root4Node50Step1Chunk0_1_checked, root4Node50Step1Chunk0_2_checked, root4Node50Step1Chunk0_3_checked, root4Node50Step1Chunk0_4_checked, root4Node50Step1Chunk0_5_checked, root4Node50Step1Chunk1_0_checked, root4Node50Step1Chunk1_1_checked, root4Node50Step1Chunk1_2_checked, root4Node50Step1Chunk1_3_checked, root4Node50Step1Chunk1_4_checked, root4Node50Step1Chunk1_5_checked, root4Node50Step1Chunk2_0_checked, root4Node50Step1Chunk2_1_checked, root4Node50Step1Chunk2_2_checked, root4Node50Step1Chunk2_3_checked, root4Node50Step1Chunk2_4_checked, root4Node50Step1Chunk2_5_checked, root4Node50Step1Chunk3_0_checked, root4Node50Step1Chunk3_1_checked, root4Node50Step1Chunk3_2_checked, root4Node50Step1Chunk3_3_checked, root4Node50Step1Chunk3_4_checked, root4Node50Step1Chunk3_5_checked, root4Node50Step1Chunk4_0_checked, root4Node50Step1Chunk4_1_checked, root4Node50Step1Chunk4_2_checked, root4Node50Step1Chunk4_3_checked, root4Node50Step1Chunk4_4_checked, root4Node50Step1Chunk4_5_checked, root4Node50Step1Chunk5_0_checked, root4Node50Step1Chunk5_1_checked, root4Node50Step1Chunk5_2_checked, root4Node50Step1Chunk5_3_checked, root4Node50Step1Chunk5_4_checked, root4Node50Step1Chunk5_5_checked, root4Node50Step1Chunk6_0_checked, root4Node50Step1Chunk6_1_checked, root4Node50Step1Chunk6_2_checked, root4Node50Step1Chunk6_3_checked, root4Node50Step1Chunk6_4_checked, root4Node50Step1Chunk6_5_checked, root4Node50Step1Chunk7_0_checked, root4Node50Step1Chunk7_1_checked, root4Node50Step1Chunk7_2_checked, root4Node50Step1Chunk7_3_checked, root4Node50Step1Chunk7_4_checked, root4Node50Step1Chunk7_5_checked, root4Node50Step1Chunk8_0_checked, root4Node50Step1Chunk8_1_checked, root4Node50Step1Chunk8_2_checked, root4Node50Step1Chunk8_3_checked, root4Node50Step1Chunk8_4_checked, root4Node50Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node50Step1_checked :
    checkReplacement table13 root4Node50Domains0 root4Node50Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node50Domains0 root4Node50Domains1
    root4Node50Domains0Fast root4Node50Domains1Fast
    root4Node50Domains0_fast_eq root4Node50Domains1_fast_eq
    root4Node50Step1Narrowing_checked (by decide)
theorem root4Node50Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node50Domains1 (.output 23) = true := by decide
def root4Node51Domains0 : Domains 91 State := restrict root4Node49Domains1 30 (8,5)
def root4Node51Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(4,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(7,4)]
  | 30 => some [(8,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(6,5)]
  | 40 => some [(0,0),(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(6,3)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(1,1),(6,1)]
  | 52 => some [(4,1)]
  | 53 => some [(0,2)]
  | 54 => some [(1,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(7,3)]
  | 62 => some [(5,2)]
  | 63 => some [(8,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(6,2)]
  | 71 => some [(8,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(4,4)]
  | 75 => some [(0,0)]
  | 76 => some [(3,2)]
  | 77 => some [(4,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(7,1)]
  | 82 => some [(1,5)]
  | 83 => some [(6,1)]
  | 84 => some [(5,1)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(7,0)]
  | _ => some [(8,3)]
theorem root4Node51Domains0_fast_eq : root4Node51Domains0 = expandDomains root4Node51Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node51Domains0 v = expandDomains root4Node51Domains0Fast v from by decide) v
def root4Node51Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,4)]
  | 6 => [(4,5)]
  | 7 => [(1,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(6,0)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(0,0)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(7,4)]
  | 30 => [(8,5)]
  | 31 => [(7,0)]
  | 32 => [(8,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(8,1)]
  | 39 => [(6,5)]
  | 40 => [(6,3)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(6,3)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(7,0)]
  | 51 => [(1,1)]
  | 52 => [(4,1)]
  | 53 => [(0,2)]
  | 54 => [(1,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(7,3)]
  | 62 => [(5,2)]
  | 63 => [(8,0)]
  | 64 => [(8,3)]
  | 65 => [(5,5)]
  | 66 => [(1,0)]
  | 67 => [(2,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(6,2)]
  | 71 => [(8,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(4,4)]
  | 75 => [(0,0)]
  | 76 => [(3,2)]
  | 77 => [(4,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(7,1)]
  | 82 => [(1,5)]
  | 83 => [(6,1)]
  | 84 => [(5,1)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(7,0)]
  | _ => [(8,3)]
def root4Node51Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(4,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(7,4)]
  | 30 => some [(8,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(6,5)]
  | 40 => some [(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(6,3)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(1,1)]
  | 52 => some [(4,1)]
  | 53 => some [(0,2)]
  | 54 => some [(1,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(7,3)]
  | 62 => some [(5,2)]
  | 63 => some [(8,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(6,2)]
  | 71 => some [(8,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(4,4)]
  | 75 => some [(0,0)]
  | 76 => some [(3,2)]
  | 77 => some [(4,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(7,1)]
  | 82 => some [(1,5)]
  | 83 => some [(6,1)]
  | 84 => some [(5,1)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(7,0)]
  | _ => some [(8,3)]
theorem root4Node51Domains1_fast_eq : root4Node51Domains1 = expandDomains root4Node51Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node51Domains1 v = expandDomains root4Node51Domains1Fast v from by decide) v
theorem root4Node51Step1Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq (by decide)
theorem root4Node51Step1Narrowing_checked :
    checkNarrowing table13 root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkNarrowing_flatten table13Scope [table13Rows0_0,table13Rows0_1,table13Rows0_2,table13Rows0_3,table13Rows0_4,table13Rows0_5,table13Rows1_0,table13Rows1_1,table13Rows1_2,table13Rows1_3,table13Rows1_4,table13Rows1_5,table13Rows2_0,table13Rows2_1,table13Rows2_2,table13Rows2_3,table13Rows2_4,table13Rows2_5,table13Rows3_0,table13Rows3_1,table13Rows3_2,table13Rows3_3,table13Rows3_4,table13Rows3_5,table13Rows4_0,table13Rows4_1,table13Rows4_2,table13Rows4_3,table13Rows4_4,table13Rows4_5,table13Rows5_0,table13Rows5_1,table13Rows5_2,table13Rows5_3,table13Rows5_4,table13Rows5_5,table13Rows6_0,table13Rows6_1,table13Rows6_2,table13Rows6_3,table13Rows6_4,table13Rows6_5,table13Rows7_0,table13Rows7_1,table13Rows7_2,table13Rows7_3,table13Rows7_4,table13Rows7_5,table13Rows8_0,table13Rows8_1,table13Rows8_2,table13Rows8_3,table13Rows8_4,table13Rows8_5]
    root4Node51Domains0 root4Node51Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node51Step1Chunk0_0_checked, root4Node51Step1Chunk0_1_checked, root4Node51Step1Chunk0_2_checked, root4Node51Step1Chunk0_3_checked, root4Node51Step1Chunk0_4_checked, root4Node51Step1Chunk0_5_checked, root4Node51Step1Chunk1_0_checked, root4Node51Step1Chunk1_1_checked, root4Node51Step1Chunk1_2_checked, root4Node51Step1Chunk1_3_checked, root4Node51Step1Chunk1_4_checked, root4Node51Step1Chunk1_5_checked, root4Node51Step1Chunk2_0_checked, root4Node51Step1Chunk2_1_checked, root4Node51Step1Chunk2_2_checked, root4Node51Step1Chunk2_3_checked, root4Node51Step1Chunk2_4_checked, root4Node51Step1Chunk2_5_checked, root4Node51Step1Chunk3_0_checked, root4Node51Step1Chunk3_1_checked, root4Node51Step1Chunk3_2_checked, root4Node51Step1Chunk3_3_checked, root4Node51Step1Chunk3_4_checked, root4Node51Step1Chunk3_5_checked, root4Node51Step1Chunk4_0_checked, root4Node51Step1Chunk4_1_checked, root4Node51Step1Chunk4_2_checked, root4Node51Step1Chunk4_3_checked, root4Node51Step1Chunk4_4_checked, root4Node51Step1Chunk4_5_checked, root4Node51Step1Chunk5_0_checked, root4Node51Step1Chunk5_1_checked, root4Node51Step1Chunk5_2_checked, root4Node51Step1Chunk5_3_checked, root4Node51Step1Chunk5_4_checked, root4Node51Step1Chunk5_5_checked, root4Node51Step1Chunk6_0_checked, root4Node51Step1Chunk6_1_checked, root4Node51Step1Chunk6_2_checked, root4Node51Step1Chunk6_3_checked, root4Node51Step1Chunk6_4_checked, root4Node51Step1Chunk6_5_checked, root4Node51Step1Chunk7_0_checked, root4Node51Step1Chunk7_1_checked, root4Node51Step1Chunk7_2_checked, root4Node51Step1Chunk7_3_checked, root4Node51Step1Chunk7_4_checked, root4Node51Step1Chunk7_5_checked, root4Node51Step1Chunk8_0_checked, root4Node51Step1Chunk8_1_checked, root4Node51Step1Chunk8_2_checked, root4Node51Step1Chunk8_3_checked, root4Node51Step1Chunk8_4_checked, root4Node51Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node51Step1_checked :
    checkReplacement table13 root4Node51Domains0 root4Node51Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node51Domains0 root4Node51Domains1
    root4Node51Domains0Fast root4Node51Domains1Fast
    root4Node51Domains0_fast_eq root4Node51Domains1_fast_eq
    root4Node51Step1Narrowing_checked (by decide)
theorem root4Node51Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node51Domains1 (.output 24) = true := by decide
def root4Node52Domains0 : Domains 91 State := restrict root4Node48Domains1 20 (8,2)
def root4Node52Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(4,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(7,4),(8,4)]
  | 30 => some [(4,5),(8,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(1,5),(6,5)]
  | 40 => some [(0,0),(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(6,3)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(1,1),(6,1)]
  | 52 => some [(4,1)]
  | 53 => some [(0,2)]
  | 54 => some [(1,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(7,3)]
  | 62 => some [(5,2)]
  | 63 => some [(8,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(6,2)]
  | 71 => some [(8,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(4,4)]
  | 75 => some [(0,0)]
  | 76 => some [(3,2)]
  | 77 => some [(4,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(7,1)]
  | 82 => some [(1,5)]
  | 83 => some [(6,1)]
  | 84 => some [(5,1)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(7,0)]
  | _ => some [(8,3)]
theorem root4Node52Domains0_fast_eq : root4Node52Domains0 = expandDomains root4Node52Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node52Domains0 v = expandDomains root4Node52Domains0Fast v from by decide) v
def root4Node52Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,4)]
  | 6 => [(4,5)]
  | 7 => [(1,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(6,0)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(0,0)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(8,4)]
  | 30 => [(4,5),(8,5)]
  | 31 => [(7,0)]
  | 32 => [(8,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(8,1)]
  | 39 => [(1,5)]
  | 40 => [(0,0),(6,3)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(6,3)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(7,0)]
  | 51 => [(1,1),(6,1)]
  | 52 => [(4,1)]
  | 53 => [(0,2)]
  | 54 => [(1,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(7,3)]
  | 62 => [(5,2)]
  | 63 => [(8,0)]
  | 64 => [(8,3)]
  | 65 => [(5,5)]
  | 66 => [(1,0)]
  | 67 => [(2,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(6,2)]
  | 71 => [(8,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(4,4)]
  | 75 => [(0,0)]
  | 76 => [(3,2)]
  | 77 => [(4,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(7,1)]
  | 82 => [(1,5)]
  | 83 => [(6,1)]
  | 84 => [(5,1)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(7,0)]
  | _ => [(8,3)]
def root4Node52Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(4,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(4,5),(8,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(1,5)]
  | 40 => some [(0,0),(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(6,3)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(1,1),(6,1)]
  | 52 => some [(4,1)]
  | 53 => some [(0,2)]
  | 54 => some [(1,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(7,3)]
  | 62 => some [(5,2)]
  | 63 => some [(8,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(6,2)]
  | 71 => some [(8,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(4,4)]
  | 75 => some [(0,0)]
  | 76 => some [(3,2)]
  | 77 => some [(4,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(7,1)]
  | 82 => some [(1,5)]
  | 83 => some [(6,1)]
  | 84 => some [(5,1)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(7,0)]
  | _ => some [(8,3)]
theorem root4Node52Domains1_fast_eq : root4Node52Domains1 = expandDomains root4Node52Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node52Domains1 v = expandDomains root4Node52Domains1Fast v from by decide) v
theorem root4Node52Step1Chunk0_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_0⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk0_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_1⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk0_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_2⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk0_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_3⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk0_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_4⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk0_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_5⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk1_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_0⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk1_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_1⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk1_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_2⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk1_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_3⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk1_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_4⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk1_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_5⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk2_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_0⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk2_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_1⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk2_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_2⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk2_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_3⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk2_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_4⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk2_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_5⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk3_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_0⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk3_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_1⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk3_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_2⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk3_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_3⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk3_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_4⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk3_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_5⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk4_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_0⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk4_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_1⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk4_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_2⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk4_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_3⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk4_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_4⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk4_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_5⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk5_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_0⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk5_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_1⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk5_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_2⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk5_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_3⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk5_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_4⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk5_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_5⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk6_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_0⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk6_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_1⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk6_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_2⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk6_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_3⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk6_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_4⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk6_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_5⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk7_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_0⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk7_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_1⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk7_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_2⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk7_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_3⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk7_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_4⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk7_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_5⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk8_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_0⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk8_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_1⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk8_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_2⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk8_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_3⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk8_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_4⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Chunk8_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_5⟩
      root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq (by decide)
theorem root4Node52Step1Narrowing_checked :
    checkNarrowing table5 root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkNarrowing_flatten table5Scope [table5Rows0_0,table5Rows0_1,table5Rows0_2,table5Rows0_3,table5Rows0_4,table5Rows0_5,table5Rows1_0,table5Rows1_1,table5Rows1_2,table5Rows1_3,table5Rows1_4,table5Rows1_5,table5Rows2_0,table5Rows2_1,table5Rows2_2,table5Rows2_3,table5Rows2_4,table5Rows2_5,table5Rows3_0,table5Rows3_1,table5Rows3_2,table5Rows3_3,table5Rows3_4,table5Rows3_5,table5Rows4_0,table5Rows4_1,table5Rows4_2,table5Rows4_3,table5Rows4_4,table5Rows4_5,table5Rows5_0,table5Rows5_1,table5Rows5_2,table5Rows5_3,table5Rows5_4,table5Rows5_5,table5Rows6_0,table5Rows6_1,table5Rows6_2,table5Rows6_3,table5Rows6_4,table5Rows6_5,table5Rows7_0,table5Rows7_1,table5Rows7_2,table5Rows7_3,table5Rows7_4,table5Rows7_5,table5Rows8_0,table5Rows8_1,table5Rows8_2,table5Rows8_3,table5Rows8_4,table5Rows8_5]
    root4Node52Domains0 root4Node52Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node52Step1Chunk0_0_checked, root4Node52Step1Chunk0_1_checked, root4Node52Step1Chunk0_2_checked, root4Node52Step1Chunk0_3_checked, root4Node52Step1Chunk0_4_checked, root4Node52Step1Chunk0_5_checked, root4Node52Step1Chunk1_0_checked, root4Node52Step1Chunk1_1_checked, root4Node52Step1Chunk1_2_checked, root4Node52Step1Chunk1_3_checked, root4Node52Step1Chunk1_4_checked, root4Node52Step1Chunk1_5_checked, root4Node52Step1Chunk2_0_checked, root4Node52Step1Chunk2_1_checked, root4Node52Step1Chunk2_2_checked, root4Node52Step1Chunk2_3_checked, root4Node52Step1Chunk2_4_checked, root4Node52Step1Chunk2_5_checked, root4Node52Step1Chunk3_0_checked, root4Node52Step1Chunk3_1_checked, root4Node52Step1Chunk3_2_checked, root4Node52Step1Chunk3_3_checked, root4Node52Step1Chunk3_4_checked, root4Node52Step1Chunk3_5_checked, root4Node52Step1Chunk4_0_checked, root4Node52Step1Chunk4_1_checked, root4Node52Step1Chunk4_2_checked, root4Node52Step1Chunk4_3_checked, root4Node52Step1Chunk4_4_checked, root4Node52Step1Chunk4_5_checked, root4Node52Step1Chunk5_0_checked, root4Node52Step1Chunk5_1_checked, root4Node52Step1Chunk5_2_checked, root4Node52Step1Chunk5_3_checked, root4Node52Step1Chunk5_4_checked, root4Node52Step1Chunk5_5_checked, root4Node52Step1Chunk6_0_checked, root4Node52Step1Chunk6_1_checked, root4Node52Step1Chunk6_2_checked, root4Node52Step1Chunk6_3_checked, root4Node52Step1Chunk6_4_checked, root4Node52Step1Chunk6_5_checked, root4Node52Step1Chunk7_0_checked, root4Node52Step1Chunk7_1_checked, root4Node52Step1Chunk7_2_checked, root4Node52Step1Chunk7_3_checked, root4Node52Step1Chunk7_4_checked, root4Node52Step1Chunk7_5_checked, root4Node52Step1Chunk8_0_checked, root4Node52Step1Chunk8_1_checked, root4Node52Step1Chunk8_2_checked, root4Node52Step1Chunk8_3_checked, root4Node52Step1Chunk8_4_checked, root4Node52Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node52Step1_checked :
    checkReplacement table5 root4Node52Domains0 root4Node52Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node52Domains0 root4Node52Domains1
    root4Node52Domains0Fast root4Node52Domains1Fast
    root4Node52Domains0_fast_eq root4Node52Domains1_fast_eq
    root4Node52Step1Narrowing_checked (by decide)
def root4Node53Domains0 : Domains 91 State := restrict root4Node52Domains1 30 (4,5)
def root4Node53Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(4,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(1,5)]
  | 40 => some [(0,0),(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(6,3)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(1,1),(6,1)]
  | 52 => some [(4,1)]
  | 53 => some [(0,2)]
  | 54 => some [(1,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(7,3)]
  | 62 => some [(5,2)]
  | 63 => some [(8,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(6,2)]
  | 71 => some [(8,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(4,4)]
  | 75 => some [(0,0)]
  | 76 => some [(3,2)]
  | 77 => some [(4,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(7,1)]
  | 82 => some [(1,5)]
  | 83 => some [(6,1)]
  | 84 => some [(5,1)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(7,0)]
  | _ => some [(8,3)]
theorem root4Node53Domains0_fast_eq : root4Node53Domains0 = expandDomains root4Node53Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node53Domains0 v = expandDomains root4Node53Domains0Fast v from by decide) v
def root4Node53Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,4)]
  | 6 => [(4,5)]
  | 7 => [(1,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(6,0)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(0,0)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(8,4)]
  | 30 => [(4,5)]
  | 31 => [(7,0)]
  | 32 => [(8,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(8,1)]
  | 39 => [(1,5)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(6,3)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(7,0)]
  | 51 => [(6,1)]
  | 52 => [(4,1)]
  | 53 => [(0,2)]
  | 54 => [(1,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(7,3)]
  | 62 => [(5,2)]
  | 63 => [(8,0)]
  | 64 => [(8,3)]
  | 65 => [(5,5)]
  | 66 => [(1,0)]
  | 67 => [(2,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(6,2)]
  | 71 => [(8,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(4,4)]
  | 75 => [(0,0)]
  | 76 => [(3,2)]
  | 77 => [(4,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(7,1)]
  | 82 => [(1,5)]
  | 83 => [(6,1)]
  | 84 => [(5,1)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(7,0)]
  | _ => [(8,3)]
def root4Node53Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(4,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(1,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(6,3)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(4,1)]
  | 53 => some [(0,2)]
  | 54 => some [(1,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(7,3)]
  | 62 => some [(5,2)]
  | 63 => some [(8,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(6,2)]
  | 71 => some [(8,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(4,4)]
  | 75 => some [(0,0)]
  | 76 => some [(3,2)]
  | 77 => some [(4,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(7,1)]
  | 82 => some [(1,5)]
  | 83 => some [(6,1)]
  | 84 => some [(5,1)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(7,0)]
  | _ => some [(8,3)]
theorem root4Node53Domains1_fast_eq : root4Node53Domains1 = expandDomains root4Node53Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node53Domains1 v = expandDomains root4Node53Domains1Fast v from by decide) v
theorem root4Node53Step1Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq (by decide)
theorem root4Node53Step1Narrowing_checked :
    checkNarrowing table13 root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkNarrowing_flatten table13Scope [table13Rows0_0,table13Rows0_1,table13Rows0_2,table13Rows0_3,table13Rows0_4,table13Rows0_5,table13Rows1_0,table13Rows1_1,table13Rows1_2,table13Rows1_3,table13Rows1_4,table13Rows1_5,table13Rows2_0,table13Rows2_1,table13Rows2_2,table13Rows2_3,table13Rows2_4,table13Rows2_5,table13Rows3_0,table13Rows3_1,table13Rows3_2,table13Rows3_3,table13Rows3_4,table13Rows3_5,table13Rows4_0,table13Rows4_1,table13Rows4_2,table13Rows4_3,table13Rows4_4,table13Rows4_5,table13Rows5_0,table13Rows5_1,table13Rows5_2,table13Rows5_3,table13Rows5_4,table13Rows5_5,table13Rows6_0,table13Rows6_1,table13Rows6_2,table13Rows6_3,table13Rows6_4,table13Rows6_5,table13Rows7_0,table13Rows7_1,table13Rows7_2,table13Rows7_3,table13Rows7_4,table13Rows7_5,table13Rows8_0,table13Rows8_1,table13Rows8_2,table13Rows8_3,table13Rows8_4,table13Rows8_5]
    root4Node53Domains0 root4Node53Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node53Step1Chunk0_0_checked, root4Node53Step1Chunk0_1_checked, root4Node53Step1Chunk0_2_checked, root4Node53Step1Chunk0_3_checked, root4Node53Step1Chunk0_4_checked, root4Node53Step1Chunk0_5_checked, root4Node53Step1Chunk1_0_checked, root4Node53Step1Chunk1_1_checked, root4Node53Step1Chunk1_2_checked, root4Node53Step1Chunk1_3_checked, root4Node53Step1Chunk1_4_checked, root4Node53Step1Chunk1_5_checked, root4Node53Step1Chunk2_0_checked, root4Node53Step1Chunk2_1_checked, root4Node53Step1Chunk2_2_checked, root4Node53Step1Chunk2_3_checked, root4Node53Step1Chunk2_4_checked, root4Node53Step1Chunk2_5_checked, root4Node53Step1Chunk3_0_checked, root4Node53Step1Chunk3_1_checked, root4Node53Step1Chunk3_2_checked, root4Node53Step1Chunk3_3_checked, root4Node53Step1Chunk3_4_checked, root4Node53Step1Chunk3_5_checked, root4Node53Step1Chunk4_0_checked, root4Node53Step1Chunk4_1_checked, root4Node53Step1Chunk4_2_checked, root4Node53Step1Chunk4_3_checked, root4Node53Step1Chunk4_4_checked, root4Node53Step1Chunk4_5_checked, root4Node53Step1Chunk5_0_checked, root4Node53Step1Chunk5_1_checked, root4Node53Step1Chunk5_2_checked, root4Node53Step1Chunk5_3_checked, root4Node53Step1Chunk5_4_checked, root4Node53Step1Chunk5_5_checked, root4Node53Step1Chunk6_0_checked, root4Node53Step1Chunk6_1_checked, root4Node53Step1Chunk6_2_checked, root4Node53Step1Chunk6_3_checked, root4Node53Step1Chunk6_4_checked, root4Node53Step1Chunk6_5_checked, root4Node53Step1Chunk7_0_checked, root4Node53Step1Chunk7_1_checked, root4Node53Step1Chunk7_2_checked, root4Node53Step1Chunk7_3_checked, root4Node53Step1Chunk7_4_checked, root4Node53Step1Chunk7_5_checked, root4Node53Step1Chunk8_0_checked, root4Node53Step1Chunk8_1_checked, root4Node53Step1Chunk8_2_checked, root4Node53Step1Chunk8_3_checked, root4Node53Step1Chunk8_4_checked, root4Node53Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node53Step1_checked :
    checkReplacement table13 root4Node53Domains0 root4Node53Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node53Domains0 root4Node53Domains1
    root4Node53Domains0Fast root4Node53Domains1Fast
    root4Node53Domains0_fast_eq root4Node53Domains1_fast_eq
    root4Node53Step1Narrowing_checked (by decide)
theorem root4Node53Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node53Domains1 (.output 25) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
