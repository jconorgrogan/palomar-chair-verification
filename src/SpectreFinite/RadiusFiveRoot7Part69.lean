module

public import SpectreFinite.RadiusFiveRoot7Part68
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable1
public import SpectreFinite.RadiusFiveTable33
public import SpectreFinite.RadiusFiveTable51
public import SpectreFinite.RadiusFiveTable53

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node177Domains0 : Domains 91 State := restrict root7Node175Domains1 40 (3,3)
def root7Node177Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,3)]
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(7,4)]
  | 40 => some [(3,3)]
  | 41 => some [(5,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(3,5)]
  | 48 => some [(0,3)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,4),(6,2)]
  | 52 => some [(5,4),(8,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(2,4)]
  | 59 => some [(1,3)]
  | 60 => some [(5,2)]
  | 61 => some [(4,3),(7,1)]
  | 62 => some [(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(7,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4),(6,2)]
  | 79 => some [(5,4),(8,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3)]
  | 88 => some [(8,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root7Node177Domains0_fast_eq : root7Node177Domains0 = expandDomains root7Node177Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node177Domains0 v = expandDomains root7Node177Domains0Fast v from by decide) v
def root7Node177Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(8,2)]
  | 6 => [(8,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(5,1)]
  | 10 => [(0,1)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(5,3)]
  | 14 => [(8,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(7,4)]
  | 22 => [(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(4,2)]
  | 30 => [(4,1)]
  | 31 => [(0,2)]
  | 32 => [(1,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(7,4)]
  | 40 => [(3,3)]
  | 41 => [(5,2)]
  | 42 => [(8,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(3,5)]
  | 48 => [(0,3)]
  | 49 => [(4,1)]
  | 50 => [(0,2)]
  | 51 => [(6,2)]
  | 52 => [(8,4)]
  | 53 => [(1,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(1,4)]
  | 57 => [(0,5)]
  | 58 => [(2,4)]
  | 59 => [(1,3)]
  | 60 => [(5,2)]
  | 61 => [(7,1)]
  | 62 => [(7,5)]
  | 63 => [(6,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(6,0)]
  | 67 => [(7,1)]
  | 68 => [(6,5)]
  | 69 => [(0,4)]
  | 70 => [(7,3)]
  | 71 => [(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3)]
  | 74 => [(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(7,0)]
  | 78 => [(6,2)]
  | 79 => [(8,4)]
  | 80 => [(6,4)]
  | 81 => [(1,2)]
  | 82 => [(8,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(0,3)]
  | 88 => [(8,1)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root7Node177Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,3)]
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(7,4)]
  | 40 => some [(3,3)]
  | 41 => some [(5,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(3,5)]
  | 48 => some [(0,3)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(6,2)]
  | 52 => some [(8,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(2,4)]
  | 59 => some [(1,3)]
  | 60 => some [(5,2)]
  | 61 => some [(7,1)]
  | 62 => some [(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(7,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(7,3)]
  | 71 => some [(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(7,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3)]
  | 88 => some [(8,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root7Node177Domains1_fast_eq : root7Node177Domains1 = expandDomains root7Node177Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node177Domains1 v = expandDomains root7Node177Domains1Fast v from by decide) v
theorem root7Node177Step1Chunk0_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_0⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk0_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_1⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk0_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_2⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk0_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_3⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk0_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_4⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk0_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_5⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk1_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_0⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk1_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_1⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk1_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_2⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk1_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_3⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk1_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_4⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk1_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_5⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk2_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_0⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk2_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_1⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk2_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_2⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk2_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_3⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk2_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_4⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk2_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_5⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk3_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_0⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk3_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_1⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk3_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_2⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk3_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_3⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk3_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_4⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk3_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_5⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk4_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_0⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk4_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_1⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk4_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_2⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk4_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_3⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk4_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_4⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk4_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_5⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk5_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_0⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk5_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_1⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk5_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_2⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk5_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_3⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk5_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_4⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk5_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_5⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk6_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_0⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk6_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_1⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk6_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_2⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk6_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_3⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk6_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_4⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk6_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_5⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk7_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_0⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk7_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_1⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk7_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_2⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk7_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_3⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk7_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_4⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk7_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_5⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk8_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_0⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk8_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_1⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk8_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_2⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk8_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_3⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk8_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_4⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Chunk8_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_5⟩
      root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq (by decide)
theorem root7Node177Step1Narrowing_checked :
    checkNarrowing table51 root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkNarrowing_flatten table51Scope [table51Rows0_0,table51Rows0_1,table51Rows0_2,table51Rows0_3,table51Rows0_4,table51Rows0_5,table51Rows1_0,table51Rows1_1,table51Rows1_2,table51Rows1_3,table51Rows1_4,table51Rows1_5,table51Rows2_0,table51Rows2_1,table51Rows2_2,table51Rows2_3,table51Rows2_4,table51Rows2_5,table51Rows3_0,table51Rows3_1,table51Rows3_2,table51Rows3_3,table51Rows3_4,table51Rows3_5,table51Rows4_0,table51Rows4_1,table51Rows4_2,table51Rows4_3,table51Rows4_4,table51Rows4_5,table51Rows5_0,table51Rows5_1,table51Rows5_2,table51Rows5_3,table51Rows5_4,table51Rows5_5,table51Rows6_0,table51Rows6_1,table51Rows6_2,table51Rows6_3,table51Rows6_4,table51Rows6_5,table51Rows7_0,table51Rows7_1,table51Rows7_2,table51Rows7_3,table51Rows7_4,table51Rows7_5,table51Rows8_0,table51Rows8_1,table51Rows8_2,table51Rows8_3,table51Rows8_4,table51Rows8_5]
    root7Node177Domains0 root7Node177Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node177Step1Chunk0_0_checked, root7Node177Step1Chunk0_1_checked, root7Node177Step1Chunk0_2_checked, root7Node177Step1Chunk0_3_checked, root7Node177Step1Chunk0_4_checked, root7Node177Step1Chunk0_5_checked, root7Node177Step1Chunk1_0_checked, root7Node177Step1Chunk1_1_checked, root7Node177Step1Chunk1_2_checked, root7Node177Step1Chunk1_3_checked, root7Node177Step1Chunk1_4_checked, root7Node177Step1Chunk1_5_checked, root7Node177Step1Chunk2_0_checked, root7Node177Step1Chunk2_1_checked, root7Node177Step1Chunk2_2_checked, root7Node177Step1Chunk2_3_checked, root7Node177Step1Chunk2_4_checked, root7Node177Step1Chunk2_5_checked, root7Node177Step1Chunk3_0_checked, root7Node177Step1Chunk3_1_checked, root7Node177Step1Chunk3_2_checked, root7Node177Step1Chunk3_3_checked, root7Node177Step1Chunk3_4_checked, root7Node177Step1Chunk3_5_checked, root7Node177Step1Chunk4_0_checked, root7Node177Step1Chunk4_1_checked, root7Node177Step1Chunk4_2_checked, root7Node177Step1Chunk4_3_checked, root7Node177Step1Chunk4_4_checked, root7Node177Step1Chunk4_5_checked, root7Node177Step1Chunk5_0_checked, root7Node177Step1Chunk5_1_checked, root7Node177Step1Chunk5_2_checked, root7Node177Step1Chunk5_3_checked, root7Node177Step1Chunk5_4_checked, root7Node177Step1Chunk5_5_checked, root7Node177Step1Chunk6_0_checked, root7Node177Step1Chunk6_1_checked, root7Node177Step1Chunk6_2_checked, root7Node177Step1Chunk6_3_checked, root7Node177Step1Chunk6_4_checked, root7Node177Step1Chunk6_5_checked, root7Node177Step1Chunk7_0_checked, root7Node177Step1Chunk7_1_checked, root7Node177Step1Chunk7_2_checked, root7Node177Step1Chunk7_3_checked, root7Node177Step1Chunk7_4_checked, root7Node177Step1Chunk7_5_checked, root7Node177Step1Chunk8_0_checked, root7Node177Step1Chunk8_1_checked, root7Node177Step1Chunk8_2_checked, root7Node177Step1Chunk8_3_checked, root7Node177Step1Chunk8_4_checked, root7Node177Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node177Step1_checked :
    checkReplacement table51 root7Node177Domains0 root7Node177Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node177Domains0 root7Node177Domains1
    root7Node177Domains0Fast root7Node177Domains1Fast
    root7Node177Domains0_fast_eq root7Node177Domains1_fast_eq
    root7Node177Step1Narrowing_checked (by decide)
theorem root7Node177Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node177Domains1 (.output 88) = true := by decide
def root7Node178Domains0 : Domains 91 State := restrict root7Node128Domains4 3 (8,0)
def root7Node178Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4),(4,4),(7,4),(8,4)]
  | 1 => some [(0,0),(1,3),(6,4)]
  | 2 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3),(8,3)]
  | 5 => some [(4,2),(5,2),(5,5),(8,2)]
  | 6 => some [(7,1),(8,1)]
  | 7 => some [(1,5),(6,5),(7,5)]
  | 8 => some [(0,3),(0,4),(6,1)]
  | 9 => some [(5,1),(5,4)]
  | 10 => some [(0,1),(1,4),(6,4)]
  | 11 => some [(0,5),(1,2),(6,2)]
  | 12 => some [(4,4),(7,4),(8,4)]
  | 13 => some [(5,0),(5,3),(8,0),(8,3)]
  | 14 => some [(4,5),(7,3),(8,5)]
  | 15 => some [(4,2),(7,0)]
  | 16 => some [(4,3),(5,3),(8,3)]
  | 17 => some [(7,5),(8,5)]
  | 18 => some [(0,3),(1,0),(6,0)]
  | 19 => some [(7,1),(8,1)]
  | 20 => some [(1,5),(6,5),(7,5)]
  | 21 => some [(5,4),(7,4),(8,4)]
  | 22 => some [(0,0),(6,3),(6,4)]
  | 23 => some [(1,2),(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2),(8,2)]
  | 27 => some [(5,0),(5,3),(8,0)]
  | 28 => some [(4,5),(7,3),(8,5)]
  | 29 => some [(4,2),(7,0),(8,2)]
  | 30 => some [(4,1),(4,3),(7,1),(8,1)]
  | 31 => some [(0,2),(1,5),(7,5)]
  | 32 => some [(0,3),(1,1),(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(3,4),(5,4)]
  | 37 => some [(0,0),(6,3),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4),(8,4)]
  | 40 => some [(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(7,4),(8,0)]
  | 41 => some [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 42 => some [(4,2),(7,0),(8,0)]
  | 43 => some [(5,3),(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(2,3),(4,3)]
  | 47 => some [(0,2),(1,5),(3,5),(7,5)]
  | 48 => some [(0,3),(1,1),(6,1)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(1,5),(6,5)]
  | 51 => some [(0,0),(0,1),(0,4),(0,5),(6,2),(6,3),(6,4),(6,5)]
  | 52 => some [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 53 => some [(1,4),(3,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(6,4),(7,4)]
  | 57 => some [(0,5),(1,2),(1,3),(6,3)]
  | 58 => some [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 59 => some [(1,3),(3,3),(5,3),(7,3)]
  | 60 => some [(5,2),(5,5),(8,5)]
  | 61 => some [(0,3),(1,0),(1,1),(3,0),(4,3),(6,1),(7,0),(7,1)]
  | 62 => some [(2,1),(2,3),(2,5),(4,1),(7,5)]
  | 63 => some [(0,2),(6,0)]
  | 64 => some [(1,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(0,3),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 68 => some [(0,1),(1,4),(3,4),(6,5)]
  | 69 => some [(0,4),(0,5),(6,2),(6,3)]
  | 70 => some [(0,0),(1,3),(3,3),(6,4),(7,3)]
  | 71 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(4,2),(5,2),(5,5),(8,2)]
  | 75 => some [(3,0),(5,0),(5,3),(7,0)]
  | 76 => some [(2,3),(2,5),(4,5),(8,5)]
  | 77 => some [(0,2),(1,0),(6,0),(7,0)]
  | 78 => some [(0,3),(0,4),(6,1),(6,2)]
  | 79 => some [(5,1),(5,4),(8,4)]
  | 80 => some [(0,1),(1,4),(6,4)]
  | 81 => some [(0,5),(1,2),(6,2)]
  | 82 => some [(4,4),(7,4),(8,4)]
  | 83 => some [(0,0),(1,3),(6,3),(6,4)]
  | 84 => some [(1,2),(7,2),(8,2)]
  | 85 => some [(4,3),(5,3),(7,1),(8,3)]
  | 86 => some [(3,5),(7,5),(8,5)]
  | 87 => some [(0,3),(1,0),(6,0)]
  | 88 => some [(4,1),(7,1),(8,1)]
  | 89 => some [(0,2),(1,5),(6,5),(7,5)]
  | _ => some [(0,3),(0,4),(1,1),(6,1)]
theorem root7Node178Domains0_fast_eq : root7Node178Domains0 = expandDomains root7Node178Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node178Domains0 v = expandDomains root7Node178Domains0Fast v from by decide) v
def root7Node178Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,4),(7,4)]
  | 1 => [(1,3)]
  | 2 => [(5,2),(8,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3),(8,3)]
  | 5 => [(4,2),(5,2),(5,5),(8,2)]
  | 6 => [(7,1),(8,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(1,4),(6,4)]
  | 11 => [(0,5),(1,2),(6,2)]
  | 12 => [(4,4),(7,4),(8,4)]
  | 13 => [(5,0),(5,3),(8,3)]
  | 14 => [(4,5),(8,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(0,3),(6,0)]
  | 19 => [(7,1),(8,1)]
  | 20 => [(1,5),(6,5),(7,5)]
  | 21 => [(7,4),(8,4)]
  | 22 => [(0,0),(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(4,2),(8,2)]
  | 27 => [(5,0),(5,3),(8,0)]
  | 28 => [(4,5),(7,3),(8,5)]
  | 29 => [(4,2),(7,0),(8,2)]
  | 30 => [(4,1),(7,1),(8,1)]
  | 31 => [(0,2),(1,5)]
  | 32 => [(1,1),(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(3,4),(5,4)]
  | 37 => [(0,0),(6,3),(6,4)]
  | 38 => [(1,2),(7,2)]
  | 39 => [(7,4),(8,4)]
  | 40 => [(1,3),(3,3),(5,0),(5,3),(7,3)]
  | 41 => [(4,5),(5,2),(5,5),(8,5)]
  | 42 => [(7,0),(8,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5),(8,5)]
  | 45 => [(7,0)]
  | 46 => [(2,3),(4,3)]
  | 47 => [(0,2),(1,5),(3,5),(7,5)]
  | 48 => [(0,3),(1,1),(6,1)]
  | 49 => [(4,1),(8,1)]
  | 50 => [(0,2),(1,5),(6,5)]
  | 51 => [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 52 => [(4,4),(5,4),(7,2),(8,4)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,4),(6,4),(7,4)]
  | 57 => [(0,5),(1,2),(1,3),(6,3)]
  | 58 => [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 59 => [(1,3),(3,3),(5,3),(7,3)]
  | 60 => [(5,2),(5,5),(8,5)]
  | 61 => [(1,1),(4,3),(6,1),(7,1)]
  | 62 => [(4,1),(7,5)]
  | 63 => [(0,2),(6,0)]
  | 64 => [(1,1),(7,1)]
  | 65 => [(4,1),(7,5),(8,1)]
  | 66 => [(0,2),(0,3),(6,0),(6,5)]
  | 67 => [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 68 => [(0,1),(1,4),(3,4),(6,5)]
  | 69 => [(0,4),(0,5),(6,2),(6,3)]
  | 70 => [(1,3),(7,3)]
  | 71 => [(5,2),(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(4,2),(5,2),(5,5),(8,2)]
  | 75 => [(3,0),(5,0),(5,3),(7,0)]
  | 76 => [(2,3),(2,5),(4,5),(8,5)]
  | 77 => [(0,2),(1,0),(6,0),(7,0)]
  | 78 => [(0,3),(0,4),(6,1),(6,2)]
  | 79 => [(5,1),(5,4),(8,4)]
  | 80 => [(0,1),(1,4),(6,4)]
  | 81 => [(0,5),(1,2),(6,2)]
  | 82 => [(4,4),(7,4),(8,4)]
  | 83 => [(0,0),(1,3),(6,3),(6,4)]
  | 84 => [(1,2),(7,2),(8,2)]
  | 85 => [(4,3),(5,3),(7,1),(8,3)]
  | 86 => [(3,5),(7,5),(8,5)]
  | 87 => [(0,3),(1,0),(6,0)]
  | 88 => [(4,1),(7,1),(8,1)]
  | 89 => [(0,2),(1,5),(6,5),(7,5)]
  | _ => [(0,3),(0,4),(1,1),(6,1)]
def root7Node178Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4),(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2),(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3),(8,3)]
  | 5 => some [(4,2),(5,2),(5,5),(8,2)]
  | 6 => some [(7,1),(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(1,4),(6,4)]
  | 11 => some [(0,5),(1,2),(6,2)]
  | 12 => some [(4,4),(7,4),(8,4)]
  | 13 => some [(5,0),(5,3),(8,3)]
  | 14 => some [(4,5),(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3),(6,0)]
  | 19 => some [(7,1),(8,1)]
  | 20 => some [(1,5),(6,5),(7,5)]
  | 21 => some [(7,4),(8,4)]
  | 22 => some [(0,0),(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2),(8,2)]
  | 27 => some [(5,0),(5,3),(8,0)]
  | 28 => some [(4,5),(7,3),(8,5)]
  | 29 => some [(4,2),(7,0),(8,2)]
  | 30 => some [(4,1),(7,1),(8,1)]
  | 31 => some [(0,2),(1,5)]
  | 32 => some [(1,1),(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(3,4),(5,4)]
  | 37 => some [(0,0),(6,3),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4),(8,4)]
  | 40 => some [(1,3),(3,3),(5,0),(5,3),(7,3)]
  | 41 => some [(4,5),(5,2),(5,5),(8,5)]
  | 42 => some [(7,0),(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(2,3),(4,3)]
  | 47 => some [(0,2),(1,5),(3,5),(7,5)]
  | 48 => some [(0,3),(1,1),(6,1)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(1,5),(6,5)]
  | 51 => some [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 52 => some [(4,4),(5,4),(7,2),(8,4)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(6,4),(7,4)]
  | 57 => some [(0,5),(1,2),(1,3),(6,3)]
  | 58 => some [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 59 => some [(1,3),(3,3),(5,3),(7,3)]
  | 60 => some [(5,2),(5,5),(8,5)]
  | 61 => some [(1,1),(4,3),(6,1),(7,1)]
  | 62 => some [(4,1),(7,5)]
  | 63 => some [(0,2),(6,0)]
  | 64 => some [(1,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(0,3),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 68 => some [(0,1),(1,4),(3,4),(6,5)]
  | 69 => some [(0,4),(0,5),(6,2),(6,3)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(5,2),(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(4,2),(5,2),(5,5),(8,2)]
  | 75 => some [(3,0),(5,0),(5,3),(7,0)]
  | 76 => some [(2,3),(2,5),(4,5),(8,5)]
  | 77 => some [(0,2),(1,0),(6,0),(7,0)]
  | 78 => some [(0,3),(0,4),(6,1),(6,2)]
  | 79 => some [(5,1),(5,4),(8,4)]
  | 80 => some [(0,1),(1,4),(6,4)]
  | 81 => some [(0,5),(1,2),(6,2)]
  | 82 => some [(4,4),(7,4),(8,4)]
  | 83 => some [(0,0),(1,3),(6,3),(6,4)]
  | 84 => some [(1,2),(7,2),(8,2)]
  | 85 => some [(4,3),(5,3),(7,1),(8,3)]
  | 86 => some [(3,5),(7,5),(8,5)]
  | 87 => some [(0,3),(1,0),(6,0)]
  | 88 => some [(4,1),(7,1),(8,1)]
  | 89 => some [(0,2),(1,5),(6,5),(7,5)]
  | _ => some [(0,3),(0,4),(1,1),(6,1)]
theorem root7Node178Domains1_fast_eq : root7Node178Domains1 = expandDomains root7Node178Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node178Domains1 v = expandDomains root7Node178Domains1Fast v from by decide) v
theorem root7Node178Step1Chunk0_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_0⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk0_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_1⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk0_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_2⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk0_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_3⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk0_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_4⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk0_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_5⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk1_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_0⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk1_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_1⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk1_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_2⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk1_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_3⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk1_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_4⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk1_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_5⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk2_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_0⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk2_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_1⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk2_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_2⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk2_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_3⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk2_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_4⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk2_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_5⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk3_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_0⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk3_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_1⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk3_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_2⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk3_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_3⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk3_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_4⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk3_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_5⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk4_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_0⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk4_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_1⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk4_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_2⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk4_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_3⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk4_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_4⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk4_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_5⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk5_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_0⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk5_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_1⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk5_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_2⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk5_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_3⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk5_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_4⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk5_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_5⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk6_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_0⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk6_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_1⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk6_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_2⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk6_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_3⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk6_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_4⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk6_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_5⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk7_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_0⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk7_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_1⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk7_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_2⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk7_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_3⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk7_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_4⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk7_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_5⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk8_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_0⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk8_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_1⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk8_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_2⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk8_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_3⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk8_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_4⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Chunk8_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_5⟩
      root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq (by decide)
theorem root7Node178Step1Narrowing_checked :
    checkNarrowing table33 root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkNarrowing_flatten table33Scope [table33Rows0_0,table33Rows0_1,table33Rows0_2,table33Rows0_3,table33Rows0_4,table33Rows0_5,table33Rows1_0,table33Rows1_1,table33Rows1_2,table33Rows1_3,table33Rows1_4,table33Rows1_5,table33Rows2_0,table33Rows2_1,table33Rows2_2,table33Rows2_3,table33Rows2_4,table33Rows2_5,table33Rows3_0,table33Rows3_1,table33Rows3_2,table33Rows3_3,table33Rows3_4,table33Rows3_5,table33Rows4_0,table33Rows4_1,table33Rows4_2,table33Rows4_3,table33Rows4_4,table33Rows4_5,table33Rows5_0,table33Rows5_1,table33Rows5_2,table33Rows5_3,table33Rows5_4,table33Rows5_5,table33Rows6_0,table33Rows6_1,table33Rows6_2,table33Rows6_3,table33Rows6_4,table33Rows6_5,table33Rows7_0,table33Rows7_1,table33Rows7_2,table33Rows7_3,table33Rows7_4,table33Rows7_5,table33Rows8_0,table33Rows8_1,table33Rows8_2,table33Rows8_3,table33Rows8_4,table33Rows8_5]
    root7Node178Domains0 root7Node178Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node178Step1Chunk0_0_checked, root7Node178Step1Chunk0_1_checked, root7Node178Step1Chunk0_2_checked, root7Node178Step1Chunk0_3_checked, root7Node178Step1Chunk0_4_checked, root7Node178Step1Chunk0_5_checked, root7Node178Step1Chunk1_0_checked, root7Node178Step1Chunk1_1_checked, root7Node178Step1Chunk1_2_checked, root7Node178Step1Chunk1_3_checked, root7Node178Step1Chunk1_4_checked, root7Node178Step1Chunk1_5_checked, root7Node178Step1Chunk2_0_checked, root7Node178Step1Chunk2_1_checked, root7Node178Step1Chunk2_2_checked, root7Node178Step1Chunk2_3_checked, root7Node178Step1Chunk2_4_checked, root7Node178Step1Chunk2_5_checked, root7Node178Step1Chunk3_0_checked, root7Node178Step1Chunk3_1_checked, root7Node178Step1Chunk3_2_checked, root7Node178Step1Chunk3_3_checked, root7Node178Step1Chunk3_4_checked, root7Node178Step1Chunk3_5_checked, root7Node178Step1Chunk4_0_checked, root7Node178Step1Chunk4_1_checked, root7Node178Step1Chunk4_2_checked, root7Node178Step1Chunk4_3_checked, root7Node178Step1Chunk4_4_checked, root7Node178Step1Chunk4_5_checked, root7Node178Step1Chunk5_0_checked, root7Node178Step1Chunk5_1_checked, root7Node178Step1Chunk5_2_checked, root7Node178Step1Chunk5_3_checked, root7Node178Step1Chunk5_4_checked, root7Node178Step1Chunk5_5_checked, root7Node178Step1Chunk6_0_checked, root7Node178Step1Chunk6_1_checked, root7Node178Step1Chunk6_2_checked, root7Node178Step1Chunk6_3_checked, root7Node178Step1Chunk6_4_checked, root7Node178Step1Chunk6_5_checked, root7Node178Step1Chunk7_0_checked, root7Node178Step1Chunk7_1_checked, root7Node178Step1Chunk7_2_checked, root7Node178Step1Chunk7_3_checked, root7Node178Step1Chunk7_4_checked, root7Node178Step1Chunk7_5_checked, root7Node178Step1Chunk8_0_checked, root7Node178Step1Chunk8_1_checked, root7Node178Step1Chunk8_2_checked, root7Node178Step1Chunk8_3_checked, root7Node178Step1Chunk8_4_checked, root7Node178Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node178Step1_checked :
    checkReplacement table33 root7Node178Domains0 root7Node178Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node178Domains0 root7Node178Domains1
    root7Node178Domains0Fast root7Node178Domains1Fast
    root7Node178Domains0_fast_eq root7Node178Domains1_fast_eq
    root7Node178Step1Narrowing_checked (by decide)
def root7Node178Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,4),(7,4)]
  | 1 => [(1,3)]
  | 2 => [(5,2),(8,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3),(8,3)]
  | 5 => [(4,2),(5,2),(5,5),(8,2)]
  | 6 => [(7,1),(8,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(1,4),(6,4)]
  | 11 => [(0,5),(1,2),(6,2)]
  | 12 => [(4,4),(7,4),(8,4)]
  | 13 => [(5,0),(5,3),(8,3)]
  | 14 => [(4,5),(8,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(0,3),(6,0)]
  | 19 => [(7,1),(8,1)]
  | 20 => [(1,5),(6,5),(7,5)]
  | 21 => [(7,4),(8,4)]
  | 22 => [(0,0),(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(4,2),(8,2)]
  | 27 => [(5,0),(5,3),(8,0)]
  | 28 => [(4,5),(7,3),(8,5)]
  | 29 => [(4,2),(7,0),(8,2)]
  | 30 => [(4,1),(7,1),(8,1)]
  | 31 => [(0,2),(1,5)]
  | 32 => [(1,1),(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(3,4),(5,4)]
  | 37 => [(0,0),(6,3),(6,4)]
  | 38 => [(1,2),(7,2)]
  | 39 => [(7,4),(8,4)]
  | 40 => [(1,3),(3,3),(5,0),(5,3),(7,3)]
  | 41 => [(4,5),(5,2),(5,5),(8,5)]
  | 42 => [(7,0),(8,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5),(8,5)]
  | 45 => [(7,0)]
  | 46 => [(2,3),(4,3)]
  | 47 => [(0,2),(1,5),(3,5),(7,5)]
  | 48 => [(0,3),(1,1),(6,1)]
  | 49 => [(4,1),(8,1)]
  | 50 => [(0,2),(1,5),(6,5)]
  | 51 => [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 52 => [(4,4),(5,4),(7,2),(8,4)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,4),(6,4),(7,4)]
  | 57 => [(0,5),(1,2),(1,3),(6,3)]
  | 58 => [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 59 => [(1,3),(3,3),(5,3),(7,3)]
  | 60 => [(5,2),(5,5),(8,5)]
  | 61 => [(1,1),(4,3),(6,1),(7,1)]
  | 62 => [(4,1),(7,5)]
  | 63 => [(0,2),(6,0)]
  | 64 => [(1,1),(7,1)]
  | 65 => [(4,1),(7,5),(8,1)]
  | 66 => [(0,2),(0,3),(6,0),(6,5)]
  | 67 => [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 68 => [(0,1),(1,4),(3,4),(6,5)]
  | 69 => [(0,4),(0,5),(6,2),(6,3)]
  | 70 => [(1,3),(7,3)]
  | 71 => [(5,2),(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(4,2),(5,2),(5,5),(8,2)]
  | 75 => [(3,0),(5,0),(5,3),(7,0)]
  | 76 => [(2,3),(2,5),(4,5),(8,5)]
  | 77 => [(0,2),(1,0),(6,0),(7,0)]
  | 78 => [(0,4),(6,2)]
  | 79 => [(5,4),(8,4)]
  | 80 => [(1,4),(6,4)]
  | 81 => [(0,5),(1,2)]
  | 82 => [(4,4),(7,4),(8,4)]
  | 83 => [(0,0),(1,3),(6,3),(6,4)]
  | 84 => [(1,2),(7,2),(8,2)]
  | 85 => [(4,3),(7,1)]
  | 86 => [(3,5),(7,5)]
  | 87 => [(0,3),(6,0)]
  | 88 => [(4,1),(7,1),(8,1)]
  | 89 => [(0,2),(1,5),(6,5),(7,5)]
  | _ => [(0,3),(0,4),(1,1),(6,1)]
def root7Node178Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4),(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2),(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3),(8,3)]
  | 5 => some [(4,2),(5,2),(5,5),(8,2)]
  | 6 => some [(7,1),(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(1,4),(6,4)]
  | 11 => some [(0,5),(1,2),(6,2)]
  | 12 => some [(4,4),(7,4),(8,4)]
  | 13 => some [(5,0),(5,3),(8,3)]
  | 14 => some [(4,5),(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3),(6,0)]
  | 19 => some [(7,1),(8,1)]
  | 20 => some [(1,5),(6,5),(7,5)]
  | 21 => some [(7,4),(8,4)]
  | 22 => some [(0,0),(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2),(8,2)]
  | 27 => some [(5,0),(5,3),(8,0)]
  | 28 => some [(4,5),(7,3),(8,5)]
  | 29 => some [(4,2),(7,0),(8,2)]
  | 30 => some [(4,1),(7,1),(8,1)]
  | 31 => some [(0,2),(1,5)]
  | 32 => some [(1,1),(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(3,4),(5,4)]
  | 37 => some [(0,0),(6,3),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4),(8,4)]
  | 40 => some [(1,3),(3,3),(5,0),(5,3),(7,3)]
  | 41 => some [(4,5),(5,2),(5,5),(8,5)]
  | 42 => some [(7,0),(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(2,3),(4,3)]
  | 47 => some [(0,2),(1,5),(3,5),(7,5)]
  | 48 => some [(0,3),(1,1),(6,1)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(1,5),(6,5)]
  | 51 => some [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 52 => some [(4,4),(5,4),(7,2),(8,4)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(6,4),(7,4)]
  | 57 => some [(0,5),(1,2),(1,3),(6,3)]
  | 58 => some [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 59 => some [(1,3),(3,3),(5,3),(7,3)]
  | 60 => some [(5,2),(5,5),(8,5)]
  | 61 => some [(1,1),(4,3),(6,1),(7,1)]
  | 62 => some [(4,1),(7,5)]
  | 63 => some [(0,2),(6,0)]
  | 64 => some [(1,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(0,3),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 68 => some [(0,1),(1,4),(3,4),(6,5)]
  | 69 => some [(0,4),(0,5),(6,2),(6,3)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(5,2),(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(4,2),(5,2),(5,5),(8,2)]
  | 75 => some [(3,0),(5,0),(5,3),(7,0)]
  | 76 => some [(2,3),(2,5),(4,5),(8,5)]
  | 77 => some [(0,2),(1,0),(6,0),(7,0)]
  | 78 => some [(0,4),(6,2)]
  | 79 => some [(5,4),(8,4)]
  | 80 => some [(1,4),(6,4)]
  | 81 => some [(0,5),(1,2)]
  | 82 => some [(4,4),(7,4),(8,4)]
  | 83 => some [(0,0),(1,3),(6,3),(6,4)]
  | 84 => some [(1,2),(7,2),(8,2)]
  | 85 => some [(4,3),(7,1)]
  | 86 => some [(3,5),(7,5)]
  | 87 => some [(0,3),(6,0)]
  | 88 => some [(4,1),(7,1),(8,1)]
  | 89 => some [(0,2),(1,5),(6,5),(7,5)]
  | _ => some [(0,3),(0,4),(1,1),(6,1)]
theorem root7Node178Domains2_fast_eq : root7Node178Domains2 = expandDomains root7Node178Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node178Domains2 v = expandDomains root7Node178Domains2Fast v from by decide) v
theorem root7Node178Step2Chunk0_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_0⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk0_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_1⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk0_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_2⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk0_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_3⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk0_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_4⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk0_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_5⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk1_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_0⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk1_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_1⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk1_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_2⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk1_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_3⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk1_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_4⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk1_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_5⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk2_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_0⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk2_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_1⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk2_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_2⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk2_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_3⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk2_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_4⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk2_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_5⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk3_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_0⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk3_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_1⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk3_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_2⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk3_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_3⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk3_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_4⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk3_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_5⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk4_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_0⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk4_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_1⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk4_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_2⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk4_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_3⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk4_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_4⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk4_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_5⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk5_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_0⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk5_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_1⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk5_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_2⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk5_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_3⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk5_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_4⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk5_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_5⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk6_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_0⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk6_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_1⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk6_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_2⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk6_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_3⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk6_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_4⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk6_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_5⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk7_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_0⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk7_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_1⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk7_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_2⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk7_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_3⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk7_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_4⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk7_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_5⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk8_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_0⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk8_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_1⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk8_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_2⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk8_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_3⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk8_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_4⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Chunk8_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_5⟩
      root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq (by decide)
theorem root7Node178Step2Narrowing_checked :
    checkNarrowing table53 root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkNarrowing_flatten table53Scope [table53Rows0_0,table53Rows0_1,table53Rows0_2,table53Rows0_3,table53Rows0_4,table53Rows0_5,table53Rows1_0,table53Rows1_1,table53Rows1_2,table53Rows1_3,table53Rows1_4,table53Rows1_5,table53Rows2_0,table53Rows2_1,table53Rows2_2,table53Rows2_3,table53Rows2_4,table53Rows2_5,table53Rows3_0,table53Rows3_1,table53Rows3_2,table53Rows3_3,table53Rows3_4,table53Rows3_5,table53Rows4_0,table53Rows4_1,table53Rows4_2,table53Rows4_3,table53Rows4_4,table53Rows4_5,table53Rows5_0,table53Rows5_1,table53Rows5_2,table53Rows5_3,table53Rows5_4,table53Rows5_5,table53Rows6_0,table53Rows6_1,table53Rows6_2,table53Rows6_3,table53Rows6_4,table53Rows6_5,table53Rows7_0,table53Rows7_1,table53Rows7_2,table53Rows7_3,table53Rows7_4,table53Rows7_5,table53Rows8_0,table53Rows8_1,table53Rows8_2,table53Rows8_3,table53Rows8_4,table53Rows8_5]
    root7Node178Domains1 root7Node178Domains2 (by
      simp only [List.all_cons, List.all_nil, root7Node178Step2Chunk0_0_checked, root7Node178Step2Chunk0_1_checked, root7Node178Step2Chunk0_2_checked, root7Node178Step2Chunk0_3_checked, root7Node178Step2Chunk0_4_checked, root7Node178Step2Chunk0_5_checked, root7Node178Step2Chunk1_0_checked, root7Node178Step2Chunk1_1_checked, root7Node178Step2Chunk1_2_checked, root7Node178Step2Chunk1_3_checked, root7Node178Step2Chunk1_4_checked, root7Node178Step2Chunk1_5_checked, root7Node178Step2Chunk2_0_checked, root7Node178Step2Chunk2_1_checked, root7Node178Step2Chunk2_2_checked, root7Node178Step2Chunk2_3_checked, root7Node178Step2Chunk2_4_checked, root7Node178Step2Chunk2_5_checked, root7Node178Step2Chunk3_0_checked, root7Node178Step2Chunk3_1_checked, root7Node178Step2Chunk3_2_checked, root7Node178Step2Chunk3_3_checked, root7Node178Step2Chunk3_4_checked, root7Node178Step2Chunk3_5_checked, root7Node178Step2Chunk4_0_checked, root7Node178Step2Chunk4_1_checked, root7Node178Step2Chunk4_2_checked, root7Node178Step2Chunk4_3_checked, root7Node178Step2Chunk4_4_checked, root7Node178Step2Chunk4_5_checked, root7Node178Step2Chunk5_0_checked, root7Node178Step2Chunk5_1_checked, root7Node178Step2Chunk5_2_checked, root7Node178Step2Chunk5_3_checked, root7Node178Step2Chunk5_4_checked, root7Node178Step2Chunk5_5_checked, root7Node178Step2Chunk6_0_checked, root7Node178Step2Chunk6_1_checked, root7Node178Step2Chunk6_2_checked, root7Node178Step2Chunk6_3_checked, root7Node178Step2Chunk6_4_checked, root7Node178Step2Chunk6_5_checked, root7Node178Step2Chunk7_0_checked, root7Node178Step2Chunk7_1_checked, root7Node178Step2Chunk7_2_checked, root7Node178Step2Chunk7_3_checked, root7Node178Step2Chunk7_4_checked, root7Node178Step2Chunk7_5_checked, root7Node178Step2Chunk8_0_checked, root7Node178Step2Chunk8_1_checked, root7Node178Step2Chunk8_2_checked, root7Node178Step2Chunk8_3_checked, root7Node178Step2Chunk8_4_checked, root7Node178Step2Chunk8_5_checked, Bool.true_and])
theorem root7Node178Step2_checked :
    checkReplacement table53 root7Node178Domains1 root7Node178Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root7Node178Domains1 root7Node178Domains2
    root7Node178Domains1Fast root7Node178Domains2Fast
    root7Node178Domains1_fast_eq root7Node178Domains2_fast_eq
    root7Node178Step2Narrowing_checked (by decide)
def root7Node178Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,4),(7,4)]
  | 1 => [(1,3)]
  | 2 => [(5,2),(8,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3),(8,3)]
  | 5 => [(4,2),(5,2),(5,5),(8,2)]
  | 6 => [(7,1),(8,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(1,4),(6,4)]
  | 11 => [(0,5),(1,2)]
  | 12 => [(4,4),(7,4),(8,4)]
  | 13 => [(5,0),(5,3),(8,3)]
  | 14 => [(4,5),(8,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(0,3),(6,0)]
  | 19 => [(7,1),(8,1)]
  | 20 => [(1,5),(6,5),(7,5)]
  | 21 => [(7,4),(8,4)]
  | 22 => [(0,0),(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(4,2),(8,2)]
  | 27 => [(5,0),(5,3),(8,0)]
  | 28 => [(4,5),(7,3),(8,5)]
  | 29 => [(4,2),(7,0),(8,2)]
  | 30 => [(4,1),(7,1),(8,1)]
  | 31 => [(0,2),(1,5)]
  | 32 => [(1,1),(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(3,4),(5,4)]
  | 37 => [(0,0),(6,3),(6,4)]
  | 38 => [(1,2),(7,2)]
  | 39 => [(7,4),(8,4)]
  | 40 => [(1,3),(3,3),(5,0),(5,3),(7,3)]
  | 41 => [(4,5),(5,2),(5,5),(8,5)]
  | 42 => [(7,0),(8,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5),(8,5)]
  | 45 => [(7,0)]
  | 46 => [(2,3),(4,3)]
  | 47 => [(0,2),(1,5),(3,5),(7,5)]
  | 48 => [(0,3),(1,1),(6,1)]
  | 49 => [(4,1),(8,1)]
  | 50 => [(0,2),(1,5),(6,5)]
  | 51 => [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 52 => [(4,4),(5,4),(7,2),(8,4)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,4),(6,4),(7,4)]
  | 57 => [(0,5),(1,2),(1,3),(6,3)]
  | 58 => [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 59 => [(1,3),(3,3),(5,3),(7,3)]
  | 60 => [(5,2),(5,5),(8,5)]
  | 61 => [(1,1),(4,3),(6,1),(7,1)]
  | 62 => [(4,1),(7,5)]
  | 63 => [(0,2),(6,0)]
  | 64 => [(1,1),(7,1)]
  | 65 => [(4,1),(7,5),(8,1)]
  | 66 => [(0,2),(0,3),(6,0),(6,5)]
  | 67 => [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 68 => [(0,1),(1,4),(3,4),(6,5)]
  | 69 => [(0,4),(0,5),(6,2),(6,3)]
  | 70 => [(1,3),(7,3)]
  | 71 => [(5,2),(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(4,2),(5,2),(5,5),(8,2)]
  | 75 => [(3,0),(5,0),(5,3),(7,0)]
  | 76 => [(2,3),(2,5),(4,5),(8,5)]
  | 77 => [(0,2),(1,0),(6,0),(7,0)]
  | 78 => [(0,4),(6,2)]
  | 79 => [(5,4),(8,4)]
  | 80 => [(1,4),(6,4)]
  | 81 => [(0,5),(1,2)]
  | 82 => [(4,4),(7,4),(8,4)]
  | 83 => [(0,0),(1,3),(6,3),(6,4)]
  | 84 => [(1,2),(7,2),(8,2)]
  | 85 => [(4,3),(7,1)]
  | 86 => [(3,5),(7,5)]
  | 87 => [(0,3),(6,0)]
  | 88 => [(4,1),(7,1),(8,1)]
  | 89 => [(0,2),(1,5),(6,5),(7,5)]
  | _ => [(0,3),(0,4),(1,1),(6,1)]
def root7Node178Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4),(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2),(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3),(8,3)]
  | 5 => some [(4,2),(5,2),(5,5),(8,2)]
  | 6 => some [(7,1),(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(1,4),(6,4)]
  | 11 => some [(0,5),(1,2)]
  | 12 => some [(4,4),(7,4),(8,4)]
  | 13 => some [(5,0),(5,3),(8,3)]
  | 14 => some [(4,5),(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3),(6,0)]
  | 19 => some [(7,1),(8,1)]
  | 20 => some [(1,5),(6,5),(7,5)]
  | 21 => some [(7,4),(8,4)]
  | 22 => some [(0,0),(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2),(8,2)]
  | 27 => some [(5,0),(5,3),(8,0)]
  | 28 => some [(4,5),(7,3),(8,5)]
  | 29 => some [(4,2),(7,0),(8,2)]
  | 30 => some [(4,1),(7,1),(8,1)]
  | 31 => some [(0,2),(1,5)]
  | 32 => some [(1,1),(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(3,4),(5,4)]
  | 37 => some [(0,0),(6,3),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4),(8,4)]
  | 40 => some [(1,3),(3,3),(5,0),(5,3),(7,3)]
  | 41 => some [(4,5),(5,2),(5,5),(8,5)]
  | 42 => some [(7,0),(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(2,3),(4,3)]
  | 47 => some [(0,2),(1,5),(3,5),(7,5)]
  | 48 => some [(0,3),(1,1),(6,1)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(1,5),(6,5)]
  | 51 => some [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 52 => some [(4,4),(5,4),(7,2),(8,4)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(6,4),(7,4)]
  | 57 => some [(0,5),(1,2),(1,3),(6,3)]
  | 58 => some [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 59 => some [(1,3),(3,3),(5,3),(7,3)]
  | 60 => some [(5,2),(5,5),(8,5)]
  | 61 => some [(1,1),(4,3),(6,1),(7,1)]
  | 62 => some [(4,1),(7,5)]
  | 63 => some [(0,2),(6,0)]
  | 64 => some [(1,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(0,3),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 68 => some [(0,1),(1,4),(3,4),(6,5)]
  | 69 => some [(0,4),(0,5),(6,2),(6,3)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(5,2),(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(4,2),(5,2),(5,5),(8,2)]
  | 75 => some [(3,0),(5,0),(5,3),(7,0)]
  | 76 => some [(2,3),(2,5),(4,5),(8,5)]
  | 77 => some [(0,2),(1,0),(6,0),(7,0)]
  | 78 => some [(0,4),(6,2)]
  | 79 => some [(5,4),(8,4)]
  | 80 => some [(1,4),(6,4)]
  | 81 => some [(0,5),(1,2)]
  | 82 => some [(4,4),(7,4),(8,4)]
  | 83 => some [(0,0),(1,3),(6,3),(6,4)]
  | 84 => some [(1,2),(7,2),(8,2)]
  | 85 => some [(4,3),(7,1)]
  | 86 => some [(3,5),(7,5)]
  | 87 => some [(0,3),(6,0)]
  | 88 => some [(4,1),(7,1),(8,1)]
  | 89 => some [(0,2),(1,5),(6,5),(7,5)]
  | _ => some [(0,3),(0,4),(1,1),(6,1)]
theorem root7Node178Domains3_fast_eq : root7Node178Domains3 = expandDomains root7Node178Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node178Domains3 v = expandDomains root7Node178Domains3Fast v from by decide) v
theorem root7Node178Step3Chunk0_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_0⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk0_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_1⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk0_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_2⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk0_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_3⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk0_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_4⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk0_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_5⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk1_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_0⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk1_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_1⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk1_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_2⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk1_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_3⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk1_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_4⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk1_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_5⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk2_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_0⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk2_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_1⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk2_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_2⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk2_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_3⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk2_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_4⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk2_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_5⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk3_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_0⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk3_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_1⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk3_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_2⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk3_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_3⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk3_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_4⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk3_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_5⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk4_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_0⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk4_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_1⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk4_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_2⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk4_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_3⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk4_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_4⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk4_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_5⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk5_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_0⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk5_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_1⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk5_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_2⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk5_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_3⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk5_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_4⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk5_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_5⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk6_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_0⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk6_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_1⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk6_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_2⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk6_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_3⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk6_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_4⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk6_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_5⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk7_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_0⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk7_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_1⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk7_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_2⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk7_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_3⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk7_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_4⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk7_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_5⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk8_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_0⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk8_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_1⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk8_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_2⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk8_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_3⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk8_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_4⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Chunk8_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_5⟩
      root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq (by decide)
theorem root7Node178Step3Narrowing_checked :
    checkNarrowing table1 root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkNarrowing_flatten table1Scope [table1Rows0_0,table1Rows0_1,table1Rows0_2,table1Rows0_3,table1Rows0_4,table1Rows0_5,table1Rows1_0,table1Rows1_1,table1Rows1_2,table1Rows1_3,table1Rows1_4,table1Rows1_5,table1Rows2_0,table1Rows2_1,table1Rows2_2,table1Rows2_3,table1Rows2_4,table1Rows2_5,table1Rows3_0,table1Rows3_1,table1Rows3_2,table1Rows3_3,table1Rows3_4,table1Rows3_5,table1Rows4_0,table1Rows4_1,table1Rows4_2,table1Rows4_3,table1Rows4_4,table1Rows4_5,table1Rows5_0,table1Rows5_1,table1Rows5_2,table1Rows5_3,table1Rows5_4,table1Rows5_5,table1Rows6_0,table1Rows6_1,table1Rows6_2,table1Rows6_3,table1Rows6_4,table1Rows6_5,table1Rows7_0,table1Rows7_1,table1Rows7_2,table1Rows7_3,table1Rows7_4,table1Rows7_5,table1Rows8_0,table1Rows8_1,table1Rows8_2,table1Rows8_3,table1Rows8_4,table1Rows8_5]
    root7Node178Domains2 root7Node178Domains3 (by
      simp only [List.all_cons, List.all_nil, root7Node178Step3Chunk0_0_checked, root7Node178Step3Chunk0_1_checked, root7Node178Step3Chunk0_2_checked, root7Node178Step3Chunk0_3_checked, root7Node178Step3Chunk0_4_checked, root7Node178Step3Chunk0_5_checked, root7Node178Step3Chunk1_0_checked, root7Node178Step3Chunk1_1_checked, root7Node178Step3Chunk1_2_checked, root7Node178Step3Chunk1_3_checked, root7Node178Step3Chunk1_4_checked, root7Node178Step3Chunk1_5_checked, root7Node178Step3Chunk2_0_checked, root7Node178Step3Chunk2_1_checked, root7Node178Step3Chunk2_2_checked, root7Node178Step3Chunk2_3_checked, root7Node178Step3Chunk2_4_checked, root7Node178Step3Chunk2_5_checked, root7Node178Step3Chunk3_0_checked, root7Node178Step3Chunk3_1_checked, root7Node178Step3Chunk3_2_checked, root7Node178Step3Chunk3_3_checked, root7Node178Step3Chunk3_4_checked, root7Node178Step3Chunk3_5_checked, root7Node178Step3Chunk4_0_checked, root7Node178Step3Chunk4_1_checked, root7Node178Step3Chunk4_2_checked, root7Node178Step3Chunk4_3_checked, root7Node178Step3Chunk4_4_checked, root7Node178Step3Chunk4_5_checked, root7Node178Step3Chunk5_0_checked, root7Node178Step3Chunk5_1_checked, root7Node178Step3Chunk5_2_checked, root7Node178Step3Chunk5_3_checked, root7Node178Step3Chunk5_4_checked, root7Node178Step3Chunk5_5_checked, root7Node178Step3Chunk6_0_checked, root7Node178Step3Chunk6_1_checked, root7Node178Step3Chunk6_2_checked, root7Node178Step3Chunk6_3_checked, root7Node178Step3Chunk6_4_checked, root7Node178Step3Chunk6_5_checked, root7Node178Step3Chunk7_0_checked, root7Node178Step3Chunk7_1_checked, root7Node178Step3Chunk7_2_checked, root7Node178Step3Chunk7_3_checked, root7Node178Step3Chunk7_4_checked, root7Node178Step3Chunk7_5_checked, root7Node178Step3Chunk8_0_checked, root7Node178Step3Chunk8_1_checked, root7Node178Step3Chunk8_2_checked, root7Node178Step3Chunk8_3_checked, root7Node178Step3Chunk8_4_checked, root7Node178Step3Chunk8_5_checked, Bool.true_and])
theorem root7Node178Step3_checked :
    checkReplacement table1 root7Node178Domains2 root7Node178Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root7Node178Domains2 root7Node178Domains3
    root7Node178Domains2Fast root7Node178Domains3Fast
    root7Node178Domains2_fast_eq root7Node178Domains3_fast_eq
    root7Node178Step3Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
