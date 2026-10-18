module

public import SpectreFinite.RadiusFiveRoot7Part45
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable52
public import SpectreFinite.RadiusFiveTable56
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node114Domains0 : Domains 91 State := restrict root7Node112Domains3 60 (8,5)
def root7Node114Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(4,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(2,4)]
  | 25 => some [(1,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(8,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(0,3)]
  | 62 => some [(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(1,4),(3,4)]
  | 69 => some [(0,5),(6,3)]
  | 70 => some [(5,3)]
  | 71 => some [(5,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(3,0),(7,0)]
  | 76 => some [(2,3),(2,5)]
  | 77 => some [(0,2),(6,0)]
  | 78 => some [(0,5)]
  | 79 => some [(4,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node114Domains0_fast_eq : root7Node114Domains0 = expandDomains root7Node114Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node114Domains0 v = expandDomains root7Node114Domains0Fast v from by decide) v
def root7Node114Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(8,0)]
  | 2 => [(7,3)]
  | 3 => [(4,2)]
  | 4 => [(5,3)]
  | 5 => [(8,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(6,4)]
  | 9 => [(1,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(3,5)]
  | 16 => [(0,3)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(4,1)]
  | 21 => [(4,4)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(2,4)]
  | 25 => [(1,3)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(8,4)]
  | 40 => [(8,0)]
  | 41 => [(7,3)]
  | 42 => [(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(8,1)]
  | 50 => [(1,5)]
  | 51 => [(6,4)]
  | 52 => [(1,2)]
  | 53 => [(8,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3)]
  | 58 => [(4,2)]
  | 59 => [(5,3)]
  | 60 => [(8,5)]
  | 61 => [(0,3)]
  | 62 => [(8,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(8,1)]
  | 66 => [(6,5)]
  | 67 => [(0,4)]
  | 68 => [(3,4)]
  | 69 => [(6,3)]
  | 70 => [(5,3)]
  | 71 => [(5,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5)]
  | 75 => [(7,0)]
  | 76 => [(2,3)]
  | 77 => [(0,2)]
  | 78 => [(0,5)]
  | 79 => [(4,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(4,4)]
  | 83 => [(6,4)]
  | 84 => [(1,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(7,1)]
  | 89 => [(7,5)]
  | _ => [(0,3)]
def root7Node114Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(4,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(2,4)]
  | 25 => some [(1,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(8,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(0,3)]
  | 62 => some [(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(3,4)]
  | 69 => some [(6,3)]
  | 70 => some [(5,3)]
  | 71 => some [(5,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(7,0)]
  | 76 => some [(2,3)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5)]
  | 79 => some [(4,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(0,3)]
theorem root7Node114Domains1_fast_eq : root7Node114Domains1 = expandDomains root7Node114Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node114Domains1 v = expandDomains root7Node114Domains1Fast v from by decide) v
theorem root7Node114Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Narrowing_checked :
    checkNarrowing table56 root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root7Node114Domains0 root7Node114Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node114Step1Chunk0_0_checked, root7Node114Step1Chunk0_1_checked, root7Node114Step1Chunk0_2_checked, root7Node114Step1Chunk0_3_checked, root7Node114Step1Chunk0_4_checked, root7Node114Step1Chunk0_5_checked, root7Node114Step1Chunk1_0_checked, root7Node114Step1Chunk1_1_checked, root7Node114Step1Chunk1_2_checked, root7Node114Step1Chunk1_3_checked, root7Node114Step1Chunk1_4_checked, root7Node114Step1Chunk1_5_checked, root7Node114Step1Chunk2_0_checked, root7Node114Step1Chunk2_1_checked, root7Node114Step1Chunk2_2_checked, root7Node114Step1Chunk2_3_checked, root7Node114Step1Chunk2_4_checked, root7Node114Step1Chunk2_5_checked, root7Node114Step1Chunk3_0_checked, root7Node114Step1Chunk3_1_checked, root7Node114Step1Chunk3_2_checked, root7Node114Step1Chunk3_3_checked, root7Node114Step1Chunk3_4_checked, root7Node114Step1Chunk3_5_checked, root7Node114Step1Chunk4_0_checked, root7Node114Step1Chunk4_1_checked, root7Node114Step1Chunk4_2_checked, root7Node114Step1Chunk4_3_checked, root7Node114Step1Chunk4_4_checked, root7Node114Step1Chunk4_5_checked, root7Node114Step1Chunk5_0_checked, root7Node114Step1Chunk5_1_checked, root7Node114Step1Chunk5_2_checked, root7Node114Step1Chunk5_3_checked, root7Node114Step1Chunk5_4_checked, root7Node114Step1Chunk5_5_checked, root7Node114Step1Chunk6_0_checked, root7Node114Step1Chunk6_1_checked, root7Node114Step1Chunk6_2_checked, root7Node114Step1Chunk6_3_checked, root7Node114Step1Chunk6_4_checked, root7Node114Step1Chunk6_5_checked, root7Node114Step1Chunk7_0_checked, root7Node114Step1Chunk7_1_checked, root7Node114Step1Chunk7_2_checked, root7Node114Step1Chunk7_3_checked, root7Node114Step1Chunk7_4_checked, root7Node114Step1Chunk7_5_checked, root7Node114Step1Chunk8_0_checked, root7Node114Step1Chunk8_1_checked, root7Node114Step1Chunk8_2_checked, root7Node114Step1Chunk8_3_checked, root7Node114Step1Chunk8_4_checked, root7Node114Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node114Step1_checked :
    checkReplacement table56 root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq
    root7Node114Step1Narrowing_checked (by decide)
theorem root7Node114Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node114Domains1 (.output 56) = true := by decide
def root7Node115Domains0 : Domains 91 State := restrict root7Node111Domains4 28 (8,3)
def root7Node115Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1),(5,1),(8,1)]
  | 21 => some [(4,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(2,4)]
  | 25 => some [(1,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,2),(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(1,4),(6,4)]
  | 38 => some [(0,5),(1,2)]
  | 39 => some [(4,4),(8,4)]
  | 40 => some [(4,0),(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3),(6,0)]
  | 49 => some [(7,1),(8,1)]
  | 50 => some [(1,5),(7,5)]
  | 51 => some [(0,1),(6,4)]
  | 52 => some [(1,2),(6,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(4,2),(8,2)]
  | 59 => some [(5,0),(5,3),(8,0)]
  | 60 => some [(4,5),(5,5),(7,3),(8,5)]
  | 61 => some [(0,3),(1,0)]
  | 62 => some [(7,1),(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(1,4),(3,4),(5,4)]
  | 69 => some [(0,0),(0,5),(6,3),(6,4)]
  | 70 => some [(5,0),(5,3)]
  | 71 => some [(4,5),(5,5),(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5),(8,5)]
  | 75 => some [(3,0),(7,0)]
  | 76 => some [(2,3),(2,5),(4,3)]
  | 77 => some [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | 78 => some [(0,0),(0,5),(6,3)]
  | 79 => some [(4,4),(7,2)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(6,3)]
  | 82 => some [(4,4),(7,2)]
  | 83 => some [(0,0),(1,4),(6,4),(7,4)]
  | 84 => some [(0,5),(1,2),(1,3),(6,3),(7,2)]
  | 85 => some [(1,1),(6,1),(7,1)]
  | 86 => some [(4,1),(7,5)]
  | 87 => some [(0,2),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(1,5),(4,1),(7,5),(8,1)]
  | _ => some [(0,2),(0,3),(6,0),(6,1),(6,5)]
theorem root7Node115Domains0_fast_eq : root7Node115Domains0 = expandDomains root7Node115Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node115Domains0 v = expandDomains root7Node115Domains0Fast v from by decide) v
def root7Node115Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(8,0)]
  | 2 => [(7,3)]
  | 3 => [(4,2)]
  | 4 => [(5,3)]
  | 5 => [(8,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(6,4)]
  | 9 => [(1,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(3,5)]
  | 16 => [(0,3)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(5,1),(8,1)]
  | 21 => [(4,4)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(2,4)]
  | 25 => [(1,3)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(4,4)]
  | 40 => [(4,0),(8,0)]
  | 41 => [(7,3)]
  | 42 => [(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(7,1)]
  | 50 => [(1,5),(7,5)]
  | 51 => [(0,1),(6,4)]
  | 52 => [(1,2),(6,2)]
  | 53 => [(8,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0),(8,0)]
  | 60 => [(4,5),(7,3)]
  | 61 => [(0,3),(1,0)]
  | 62 => [(7,1),(8,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(8,1)]
  | 66 => [(6,5)]
  | 67 => [(0,4)]
  | 68 => [(5,4)]
  | 69 => [(0,0),(6,4)]
  | 70 => [(5,0),(5,3)]
  | 71 => [(4,5),(5,5),(8,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5),(8,5)]
  | 75 => [(7,0)]
  | 76 => [(4,3)]
  | 77 => [(1,5),(3,5),(7,5)]
  | 78 => [(0,0),(0,5),(6,3)]
  | 79 => [(4,4),(7,2)]
  | 80 => [(1,4),(7,4)]
  | 81 => [(0,5),(6,3)]
  | 82 => [(4,4),(7,2)]
  | 83 => [(1,4),(7,4)]
  | 84 => [(0,5),(1,3),(6,3)]
  | 85 => [(1,1),(6,1),(7,1)]
  | 86 => [(4,1),(7,5)]
  | 87 => [(0,2),(6,0)]
  | 88 => [(1,1),(7,1)]
  | 89 => [(4,1),(7,5),(8,1)]
  | _ => [(0,2),(6,0),(6,5)]
def root7Node115Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(5,1),(8,1)]
  | 21 => some [(4,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(2,4)]
  | 25 => some [(1,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(4,0),(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5),(7,5)]
  | 51 => some [(0,1),(6,4)]
  | 52 => some [(1,2),(6,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0),(8,0)]
  | 60 => some [(4,5),(7,3)]
  | 61 => some [(0,3),(1,0)]
  | 62 => some [(7,1),(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(5,4)]
  | 69 => some [(0,0),(6,4)]
  | 70 => some [(5,0),(5,3)]
  | 71 => some [(4,5),(5,5),(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5),(8,5)]
  | 75 => some [(7,0)]
  | 76 => some [(4,3)]
  | 77 => some [(1,5),(3,5),(7,5)]
  | 78 => some [(0,0),(0,5),(6,3)]
  | 79 => some [(4,4),(7,2)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(6,3)]
  | 82 => some [(4,4),(7,2)]
  | 83 => some [(1,4),(7,4)]
  | 84 => some [(0,5),(1,3),(6,3)]
  | 85 => some [(1,1),(6,1),(7,1)]
  | 86 => some [(4,1),(7,5)]
  | 87 => some [(0,2),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(4,1),(7,5),(8,1)]
  | _ => some [(0,2),(6,0),(6,5)]
theorem root7Node115Domains1_fast_eq : root7Node115Domains1 = expandDomains root7Node115Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node115Domains1 v = expandDomains root7Node115Domains1Fast v from by decide) v
theorem root7Node115Step1Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Narrowing_checked :
    checkNarrowing table57 root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root7Node115Domains0 root7Node115Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node115Step1Chunk0_0_checked, root7Node115Step1Chunk0_1_checked, root7Node115Step1Chunk0_2_checked, root7Node115Step1Chunk0_3_checked, root7Node115Step1Chunk0_4_checked, root7Node115Step1Chunk0_5_checked, root7Node115Step1Chunk1_0_checked, root7Node115Step1Chunk1_1_checked, root7Node115Step1Chunk1_2_checked, root7Node115Step1Chunk1_3_checked, root7Node115Step1Chunk1_4_checked, root7Node115Step1Chunk1_5_checked, root7Node115Step1Chunk2_0_checked, root7Node115Step1Chunk2_1_checked, root7Node115Step1Chunk2_2_checked, root7Node115Step1Chunk2_3_checked, root7Node115Step1Chunk2_4_checked, root7Node115Step1Chunk2_5_checked, root7Node115Step1Chunk3_0_checked, root7Node115Step1Chunk3_1_checked, root7Node115Step1Chunk3_2_checked, root7Node115Step1Chunk3_3_checked, root7Node115Step1Chunk3_4_checked, root7Node115Step1Chunk3_5_checked, root7Node115Step1Chunk4_0_checked, root7Node115Step1Chunk4_1_checked, root7Node115Step1Chunk4_2_checked, root7Node115Step1Chunk4_3_checked, root7Node115Step1Chunk4_4_checked, root7Node115Step1Chunk4_5_checked, root7Node115Step1Chunk5_0_checked, root7Node115Step1Chunk5_1_checked, root7Node115Step1Chunk5_2_checked, root7Node115Step1Chunk5_3_checked, root7Node115Step1Chunk5_4_checked, root7Node115Step1Chunk5_5_checked, root7Node115Step1Chunk6_0_checked, root7Node115Step1Chunk6_1_checked, root7Node115Step1Chunk6_2_checked, root7Node115Step1Chunk6_3_checked, root7Node115Step1Chunk6_4_checked, root7Node115Step1Chunk6_5_checked, root7Node115Step1Chunk7_0_checked, root7Node115Step1Chunk7_1_checked, root7Node115Step1Chunk7_2_checked, root7Node115Step1Chunk7_3_checked, root7Node115Step1Chunk7_4_checked, root7Node115Step1Chunk7_5_checked, root7Node115Step1Chunk8_0_checked, root7Node115Step1Chunk8_1_checked, root7Node115Step1Chunk8_2_checked, root7Node115Step1Chunk8_3_checked, root7Node115Step1Chunk8_4_checked, root7Node115Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node115Step1_checked :
    checkReplacement table57 root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq
    root7Node115Step1Narrowing_checked (by decide)
def root7Node116Domains0 : Domains 91 State := restrict root7Node115Domains1 20 (5,1)
def root7Node116Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(5,1)]
  | 21 => some [(4,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(2,4)]
  | 25 => some [(1,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(4,0),(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5),(7,5)]
  | 51 => some [(0,1),(6,4)]
  | 52 => some [(1,2),(6,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0),(8,0)]
  | 60 => some [(4,5),(7,3)]
  | 61 => some [(0,3),(1,0)]
  | 62 => some [(7,1),(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(5,4)]
  | 69 => some [(0,0),(6,4)]
  | 70 => some [(5,0),(5,3)]
  | 71 => some [(4,5),(5,5),(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5),(8,5)]
  | 75 => some [(7,0)]
  | 76 => some [(4,3)]
  | 77 => some [(1,5),(3,5),(7,5)]
  | 78 => some [(0,0),(0,5),(6,3)]
  | 79 => some [(4,4),(7,2)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(6,3)]
  | 82 => some [(4,4),(7,2)]
  | 83 => some [(1,4),(7,4)]
  | 84 => some [(0,5),(1,3),(6,3)]
  | 85 => some [(1,1),(6,1),(7,1)]
  | 86 => some [(4,1),(7,5)]
  | 87 => some [(0,2),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(4,1),(7,5),(8,1)]
  | _ => some [(0,2),(6,0),(6,5)]
theorem root7Node116Domains0_fast_eq : root7Node116Domains0 = expandDomains root7Node116Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node116Domains0 v = expandDomains root7Node116Domains0Fast v from by decide) v
def root7Node116Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(8,0)]
  | 2 => [(7,3)]
  | 3 => [(4,2)]
  | 4 => [(5,3)]
  | 5 => [(8,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(6,4)]
  | 9 => [(1,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(3,5)]
  | 16 => [(0,3)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(5,1)]
  | 21 => [(4,4)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(2,4)]
  | 25 => [(1,3)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(4,4)]
  | 40 => [(4,0),(8,0)]
  | 41 => [(7,3)]
  | 42 => [(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(7,1)]
  | 50 => [(1,5)]
  | 51 => [(0,1),(6,4)]
  | 52 => [(1,2),(6,2)]
  | 53 => [(8,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(0,3),(1,0)]
  | 62 => [(7,1),(8,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(8,1)]
  | 66 => [(6,5)]
  | 67 => [(0,4)]
  | 68 => [(5,4)]
  | 69 => [(0,0)]
  | 70 => [(5,0),(5,3)]
  | 71 => [(4,5),(5,5),(8,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5)]
  | 75 => [(7,0)]
  | 76 => [(4,3)]
  | 77 => [(1,5)]
  | 78 => [(0,0),(0,5),(6,3)]
  | 79 => [(4,4),(7,2)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(4,4)]
  | 83 => [(1,4)]
  | 84 => [(0,5)]
  | 85 => [(1,1),(6,1),(7,1)]
  | 86 => [(4,1),(7,5)]
  | 87 => [(6,0)]
  | 88 => [(7,1)]
  | 89 => [(7,5)]
  | _ => [(6,0)]
def root7Node116Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(5,1)]
  | 21 => some [(4,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(2,4)]
  | 25 => some [(1,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(4,0),(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5)]
  | 51 => some [(0,1),(6,4)]
  | 52 => some [(1,2),(6,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(0,3),(1,0)]
  | 62 => some [(7,1),(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(5,4)]
  | 69 => some [(0,0)]
  | 70 => some [(5,0),(5,3)]
  | 71 => some [(4,5),(5,5),(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(7,0)]
  | 76 => some [(4,3)]
  | 77 => some [(1,5)]
  | 78 => some [(0,0),(0,5),(6,3)]
  | 79 => some [(4,4),(7,2)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(1,4)]
  | 84 => some [(0,5)]
  | 85 => some [(1,1),(6,1),(7,1)]
  | 86 => some [(4,1),(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(6,0)]
theorem root7Node116Domains1_fast_eq : root7Node116Domains1 = expandDomains root7Node116Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node116Domains1 v = expandDomains root7Node116Domains1Fast v from by decide) v
theorem root7Node116Step1Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Narrowing_checked :
    checkNarrowing table57 root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root7Node116Domains0 root7Node116Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node116Step1Chunk0_0_checked, root7Node116Step1Chunk0_1_checked, root7Node116Step1Chunk0_2_checked, root7Node116Step1Chunk0_3_checked, root7Node116Step1Chunk0_4_checked, root7Node116Step1Chunk0_5_checked, root7Node116Step1Chunk1_0_checked, root7Node116Step1Chunk1_1_checked, root7Node116Step1Chunk1_2_checked, root7Node116Step1Chunk1_3_checked, root7Node116Step1Chunk1_4_checked, root7Node116Step1Chunk1_5_checked, root7Node116Step1Chunk2_0_checked, root7Node116Step1Chunk2_1_checked, root7Node116Step1Chunk2_2_checked, root7Node116Step1Chunk2_3_checked, root7Node116Step1Chunk2_4_checked, root7Node116Step1Chunk2_5_checked, root7Node116Step1Chunk3_0_checked, root7Node116Step1Chunk3_1_checked, root7Node116Step1Chunk3_2_checked, root7Node116Step1Chunk3_3_checked, root7Node116Step1Chunk3_4_checked, root7Node116Step1Chunk3_5_checked, root7Node116Step1Chunk4_0_checked, root7Node116Step1Chunk4_1_checked, root7Node116Step1Chunk4_2_checked, root7Node116Step1Chunk4_3_checked, root7Node116Step1Chunk4_4_checked, root7Node116Step1Chunk4_5_checked, root7Node116Step1Chunk5_0_checked, root7Node116Step1Chunk5_1_checked, root7Node116Step1Chunk5_2_checked, root7Node116Step1Chunk5_3_checked, root7Node116Step1Chunk5_4_checked, root7Node116Step1Chunk5_5_checked, root7Node116Step1Chunk6_0_checked, root7Node116Step1Chunk6_1_checked, root7Node116Step1Chunk6_2_checked, root7Node116Step1Chunk6_3_checked, root7Node116Step1Chunk6_4_checked, root7Node116Step1Chunk6_5_checked, root7Node116Step1Chunk7_0_checked, root7Node116Step1Chunk7_1_checked, root7Node116Step1Chunk7_2_checked, root7Node116Step1Chunk7_3_checked, root7Node116Step1Chunk7_4_checked, root7Node116Step1Chunk7_5_checked, root7Node116Step1Chunk8_0_checked, root7Node116Step1Chunk8_1_checked, root7Node116Step1Chunk8_2_checked, root7Node116Step1Chunk8_3_checked, root7Node116Step1Chunk8_4_checked, root7Node116Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node116Step1_checked :
    checkReplacement table57 root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq
    root7Node116Step1Narrowing_checked (by decide)
def root7Node116Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(8,0)]
  | 2 => [(7,3)]
  | 3 => [(4,2)]
  | 4 => [(5,3)]
  | 5 => [(8,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(6,4)]
  | 9 => [(1,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(3,5)]
  | 16 => [(0,3)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(5,1)]
  | 21 => [(4,4)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(2,4)]
  | 25 => [(1,3)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(4,4)]
  | 40 => [(8,0)]
  | 41 => [(7,3)]
  | 42 => [(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(7,1)]
  | 50 => [(1,5)]
  | 51 => [(6,4)]
  | 52 => [(1,2)]
  | 53 => [(8,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(0,3)]
  | 62 => [(8,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(8,1)]
  | 66 => [(6,5)]
  | 67 => [(0,4)]
  | 68 => [(5,4)]
  | 69 => [(0,0)]
  | 70 => [(5,3)]
  | 71 => [(5,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5)]
  | 75 => [(7,0)]
  | 76 => [(4,3)]
  | 77 => [(1,5)]
  | 78 => [(0,5)]
  | 79 => [(4,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(4,4)]
  | 83 => [(1,4)]
  | 84 => [(0,5)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(7,1)]
  | 89 => [(7,5)]
  | _ => [(6,0)]
def root7Node116Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(5,1)]
  | 21 => some [(4,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(2,4)]
  | 25 => some [(1,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(0,3)]
  | 62 => some [(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(5,4)]
  | 69 => some [(0,0)]
  | 70 => some [(5,3)]
  | 71 => some [(5,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(7,0)]
  | 76 => some [(4,3)]
  | 77 => some [(1,5)]
  | 78 => some [(0,5)]
  | 79 => some [(4,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(1,4)]
  | 84 => some [(0,5)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(6,0)]
theorem root7Node116Domains2_fast_eq : root7Node116Domains2 = expandDomains root7Node116Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node116Domains2 v = expandDomains root7Node116Domains2Fast v from by decide) v
theorem root7Node116Step2Chunk0_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_0⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk0_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_1⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk0_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_2⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk0_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_3⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk0_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_4⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk0_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_5⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk1_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_0⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk1_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_1⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk1_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_2⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk1_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_3⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk1_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_4⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk1_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_5⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk2_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_0⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk2_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_1⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk2_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_2⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk2_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_3⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk2_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_4⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk2_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_5⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk3_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_0⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk3_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_1⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk3_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_2⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk3_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_3⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk3_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_4⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk3_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_5⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk4_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_0⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk4_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_1⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk4_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_2⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk4_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_3⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk4_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_4⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk4_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_5⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk5_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_0⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk5_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_1⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk5_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_2⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk5_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_3⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk5_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_4⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk5_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_5⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk6_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_0⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk6_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_1⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk6_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_2⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk6_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_3⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk6_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_4⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk6_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_5⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk7_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_0⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk7_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_1⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk7_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_2⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk7_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_3⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk7_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_4⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk7_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_5⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk8_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_0⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk8_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_1⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk8_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_2⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk8_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_3⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk8_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_4⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Chunk8_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_5⟩
      root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq (by decide)
theorem root7Node116Step2Narrowing_checked :
    checkNarrowing table52 root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkNarrowing_flatten table52Scope [table52Rows0_0,table52Rows0_1,table52Rows0_2,table52Rows0_3,table52Rows0_4,table52Rows0_5,table52Rows1_0,table52Rows1_1,table52Rows1_2,table52Rows1_3,table52Rows1_4,table52Rows1_5,table52Rows2_0,table52Rows2_1,table52Rows2_2,table52Rows2_3,table52Rows2_4,table52Rows2_5,table52Rows3_0,table52Rows3_1,table52Rows3_2,table52Rows3_3,table52Rows3_4,table52Rows3_5,table52Rows4_0,table52Rows4_1,table52Rows4_2,table52Rows4_3,table52Rows4_4,table52Rows4_5,table52Rows5_0,table52Rows5_1,table52Rows5_2,table52Rows5_3,table52Rows5_4,table52Rows5_5,table52Rows6_0,table52Rows6_1,table52Rows6_2,table52Rows6_3,table52Rows6_4,table52Rows6_5,table52Rows7_0,table52Rows7_1,table52Rows7_2,table52Rows7_3,table52Rows7_4,table52Rows7_5,table52Rows8_0,table52Rows8_1,table52Rows8_2,table52Rows8_3,table52Rows8_4,table52Rows8_5]
    root7Node116Domains1 root7Node116Domains2 (by
      simp only [List.all_cons, List.all_nil, root7Node116Step2Chunk0_0_checked, root7Node116Step2Chunk0_1_checked, root7Node116Step2Chunk0_2_checked, root7Node116Step2Chunk0_3_checked, root7Node116Step2Chunk0_4_checked, root7Node116Step2Chunk0_5_checked, root7Node116Step2Chunk1_0_checked, root7Node116Step2Chunk1_1_checked, root7Node116Step2Chunk1_2_checked, root7Node116Step2Chunk1_3_checked, root7Node116Step2Chunk1_4_checked, root7Node116Step2Chunk1_5_checked, root7Node116Step2Chunk2_0_checked, root7Node116Step2Chunk2_1_checked, root7Node116Step2Chunk2_2_checked, root7Node116Step2Chunk2_3_checked, root7Node116Step2Chunk2_4_checked, root7Node116Step2Chunk2_5_checked, root7Node116Step2Chunk3_0_checked, root7Node116Step2Chunk3_1_checked, root7Node116Step2Chunk3_2_checked, root7Node116Step2Chunk3_3_checked, root7Node116Step2Chunk3_4_checked, root7Node116Step2Chunk3_5_checked, root7Node116Step2Chunk4_0_checked, root7Node116Step2Chunk4_1_checked, root7Node116Step2Chunk4_2_checked, root7Node116Step2Chunk4_3_checked, root7Node116Step2Chunk4_4_checked, root7Node116Step2Chunk4_5_checked, root7Node116Step2Chunk5_0_checked, root7Node116Step2Chunk5_1_checked, root7Node116Step2Chunk5_2_checked, root7Node116Step2Chunk5_3_checked, root7Node116Step2Chunk5_4_checked, root7Node116Step2Chunk5_5_checked, root7Node116Step2Chunk6_0_checked, root7Node116Step2Chunk6_1_checked, root7Node116Step2Chunk6_2_checked, root7Node116Step2Chunk6_3_checked, root7Node116Step2Chunk6_4_checked, root7Node116Step2Chunk6_5_checked, root7Node116Step2Chunk7_0_checked, root7Node116Step2Chunk7_1_checked, root7Node116Step2Chunk7_2_checked, root7Node116Step2Chunk7_3_checked, root7Node116Step2Chunk7_4_checked, root7Node116Step2Chunk7_5_checked, root7Node116Step2Chunk8_0_checked, root7Node116Step2Chunk8_1_checked, root7Node116Step2Chunk8_2_checked, root7Node116Step2Chunk8_3_checked, root7Node116Step2Chunk8_4_checked, root7Node116Step2Chunk8_5_checked, Bool.true_and])
theorem root7Node116Step2_checked :
    checkReplacement table52 root7Node116Domains1 root7Node116Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root7Node116Domains1 root7Node116Domains2
    root7Node116Domains1Fast root7Node116Domains2Fast
    root7Node116Domains1_fast_eq root7Node116Domains2_fast_eq
    root7Node116Step2Narrowing_checked (by decide)
theorem root7Node116Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node116Domains2 (.output 57) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
