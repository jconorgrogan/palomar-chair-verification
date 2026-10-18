module

public import SpectreFinite.RadiusFiveRoot5Part28
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node70Domains0 : Domains 91 State := restrict root5Node68Domains4 3 (7,4)
def root5Node70Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3),(7,3)]
  | 5 => some [(4,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1),(8,1)]
  | 10 => some [(0,1),(6,5)]
  | 11 => some [(0,4),(6,2)]
  | 12 => some [(1,4),(7,4)]
  | 13 => some [(5,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(1,0),(3,0)]
  | 19 => some [(2,1),(2,5)]
  | 20 => some [(0,2),(6,0)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(0,0)]
  | 28 => some [(3,2),(7,2)]
  | 29 => some [(4,0)]
  | 30 => some [(2,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3)]
  | 60 => some [(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(8,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(1,3)]
  | 71 => some [(8,2)]
  | 72 => some [(5,0)]
  | 73 => some [(4,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4)]
  | 79 => some [(5,4)]
  | 80 => some [(0,0)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3)]
  | 86 => some [(1,5)]
  | 87 => some [(6,1)]
  | 88 => some [(4,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root5Node70Domains0_fast_eq : root5Node70Domains0 = expandDomains root5Node70Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node70Domains0 v = expandDomains root5Node70Domains0Fast v from by decide) v
def root5Node70Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,2)]
  | 6 => [(8,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(1,4)]
  | 13 => [(5,3)]
  | 14 => [(5,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(3,0)]
  | 19 => [(2,5)]
  | 20 => [(6,0)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(0,0)]
  | 28 => [(7,2)]
  | 29 => [(4,0)]
  | 30 => [(2,5)]
  | 31 => [(6,0)]
  | 32 => [(7,1)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(4,0)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(7,0)]
  | 48 => [(8,3)]
  | 49 => [(8,5)]
  | 50 => [(1,0)]
  | 51 => [(6,1)]
  | 52 => [(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(7,4)]
  | 59 => [(1,3)]
  | 60 => [(8,2)]
  | 61 => [(8,3)]
  | 62 => [(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(8,1)]
  | 68 => [(6,5)]
  | 69 => [(0,4)]
  | 70 => [(1,3)]
  | 71 => [(8,2)]
  | 72 => [(5,0)]
  | 73 => [(4,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(8,5)]
  | 77 => [(7,0)]
  | 78 => [(0,4)]
  | 79 => [(5,4)]
  | 80 => [(0,0)]
  | 81 => [(7,2)]
  | 82 => [(7,4)]
  | 83 => [(6,3)]
  | 84 => [(7,2)]
  | 85 => [(4,3)]
  | 86 => [(1,5)]
  | 87 => [(6,1)]
  | 88 => [(4,1)]
  | 89 => [(0,2)]
  | _ => [(1,1)]
def root5Node70Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(1,4)]
  | 13 => some [(5,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(3,0)]
  | 19 => some [(2,5)]
  | 20 => some [(6,0)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(0,0)]
  | 28 => some [(7,2)]
  | 29 => some [(4,0)]
  | 30 => some [(2,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3)]
  | 60 => some [(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(8,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(1,3)]
  | 71 => some [(8,2)]
  | 72 => some [(5,0)]
  | 73 => some [(4,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4)]
  | 79 => some [(5,4)]
  | 80 => some [(0,0)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3)]
  | 86 => some [(1,5)]
  | 87 => some [(6,1)]
  | 88 => some [(4,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root5Node70Domains1_fast_eq : root5Node70Domains1 = expandDomains root5Node70Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node70Domains1 v = expandDomains root5Node70Domains1Fast v from by decide) v
theorem root5Node70Step1Chunk0_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_0⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk0_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_1⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk0_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_2⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk0_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_3⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk0_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_4⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk0_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_5⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk1_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_0⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk1_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_1⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk1_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_2⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk1_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_3⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk1_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_4⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk1_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_5⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk2_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_0⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk2_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_1⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk2_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_2⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk2_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_3⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk2_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_4⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk2_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_5⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk3_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_0⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk3_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_1⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk3_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_2⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk3_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_3⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk3_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_4⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk3_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_5⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk4_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_0⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk4_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_1⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk4_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_2⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk4_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_3⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk4_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_4⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk4_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_5⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk5_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_0⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk5_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_1⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk5_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_2⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk5_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_3⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk5_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_4⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk5_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_5⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk6_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_0⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk6_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_1⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk6_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_2⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk6_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_3⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk6_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_4⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk6_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_5⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk7_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_0⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk7_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_1⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk7_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_2⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk7_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_3⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk7_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_4⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk7_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_5⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk8_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_0⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk8_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_1⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk8_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_2⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk8_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_3⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk8_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_4⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Chunk8_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_5⟩
      root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq (by decide)
theorem root5Node70Step1Narrowing_checked :
    checkNarrowing table3 root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkNarrowing_flatten table3Scope [table3Rows0_0,table3Rows0_1,table3Rows0_2,table3Rows0_3,table3Rows0_4,table3Rows0_5,table3Rows1_0,table3Rows1_1,table3Rows1_2,table3Rows1_3,table3Rows1_4,table3Rows1_5,table3Rows2_0,table3Rows2_1,table3Rows2_2,table3Rows2_3,table3Rows2_4,table3Rows2_5,table3Rows3_0,table3Rows3_1,table3Rows3_2,table3Rows3_3,table3Rows3_4,table3Rows3_5,table3Rows4_0,table3Rows4_1,table3Rows4_2,table3Rows4_3,table3Rows4_4,table3Rows4_5,table3Rows5_0,table3Rows5_1,table3Rows5_2,table3Rows5_3,table3Rows5_4,table3Rows5_5,table3Rows6_0,table3Rows6_1,table3Rows6_2,table3Rows6_3,table3Rows6_4,table3Rows6_5,table3Rows7_0,table3Rows7_1,table3Rows7_2,table3Rows7_3,table3Rows7_4,table3Rows7_5,table3Rows8_0,table3Rows8_1,table3Rows8_2,table3Rows8_3,table3Rows8_4,table3Rows8_5]
    root5Node70Domains0 root5Node70Domains1 (by
      simp only [List.all_cons, List.all_nil, root5Node70Step1Chunk0_0_checked, root5Node70Step1Chunk0_1_checked, root5Node70Step1Chunk0_2_checked, root5Node70Step1Chunk0_3_checked, root5Node70Step1Chunk0_4_checked, root5Node70Step1Chunk0_5_checked, root5Node70Step1Chunk1_0_checked, root5Node70Step1Chunk1_1_checked, root5Node70Step1Chunk1_2_checked, root5Node70Step1Chunk1_3_checked, root5Node70Step1Chunk1_4_checked, root5Node70Step1Chunk1_5_checked, root5Node70Step1Chunk2_0_checked, root5Node70Step1Chunk2_1_checked, root5Node70Step1Chunk2_2_checked, root5Node70Step1Chunk2_3_checked, root5Node70Step1Chunk2_4_checked, root5Node70Step1Chunk2_5_checked, root5Node70Step1Chunk3_0_checked, root5Node70Step1Chunk3_1_checked, root5Node70Step1Chunk3_2_checked, root5Node70Step1Chunk3_3_checked, root5Node70Step1Chunk3_4_checked, root5Node70Step1Chunk3_5_checked, root5Node70Step1Chunk4_0_checked, root5Node70Step1Chunk4_1_checked, root5Node70Step1Chunk4_2_checked, root5Node70Step1Chunk4_3_checked, root5Node70Step1Chunk4_4_checked, root5Node70Step1Chunk4_5_checked, root5Node70Step1Chunk5_0_checked, root5Node70Step1Chunk5_1_checked, root5Node70Step1Chunk5_2_checked, root5Node70Step1Chunk5_3_checked, root5Node70Step1Chunk5_4_checked, root5Node70Step1Chunk5_5_checked, root5Node70Step1Chunk6_0_checked, root5Node70Step1Chunk6_1_checked, root5Node70Step1Chunk6_2_checked, root5Node70Step1Chunk6_3_checked, root5Node70Step1Chunk6_4_checked, root5Node70Step1Chunk6_5_checked, root5Node70Step1Chunk7_0_checked, root5Node70Step1Chunk7_1_checked, root5Node70Step1Chunk7_2_checked, root5Node70Step1Chunk7_3_checked, root5Node70Step1Chunk7_4_checked, root5Node70Step1Chunk7_5_checked, root5Node70Step1Chunk8_0_checked, root5Node70Step1Chunk8_1_checked, root5Node70Step1Chunk8_2_checked, root5Node70Step1Chunk8_3_checked, root5Node70Step1Chunk8_4_checked, root5Node70Step1Chunk8_5_checked, Bool.true_and])
theorem root5Node70Step1_checked :
    checkReplacement table3 root5Node70Domains0 root5Node70Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root5Node70Domains0 root5Node70Domains1
    root5Node70Domains0Fast root5Node70Domains1Fast
    root5Node70Domains0_fast_eq root5Node70Domains1_fast_eq
    root5Node70Step1Narrowing_checked (by decide)
theorem root5Node70Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node70Domains1 (.output 35) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
