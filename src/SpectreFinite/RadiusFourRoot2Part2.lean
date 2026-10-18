module

public import SpectreFinite.RadiusFourRoot2Part1
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable0
public import SpectreFinite.RadiusFourTable16
public import SpectreFinite.RadiusFourTable35

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root2Node6Domains0 : Domains 61 State := restrict root2Node5Domains1 50 (1,2)
def root2Node6Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(6,0)]
  | 2 => some [(7,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(1,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(7,0)]
  | 20 => some [(4,3)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(1,4)]
  | 29 => some [(0,5)]
  | 30 => some [(2,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(8,3)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(1,2)]
  | 51 => some [(8,4)]
  | 52 => some [(0,0)]
  | 53 => some [(7,2)]
  | 54 => some [(4,0)]
  | 55 => some [(7,3)]
  | 56 => some [(7,1),(8,1)]
  | 57 => some [(1,5)]
  | 58 => some [(6,1)]
  | 59 => some [(5,1)]
  | _ => some [(0,1)]
theorem root2Node6Domains0_fast_eq : root2Node6Domains0 = expandDomains root2Node6Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root2Node6Domains0 v = expandDomains root2Node6Domains0Fast v from by decide) v
def root2Node6Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(6,0)]
  | 2 => [(7,1)]
  | 3 => [(1,5)]
  | 4 => [(6,1)]
  | 5 => [(1,3)]
  | 6 => [(8,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => [(5,5)]
  | 19 => [(7,0)]
  | 20 => [(4,3)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(1,4)]
  | 29 => [(0,5)]
  | 30 => [(2,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(8,0)]
  | 34 => [(8,3)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(3,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(1,4)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(1,2)]
  | 51 => [(8,4)]
  | 52 => [(0,0)]
  | 53 => [(7,2)]
  | 54 => [(4,0)]
  | 55 => [(7,3)]
  | 56 => [(8,1)]
  | 57 => [(1,5)]
  | 58 => [(6,1)]
  | 59 => [(5,1)]
  | _ => [(0,1)]
def root2Node6Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(6,0)]
  | 2 => some [(7,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(1,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(7,0)]
  | 20 => some [(4,3)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(1,4)]
  | 29 => some [(0,5)]
  | 30 => some [(2,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(8,3)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(1,2)]
  | 51 => some [(8,4)]
  | 52 => some [(0,0)]
  | 53 => some [(7,2)]
  | 54 => some [(4,0)]
  | 55 => some [(7,3)]
  | 56 => some [(8,1)]
  | 57 => some [(1,5)]
  | 58 => some [(6,1)]
  | 59 => some [(5,1)]
  | _ => some [(0,1)]
theorem root2Node6Domains1_fast_eq : root2Node6Domains1 = expandDomains root2Node6Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root2Node6Domains1 v = expandDomains root2Node6Domains1Fast v from by decide) v
theorem root2Node6Step1Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root2Node6Domains0 root2Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node6Domains0 root2Node6Domains1
    root2Node6Domains0Fast root2Node6Domains1Fast
    root2Node6Domains0_fast_eq root2Node6Domains1_fast_eq (by decide)
theorem root2Node6Step1_checked :
    checkReplacement table35 root2Node6Domains0 root2Node6Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root2Node6Step1Chunk0_0_checked, root2Node6Step1Chunk0_1_checked, root2Node6Step1Chunk0_2_checked, root2Node6Step1Chunk0_3_checked, root2Node6Step1Chunk0_4_checked, root2Node6Step1Chunk0_5_checked, root2Node6Step1Chunk1_0_checked, root2Node6Step1Chunk1_1_checked, root2Node6Step1Chunk1_2_checked, root2Node6Step1Chunk1_3_checked, root2Node6Step1Chunk1_4_checked, root2Node6Step1Chunk1_5_checked, root2Node6Step1Chunk2_0_checked, root2Node6Step1Chunk2_1_checked, root2Node6Step1Chunk2_2_checked, root2Node6Step1Chunk2_3_checked, root2Node6Step1Chunk2_4_checked, root2Node6Step1Chunk2_5_checked, root2Node6Step1Chunk3_0_checked, root2Node6Step1Chunk3_1_checked, root2Node6Step1Chunk3_2_checked, root2Node6Step1Chunk3_3_checked, root2Node6Step1Chunk3_4_checked, root2Node6Step1Chunk3_5_checked, root2Node6Step1Chunk4_0_checked, root2Node6Step1Chunk4_1_checked, root2Node6Step1Chunk4_2_checked, root2Node6Step1Chunk4_3_checked, root2Node6Step1Chunk4_4_checked, root2Node6Step1Chunk4_5_checked, root2Node6Step1Chunk5_0_checked, root2Node6Step1Chunk5_1_checked, root2Node6Step1Chunk5_2_checked, root2Node6Step1Chunk5_3_checked, root2Node6Step1Chunk5_4_checked, root2Node6Step1Chunk5_5_checked, root2Node6Step1Chunk6_0_checked, root2Node6Step1Chunk6_1_checked, root2Node6Step1Chunk6_2_checked, root2Node6Step1Chunk6_3_checked, root2Node6Step1Chunk6_4_checked, root2Node6Step1Chunk6_5_checked, root2Node6Step1Chunk7_0_checked, root2Node6Step1Chunk7_1_checked, root2Node6Step1Chunk7_2_checked, root2Node6Step1Chunk7_3_checked, root2Node6Step1Chunk7_4_checked, root2Node6Step1Chunk7_5_checked, root2Node6Step1Chunk8_0_checked, root2Node6Step1Chunk8_1_checked, root2Node6Step1Chunk8_2_checked, root2Node6Step1Chunk8_3_checked, root2Node6Step1Chunk8_4_checked, root2Node6Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root2Node6Leaf_checked :
    checkCover 1 constraints root2Outputs root2Node6Domains1 (.output 2) = true := by decide
def root2Node7Domains0 : Domains 61 State := restrict root2Node5Domains1 50 (6,2)
def root2Node7Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(6,0)]
  | 2 => some [(7,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(1,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(7,0)]
  | 20 => some [(4,3)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(1,4)]
  | 29 => some [(0,5)]
  | 30 => some [(2,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(8,3)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(6,2)]
  | 51 => some [(8,4)]
  | 52 => some [(0,0)]
  | 53 => some [(7,2)]
  | 54 => some [(4,0)]
  | 55 => some [(7,3)]
  | 56 => some [(7,1),(8,1)]
  | 57 => some [(1,5)]
  | 58 => some [(6,1)]
  | 59 => some [(5,1)]
  | _ => some [(0,1)]
theorem root2Node7Domains0_fast_eq : root2Node7Domains0 = expandDomains root2Node7Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root2Node7Domains0 v = expandDomains root2Node7Domains0Fast v from by decide) v
def root2Node7Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(6,0)]
  | 2 => [(7,1)]
  | 3 => [(1,5)]
  | 4 => [(6,1)]
  | 5 => [(1,3)]
  | 6 => [(8,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => [(5,5)]
  | 19 => [(7,0)]
  | 20 => [(4,3)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(1,4)]
  | 29 => [(0,5)]
  | 30 => [(2,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(8,0)]
  | 34 => [(8,3)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(3,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(1,4)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(6,2)]
  | 51 => [(8,4)]
  | 52 => [(0,0)]
  | 53 => [(7,2)]
  | 54 => [(4,0)]
  | 55 => [(7,3)]
  | 56 => [(7,1)]
  | 57 => [(1,5)]
  | 58 => [(6,1)]
  | 59 => [(5,1)]
  | _ => [(0,1)]
def root2Node7Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(6,0)]
  | 2 => some [(7,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(1,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(7,0)]
  | 20 => some [(4,3)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(1,4)]
  | 29 => some [(0,5)]
  | 30 => some [(2,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(8,3)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(6,2)]
  | 51 => some [(8,4)]
  | 52 => some [(0,0)]
  | 53 => some [(7,2)]
  | 54 => some [(4,0)]
  | 55 => some [(7,3)]
  | 56 => some [(7,1)]
  | 57 => some [(1,5)]
  | 58 => some [(6,1)]
  | 59 => some [(5,1)]
  | _ => some [(0,1)]
theorem root2Node7Domains1_fast_eq : root2Node7Domains1 = expandDomains root2Node7Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root2Node7Domains1 v = expandDomains root2Node7Domains1Fast v from by decide) v
theorem root2Node7Step1Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root2Node7Domains0 root2Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node7Domains0 root2Node7Domains1
    root2Node7Domains0Fast root2Node7Domains1Fast
    root2Node7Domains0_fast_eq root2Node7Domains1_fast_eq (by decide)
theorem root2Node7Step1_checked :
    checkReplacement table35 root2Node7Domains0 root2Node7Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root2Node7Step1Chunk0_0_checked, root2Node7Step1Chunk0_1_checked, root2Node7Step1Chunk0_2_checked, root2Node7Step1Chunk0_3_checked, root2Node7Step1Chunk0_4_checked, root2Node7Step1Chunk0_5_checked, root2Node7Step1Chunk1_0_checked, root2Node7Step1Chunk1_1_checked, root2Node7Step1Chunk1_2_checked, root2Node7Step1Chunk1_3_checked, root2Node7Step1Chunk1_4_checked, root2Node7Step1Chunk1_5_checked, root2Node7Step1Chunk2_0_checked, root2Node7Step1Chunk2_1_checked, root2Node7Step1Chunk2_2_checked, root2Node7Step1Chunk2_3_checked, root2Node7Step1Chunk2_4_checked, root2Node7Step1Chunk2_5_checked, root2Node7Step1Chunk3_0_checked, root2Node7Step1Chunk3_1_checked, root2Node7Step1Chunk3_2_checked, root2Node7Step1Chunk3_3_checked, root2Node7Step1Chunk3_4_checked, root2Node7Step1Chunk3_5_checked, root2Node7Step1Chunk4_0_checked, root2Node7Step1Chunk4_1_checked, root2Node7Step1Chunk4_2_checked, root2Node7Step1Chunk4_3_checked, root2Node7Step1Chunk4_4_checked, root2Node7Step1Chunk4_5_checked, root2Node7Step1Chunk5_0_checked, root2Node7Step1Chunk5_1_checked, root2Node7Step1Chunk5_2_checked, root2Node7Step1Chunk5_3_checked, root2Node7Step1Chunk5_4_checked, root2Node7Step1Chunk5_5_checked, root2Node7Step1Chunk6_0_checked, root2Node7Step1Chunk6_1_checked, root2Node7Step1Chunk6_2_checked, root2Node7Step1Chunk6_3_checked, root2Node7Step1Chunk6_4_checked, root2Node7Step1Chunk6_5_checked, root2Node7Step1Chunk7_0_checked, root2Node7Step1Chunk7_1_checked, root2Node7Step1Chunk7_2_checked, root2Node7Step1Chunk7_3_checked, root2Node7Step1Chunk7_4_checked, root2Node7Step1Chunk7_5_checked, root2Node7Step1Chunk8_0_checked, root2Node7Step1Chunk8_1_checked, root2Node7Step1Chunk8_2_checked, root2Node7Step1Chunk8_3_checked, root2Node7Step1Chunk8_4_checked, root2Node7Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root2Node7Leaf_checked :
    checkCover 1 constraints root2Outputs root2Node7Domains1 (.output 3) = true := by decide
def root2Node8Domains0 : Domains 61 State := restrict root2Node0Domains5 0 (8,5)
def root2Node8Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,5)]
  | 1 => some [(1,0),(6,0)]
  | 2 => some [(7,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(1,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(7,0)]
  | 20 => some [(4,3)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(1,4)]
  | 29 => some [(0,5)]
  | 30 => some [(2,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(1,4),(6,4)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(1,2),(6,2)]
  | 51 => some [(8,4)]
  | 52 => some [(0,0)]
  | 53 => some [(7,2)]
  | 54 => some [(4,0)]
  | 55 => some [(7,3)]
  | 56 => some [(7,1),(8,1)]
  | 57 => some [(1,5)]
  | 58 => some [(6,1)]
  | 59 => some [(5,1)]
  | _ => some [(0,1)]
theorem root2Node8Domains0_fast_eq : root2Node8Domains0 = expandDomains root2Node8Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root2Node8Domains0 v = expandDomains root2Node8Domains0Fast v from by decide) v
def root2Node8Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(8,5)]
  | 1 => [(1,0)]
  | 2 => [(7,1)]
  | 3 => [(1,5)]
  | 4 => [(6,1)]
  | 5 => [(1,3)]
  | 6 => [(8,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => [(5,5)]
  | 19 => [(7,0)]
  | 20 => [(4,3)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(1,4)]
  | 29 => [(0,5)]
  | 30 => [(2,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(3,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(1,4),(6,4)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(1,2),(6,2)]
  | 51 => [(8,4)]
  | 52 => [(0,0)]
  | 53 => [(7,2)]
  | 54 => [(4,0)]
  | 55 => [(7,3)]
  | 56 => [(7,1),(8,1)]
  | 57 => [(1,5)]
  | 58 => [(6,1)]
  | 59 => [(5,1)]
  | _ => [(0,1)]
def root2Node8Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,5)]
  | 1 => some [(1,0)]
  | 2 => some [(7,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(1,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(7,0)]
  | 20 => some [(4,3)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(1,4)]
  | 29 => some [(0,5)]
  | 30 => some [(2,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(1,4),(6,4)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(1,2),(6,2)]
  | 51 => some [(8,4)]
  | 52 => some [(0,0)]
  | 53 => some [(7,2)]
  | 54 => some [(4,0)]
  | 55 => some [(7,3)]
  | 56 => some [(7,1),(8,1)]
  | 57 => some [(1,5)]
  | 58 => some [(6,1)]
  | 59 => some [(5,1)]
  | _ => some [(0,1)]
theorem root2Node8Domains1_fast_eq : root2Node8Domains1 = expandDomains root2Node8Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root2Node8Domains1 v = expandDomains root2Node8Domains1Fast v from by decide) v
theorem root2Node8Step1Chunk0_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_0⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk0_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_1⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk0_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_2⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk0_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_3⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk0_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_4⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk0_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_5⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk1_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_0⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk1_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_1⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk1_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_2⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk1_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_3⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk1_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_4⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk1_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_5⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk2_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_0⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk2_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_1⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk2_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_2⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk2_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_3⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk2_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_4⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk2_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_5⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk3_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_0⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk3_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_1⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk3_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_2⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk3_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_3⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk3_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_4⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk3_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_5⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk4_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_0⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk4_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_1⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk4_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_2⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk4_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_3⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk4_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_4⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk4_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_5⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk5_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_0⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk5_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_1⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk5_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_2⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk5_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_3⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk5_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_4⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk5_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_5⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk6_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_0⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk6_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_1⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk6_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_2⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk6_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_3⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk6_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_4⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk6_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_5⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk7_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_0⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk7_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_1⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk7_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_2⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk7_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_3⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk7_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_4⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk7_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_5⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk8_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_0⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk8_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_1⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk8_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_2⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk8_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_3⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk8_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_4⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1Chunk8_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_5⟩
      root2Node8Domains0 root2Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node8Domains0 root2Node8Domains1
    root2Node8Domains0Fast root2Node8Domains1Fast
    root2Node8Domains0_fast_eq root2Node8Domains1_fast_eq (by decide)
theorem root2Node8Step1_checked :
    checkReplacement table0 root2Node8Domains0 root2Node8Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root2Node8Step1Chunk0_0_checked, root2Node8Step1Chunk0_1_checked, root2Node8Step1Chunk0_2_checked, root2Node8Step1Chunk0_3_checked, root2Node8Step1Chunk0_4_checked, root2Node8Step1Chunk0_5_checked, root2Node8Step1Chunk1_0_checked, root2Node8Step1Chunk1_1_checked, root2Node8Step1Chunk1_2_checked, root2Node8Step1Chunk1_3_checked, root2Node8Step1Chunk1_4_checked, root2Node8Step1Chunk1_5_checked, root2Node8Step1Chunk2_0_checked, root2Node8Step1Chunk2_1_checked, root2Node8Step1Chunk2_2_checked, root2Node8Step1Chunk2_3_checked, root2Node8Step1Chunk2_4_checked, root2Node8Step1Chunk2_5_checked, root2Node8Step1Chunk3_0_checked, root2Node8Step1Chunk3_1_checked, root2Node8Step1Chunk3_2_checked, root2Node8Step1Chunk3_3_checked, root2Node8Step1Chunk3_4_checked, root2Node8Step1Chunk3_5_checked, root2Node8Step1Chunk4_0_checked, root2Node8Step1Chunk4_1_checked, root2Node8Step1Chunk4_2_checked, root2Node8Step1Chunk4_3_checked, root2Node8Step1Chunk4_4_checked, root2Node8Step1Chunk4_5_checked, root2Node8Step1Chunk5_0_checked, root2Node8Step1Chunk5_1_checked, root2Node8Step1Chunk5_2_checked, root2Node8Step1Chunk5_3_checked, root2Node8Step1Chunk5_4_checked, root2Node8Step1Chunk5_5_checked, root2Node8Step1Chunk6_0_checked, root2Node8Step1Chunk6_1_checked, root2Node8Step1Chunk6_2_checked, root2Node8Step1Chunk6_3_checked, root2Node8Step1Chunk6_4_checked, root2Node8Step1Chunk6_5_checked, root2Node8Step1Chunk7_0_checked, root2Node8Step1Chunk7_1_checked, root2Node8Step1Chunk7_2_checked, root2Node8Step1Chunk7_3_checked, root2Node8Step1Chunk7_4_checked, root2Node8Step1Chunk7_5_checked, root2Node8Step1Chunk8_0_checked, root2Node8Step1Chunk8_1_checked, root2Node8Step1Chunk8_2_checked, root2Node8Step1Chunk8_3_checked, root2Node8Step1Chunk8_4_checked, root2Node8Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root2Node9Domains0 : Domains 61 State := restrict root2Node8Domains1 34 (7,3)
def root2Node9Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,5)]
  | 1 => some [(1,0)]
  | 2 => some [(7,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(1,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(7,0)]
  | 20 => some [(4,3)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(1,4)]
  | 29 => some [(0,5)]
  | 30 => some [(2,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(1,4),(6,4)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(1,2),(6,2)]
  | 51 => some [(8,4)]
  | 52 => some [(0,0)]
  | 53 => some [(7,2)]
  | 54 => some [(4,0)]
  | 55 => some [(7,3)]
  | 56 => some [(7,1),(8,1)]
  | 57 => some [(1,5)]
  | 58 => some [(6,1)]
  | 59 => some [(5,1)]
  | _ => some [(0,1)]
theorem root2Node9Domains0_fast_eq : root2Node9Domains0 = expandDomains root2Node9Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root2Node9Domains0 v = expandDomains root2Node9Domains0Fast v from by decide) v
def root2Node9Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(8,5)]
  | 1 => [(1,0)]
  | 2 => [(7,1)]
  | 3 => [(1,5)]
  | 4 => [(6,1)]
  | 5 => [(1,3)]
  | 6 => [(8,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => [(5,5)]
  | 19 => [(7,0)]
  | 20 => [(4,3)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(1,4)]
  | 29 => [(0,5)]
  | 30 => [(2,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(8,0)]
  | 34 => [(7,3)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(3,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(6,4)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(1,2),(6,2)]
  | 51 => [(8,4)]
  | 52 => [(0,0)]
  | 53 => [(7,2)]
  | 54 => [(4,0)]
  | 55 => [(7,3)]
  | 56 => [(7,1),(8,1)]
  | 57 => [(1,5)]
  | 58 => [(6,1)]
  | 59 => [(5,1)]
  | _ => [(0,1)]
def root2Node9Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,5)]
  | 1 => some [(1,0)]
  | 2 => some [(7,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(1,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(7,0)]
  | 20 => some [(4,3)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(1,4)]
  | 29 => some [(0,5)]
  | 30 => some [(2,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(6,4)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(1,2),(6,2)]
  | 51 => some [(8,4)]
  | 52 => some [(0,0)]
  | 53 => some [(7,2)]
  | 54 => some [(4,0)]
  | 55 => some [(7,3)]
  | 56 => some [(7,1),(8,1)]
  | 57 => some [(1,5)]
  | 58 => some [(6,1)]
  | 59 => some [(5,1)]
  | _ => some [(0,1)]
theorem root2Node9Domains1_fast_eq : root2Node9Domains1 = expandDomains root2Node9Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root2Node9Domains1 v = expandDomains root2Node9Domains1Fast v from by decide) v
theorem root2Node9Step1Chunk0_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_0⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk0_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_1⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk0_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_2⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk0_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_3⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk0_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_4⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk0_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_5⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk1_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_0⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk1_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_1⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk1_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_2⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk1_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_3⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk1_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_4⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk1_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_5⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk2_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_0⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk2_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_1⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk2_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_2⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk2_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_3⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk2_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_4⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk2_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_5⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk3_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_0⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk3_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_1⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk3_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_2⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk3_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_3⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk3_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_4⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk3_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_5⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk4_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_0⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk4_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_1⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk4_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_2⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk4_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_3⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk4_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_4⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk4_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_5⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk5_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_0⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk5_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_1⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk5_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_2⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk5_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_3⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk5_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_4⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk5_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_5⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk6_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_0⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk6_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_1⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk6_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_2⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk6_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_3⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk6_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_4⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk6_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_5⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk7_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_0⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk7_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_1⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk7_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_2⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk7_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_3⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk7_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_4⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk7_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_5⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk8_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_0⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk8_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_1⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk8_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_2⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk8_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_3⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk8_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_4⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1Chunk8_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_5⟩
      root2Node9Domains0 root2Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node9Domains0 root2Node9Domains1
    root2Node9Domains0Fast root2Node9Domains1Fast
    root2Node9Domains0_fast_eq root2Node9Domains1_fast_eq (by decide)
theorem root2Node9Step1_checked :
    checkReplacement table16 root2Node9Domains0 root2Node9Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root2Node9Step1Chunk0_0_checked, root2Node9Step1Chunk0_1_checked, root2Node9Step1Chunk0_2_checked, root2Node9Step1Chunk0_3_checked, root2Node9Step1Chunk0_4_checked, root2Node9Step1Chunk0_5_checked, root2Node9Step1Chunk1_0_checked, root2Node9Step1Chunk1_1_checked, root2Node9Step1Chunk1_2_checked, root2Node9Step1Chunk1_3_checked, root2Node9Step1Chunk1_4_checked, root2Node9Step1Chunk1_5_checked, root2Node9Step1Chunk2_0_checked, root2Node9Step1Chunk2_1_checked, root2Node9Step1Chunk2_2_checked, root2Node9Step1Chunk2_3_checked, root2Node9Step1Chunk2_4_checked, root2Node9Step1Chunk2_5_checked, root2Node9Step1Chunk3_0_checked, root2Node9Step1Chunk3_1_checked, root2Node9Step1Chunk3_2_checked, root2Node9Step1Chunk3_3_checked, root2Node9Step1Chunk3_4_checked, root2Node9Step1Chunk3_5_checked, root2Node9Step1Chunk4_0_checked, root2Node9Step1Chunk4_1_checked, root2Node9Step1Chunk4_2_checked, root2Node9Step1Chunk4_3_checked, root2Node9Step1Chunk4_4_checked, root2Node9Step1Chunk4_5_checked, root2Node9Step1Chunk5_0_checked, root2Node9Step1Chunk5_1_checked, root2Node9Step1Chunk5_2_checked, root2Node9Step1Chunk5_3_checked, root2Node9Step1Chunk5_4_checked, root2Node9Step1Chunk5_5_checked, root2Node9Step1Chunk6_0_checked, root2Node9Step1Chunk6_1_checked, root2Node9Step1Chunk6_2_checked, root2Node9Step1Chunk6_3_checked, root2Node9Step1Chunk6_4_checked, root2Node9Step1Chunk6_5_checked, root2Node9Step1Chunk7_0_checked, root2Node9Step1Chunk7_1_checked, root2Node9Step1Chunk7_2_checked, root2Node9Step1Chunk7_3_checked, root2Node9Step1Chunk7_4_checked, root2Node9Step1Chunk7_5_checked, root2Node9Step1Chunk8_0_checked, root2Node9Step1Chunk8_1_checked, root2Node9Step1Chunk8_2_checked, root2Node9Step1Chunk8_3_checked, root2Node9Step1Chunk8_4_checked, root2Node9Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root2Node10Domains0 : Domains 61 State := restrict root2Node9Domains1 50 (1,2)
def root2Node10Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,5)]
  | 1 => some [(1,0)]
  | 2 => some [(7,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(1,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(7,0)]
  | 20 => some [(4,3)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(1,4)]
  | 29 => some [(0,5)]
  | 30 => some [(2,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(6,4)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(1,2)]
  | 51 => some [(8,4)]
  | 52 => some [(0,0)]
  | 53 => some [(7,2)]
  | 54 => some [(4,0)]
  | 55 => some [(7,3)]
  | 56 => some [(7,1),(8,1)]
  | 57 => some [(1,5)]
  | 58 => some [(6,1)]
  | 59 => some [(5,1)]
  | _ => some [(0,1)]
theorem root2Node10Domains0_fast_eq : root2Node10Domains0 = expandDomains root2Node10Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root2Node10Domains0 v = expandDomains root2Node10Domains0Fast v from by decide) v
def root2Node10Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(8,5)]
  | 1 => [(1,0)]
  | 2 => [(7,1)]
  | 3 => [(1,5)]
  | 4 => [(6,1)]
  | 5 => [(1,3)]
  | 6 => [(8,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => [(5,5)]
  | 19 => [(7,0)]
  | 20 => [(4,3)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(1,4)]
  | 29 => [(0,5)]
  | 30 => [(2,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(8,0)]
  | 34 => [(7,3)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(3,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(6,4)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(1,2)]
  | 51 => [(8,4)]
  | 52 => [(0,0)]
  | 53 => [(7,2)]
  | 54 => [(4,0)]
  | 55 => [(7,3)]
  | 56 => [(8,1)]
  | 57 => [(1,5)]
  | 58 => [(6,1)]
  | 59 => [(5,1)]
  | _ => [(0,1)]
def root2Node10Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,5)]
  | 1 => some [(1,0)]
  | 2 => some [(7,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(1,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(7,0)]
  | 20 => some [(4,3)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(1,4)]
  | 29 => some [(0,5)]
  | 30 => some [(2,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(6,4)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(1,2)]
  | 51 => some [(8,4)]
  | 52 => some [(0,0)]
  | 53 => some [(7,2)]
  | 54 => some [(4,0)]
  | 55 => some [(7,3)]
  | 56 => some [(8,1)]
  | 57 => some [(1,5)]
  | 58 => some [(6,1)]
  | 59 => some [(5,1)]
  | _ => some [(0,1)]
theorem root2Node10Domains1_fast_eq : root2Node10Domains1 = expandDomains root2Node10Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root2Node10Domains1 v = expandDomains root2Node10Domains1Fast v from by decide) v
theorem root2Node10Step1Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root2Node10Domains0 root2Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node10Domains0 root2Node10Domains1
    root2Node10Domains0Fast root2Node10Domains1Fast
    root2Node10Domains0_fast_eq root2Node10Domains1_fast_eq (by decide)
theorem root2Node10Step1_checked :
    checkReplacement table35 root2Node10Domains0 root2Node10Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root2Node10Step1Chunk0_0_checked, root2Node10Step1Chunk0_1_checked, root2Node10Step1Chunk0_2_checked, root2Node10Step1Chunk0_3_checked, root2Node10Step1Chunk0_4_checked, root2Node10Step1Chunk0_5_checked, root2Node10Step1Chunk1_0_checked, root2Node10Step1Chunk1_1_checked, root2Node10Step1Chunk1_2_checked, root2Node10Step1Chunk1_3_checked, root2Node10Step1Chunk1_4_checked, root2Node10Step1Chunk1_5_checked, root2Node10Step1Chunk2_0_checked, root2Node10Step1Chunk2_1_checked, root2Node10Step1Chunk2_2_checked, root2Node10Step1Chunk2_3_checked, root2Node10Step1Chunk2_4_checked, root2Node10Step1Chunk2_5_checked, root2Node10Step1Chunk3_0_checked, root2Node10Step1Chunk3_1_checked, root2Node10Step1Chunk3_2_checked, root2Node10Step1Chunk3_3_checked, root2Node10Step1Chunk3_4_checked, root2Node10Step1Chunk3_5_checked, root2Node10Step1Chunk4_0_checked, root2Node10Step1Chunk4_1_checked, root2Node10Step1Chunk4_2_checked, root2Node10Step1Chunk4_3_checked, root2Node10Step1Chunk4_4_checked, root2Node10Step1Chunk4_5_checked, root2Node10Step1Chunk5_0_checked, root2Node10Step1Chunk5_1_checked, root2Node10Step1Chunk5_2_checked, root2Node10Step1Chunk5_3_checked, root2Node10Step1Chunk5_4_checked, root2Node10Step1Chunk5_5_checked, root2Node10Step1Chunk6_0_checked, root2Node10Step1Chunk6_1_checked, root2Node10Step1Chunk6_2_checked, root2Node10Step1Chunk6_3_checked, root2Node10Step1Chunk6_4_checked, root2Node10Step1Chunk6_5_checked, root2Node10Step1Chunk7_0_checked, root2Node10Step1Chunk7_1_checked, root2Node10Step1Chunk7_2_checked, root2Node10Step1Chunk7_3_checked, root2Node10Step1Chunk7_4_checked, root2Node10Step1Chunk7_5_checked, root2Node10Step1Chunk8_0_checked, root2Node10Step1Chunk8_1_checked, root2Node10Step1Chunk8_2_checked, root2Node10Step1Chunk8_3_checked, root2Node10Step1Chunk8_4_checked, root2Node10Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root2Node10Leaf_checked :
    checkCover 1 constraints root2Outputs root2Node10Domains1 (.output 4) = true := by decide
end SpectreFinite.HexSearch.RadiusFour
