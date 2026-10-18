module

public import SpectreFinite.RadiusFourRoot1Part3
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable21
public import SpectreFinite.RadiusFourTable38
public import SpectreFinite.RadiusFourTable39
public import SpectreFinite.RadiusFourTable5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node9Domains0 : Domains 61 State := restrict root1Node7Domains1 58 (6,3)
def root1Node9Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(7,5)]
  | 7 => some [(0,3)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(7,4)]
  | 12 => some [(6,3)]
  | 13 => some [(2,2)]
  | 14 => some [(3,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(8,3)]
  | 18 => some [(4,1)]
  | 19 => some [(0,2)]
  | 20 => some [(1,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(7,3)]
  | 27 => some [(5,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(6,3)]
  | 59 => some [(7,2),(8,2)]
  | _ => some [(4,0),(8,0)]
theorem root1Node9Domains0_fast_eq : root1Node9Domains0 = expandDomains root1Node9Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node9Domains0 v = expandDomains root1Node9Domains0Fast v from by decide) v
def root1Node9Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(4,3)]
  | 6 => [(7,5)]
  | 7 => [(0,3)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(7,4)]
  | 12 => [(6,3)]
  | 13 => [(2,2)]
  | 14 => [(3,3)]
  | 15 => [(5,2)]
  | 16 => [(8,0)]
  | 17 => [(8,3)]
  | 18 => [(4,1)]
  | 19 => [(0,2)]
  | 20 => [(1,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(7,3)]
  | 27 => [(5,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(6,0)]
  | 34 => [(7,1)]
  | 35 => [(1,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(8,2)]
  | 42 => [(8,0)]
  | 43 => [(8,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(8,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(8,5)]
  | 54 => [(1,0)]
  | 55 => [(7,1)]
  | 56 => [(7,2)]
  | 57 => [(7,4)]
  | 58 => [(6,3)]
  | 59 => [(7,2)]
  | _ => [(4,0)]
def root1Node9Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(7,5)]
  | 7 => some [(0,3)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(7,4)]
  | 12 => some [(6,3)]
  | 13 => some [(2,2)]
  | 14 => some [(3,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(8,3)]
  | 18 => some [(4,1)]
  | 19 => some [(0,2)]
  | 20 => some [(1,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(7,3)]
  | 27 => some [(5,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(6,3)]
  | 59 => some [(7,2)]
  | _ => some [(4,0)]
theorem root1Node9Domains1_fast_eq : root1Node9Domains1 = expandDomains root1Node9Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node9Domains1 v = expandDomains root1Node9Domains1Fast v from by decide) v
theorem root1Node9Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root1Node9Domains0 root1Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains0 root1Node9Domains1
    root1Node9Domains0Fast root1Node9Domains1Fast
    root1Node9Domains0_fast_eq root1Node9Domains1_fast_eq (by decide)
theorem root1Node9Step1_checked :
    checkReplacement table39 root1Node9Domains0 root1Node9Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node9Step1Chunk0_0_checked, root1Node9Step1Chunk0_1_checked, root1Node9Step1Chunk0_2_checked, root1Node9Step1Chunk0_3_checked, root1Node9Step1Chunk0_4_checked, root1Node9Step1Chunk0_5_checked, root1Node9Step1Chunk1_0_checked, root1Node9Step1Chunk1_1_checked, root1Node9Step1Chunk1_2_checked, root1Node9Step1Chunk1_3_checked, root1Node9Step1Chunk1_4_checked, root1Node9Step1Chunk1_5_checked, root1Node9Step1Chunk2_0_checked, root1Node9Step1Chunk2_1_checked, root1Node9Step1Chunk2_2_checked, root1Node9Step1Chunk2_3_checked, root1Node9Step1Chunk2_4_checked, root1Node9Step1Chunk2_5_checked, root1Node9Step1Chunk3_0_checked, root1Node9Step1Chunk3_1_checked, root1Node9Step1Chunk3_2_checked, root1Node9Step1Chunk3_3_checked, root1Node9Step1Chunk3_4_checked, root1Node9Step1Chunk3_5_checked, root1Node9Step1Chunk4_0_checked, root1Node9Step1Chunk4_1_checked, root1Node9Step1Chunk4_2_checked, root1Node9Step1Chunk4_3_checked, root1Node9Step1Chunk4_4_checked, root1Node9Step1Chunk4_5_checked, root1Node9Step1Chunk5_0_checked, root1Node9Step1Chunk5_1_checked, root1Node9Step1Chunk5_2_checked, root1Node9Step1Chunk5_3_checked, root1Node9Step1Chunk5_4_checked, root1Node9Step1Chunk5_5_checked, root1Node9Step1Chunk6_0_checked, root1Node9Step1Chunk6_1_checked, root1Node9Step1Chunk6_2_checked, root1Node9Step1Chunk6_3_checked, root1Node9Step1Chunk6_4_checked, root1Node9Step1Chunk6_5_checked, root1Node9Step1Chunk7_0_checked, root1Node9Step1Chunk7_1_checked, root1Node9Step1Chunk7_2_checked, root1Node9Step1Chunk7_3_checked, root1Node9Step1Chunk7_4_checked, root1Node9Step1Chunk7_5_checked, root1Node9Step1Chunk8_0_checked, root1Node9Step1Chunk8_1_checked, root1Node9Step1Chunk8_2_checked, root1Node9Step1Chunk8_3_checked, root1Node9Step1Chunk8_4_checked, root1Node9Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root1Node9Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node9Domains1 (.output 3) = true := by decide
def root1Node10Domains0 : Domains 61 State := restrict root1Node4Domains2 35 (6,2)
def root1Node10Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(7,5)]
  | 7 => some [(0,3)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(7,4)]
  | 12 => some [(6,3)]
  | 13 => some [(2,2)]
  | 14 => some [(3,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(8,3)]
  | 18 => some [(4,1)]
  | 19 => some [(0,2)]
  | 20 => some [(1,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(7,3)]
  | 27 => some [(5,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0),(8,0)]
  | 43 => some [(7,1),(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(4,5),(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3),(6,3)]
  | 59 => some [(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(8,0)]
theorem root1Node10Domains0_fast_eq : root1Node10Domains0 = expandDomains root1Node10Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node10Domains0 v = expandDomains root1Node10Domains0Fast v from by decide) v
def root1Node10Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(4,3)]
  | 6 => [(7,5)]
  | 7 => [(0,3)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(7,4)]
  | 12 => [(6,3)]
  | 13 => [(2,2)]
  | 14 => [(3,3)]
  | 15 => [(5,2)]
  | 16 => [(8,0)]
  | 17 => [(8,3)]
  | 18 => [(4,1)]
  | 19 => [(0,2)]
  | 20 => [(1,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(7,3)]
  | 27 => [(5,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(6,0)]
  | 34 => [(7,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(8,2)]
  | 42 => [(5,0),(8,0)]
  | 43 => [(7,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(4,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(8,5)]
  | 54 => [(1,0)]
  | 55 => [(7,1)]
  | 56 => [(7,2)]
  | 57 => [(7,4)]
  | 58 => [(6,3)]
  | 59 => [(7,2)]
  | _ => [(4,0),(5,0),(8,0)]
def root1Node10Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(7,5)]
  | 7 => some [(0,3)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(7,4)]
  | 12 => some [(6,3)]
  | 13 => some [(2,2)]
  | 14 => some [(3,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(8,3)]
  | 18 => some [(4,1)]
  | 19 => some [(0,2)]
  | 20 => some [(1,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(7,3)]
  | 27 => some [(5,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0),(8,0)]
  | 43 => some [(7,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(4,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(6,3)]
  | 59 => some [(7,2)]
  | _ => some [(4,0),(5,0),(8,0)]
theorem root1Node10Domains1_fast_eq : root1Node10Domains1 = expandDomains root1Node10Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node10Domains1 v = expandDomains root1Node10Domains1Fast v from by decide) v
theorem root1Node10Step1Chunk0_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_0⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk0_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_1⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk0_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_2⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk0_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_3⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk0_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_4⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk0_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_5⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk1_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_0⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk1_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_1⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk1_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_2⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk1_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_3⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk1_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_4⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk1_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_5⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk2_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_0⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk2_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_1⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk2_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_2⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk2_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_3⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk2_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_4⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk2_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_5⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk3_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_0⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk3_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_1⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk3_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_2⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk3_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_3⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk3_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_4⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk3_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_5⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk4_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_0⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk4_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_1⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk4_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_2⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk4_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_3⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk4_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_4⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk4_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_5⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk5_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_0⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk5_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_1⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk5_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_2⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk5_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_3⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk5_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_4⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk5_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_5⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk6_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_0⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk6_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_1⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk6_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_2⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk6_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_3⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk6_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_4⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk6_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_5⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk7_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_0⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk7_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_1⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk7_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_2⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk7_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_3⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk7_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_4⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk7_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_5⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk8_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_0⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk8_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_1⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk8_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_2⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk8_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_3⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk8_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_4⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk8_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_5⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1_checked :
    checkReplacement table38 root1Node10Domains0 root1Node10Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node10Step1Chunk0_0_checked, root1Node10Step1Chunk0_1_checked, root1Node10Step1Chunk0_2_checked, root1Node10Step1Chunk0_3_checked, root1Node10Step1Chunk0_4_checked, root1Node10Step1Chunk0_5_checked, root1Node10Step1Chunk1_0_checked, root1Node10Step1Chunk1_1_checked, root1Node10Step1Chunk1_2_checked, root1Node10Step1Chunk1_3_checked, root1Node10Step1Chunk1_4_checked, root1Node10Step1Chunk1_5_checked, root1Node10Step1Chunk2_0_checked, root1Node10Step1Chunk2_1_checked, root1Node10Step1Chunk2_2_checked, root1Node10Step1Chunk2_3_checked, root1Node10Step1Chunk2_4_checked, root1Node10Step1Chunk2_5_checked, root1Node10Step1Chunk3_0_checked, root1Node10Step1Chunk3_1_checked, root1Node10Step1Chunk3_2_checked, root1Node10Step1Chunk3_3_checked, root1Node10Step1Chunk3_4_checked, root1Node10Step1Chunk3_5_checked, root1Node10Step1Chunk4_0_checked, root1Node10Step1Chunk4_1_checked, root1Node10Step1Chunk4_2_checked, root1Node10Step1Chunk4_3_checked, root1Node10Step1Chunk4_4_checked, root1Node10Step1Chunk4_5_checked, root1Node10Step1Chunk5_0_checked, root1Node10Step1Chunk5_1_checked, root1Node10Step1Chunk5_2_checked, root1Node10Step1Chunk5_3_checked, root1Node10Step1Chunk5_4_checked, root1Node10Step1Chunk5_5_checked, root1Node10Step1Chunk6_0_checked, root1Node10Step1Chunk6_1_checked, root1Node10Step1Chunk6_2_checked, root1Node10Step1Chunk6_3_checked, root1Node10Step1Chunk6_4_checked, root1Node10Step1Chunk6_5_checked, root1Node10Step1Chunk7_0_checked, root1Node10Step1Chunk7_1_checked, root1Node10Step1Chunk7_2_checked, root1Node10Step1Chunk7_3_checked, root1Node10Step1Chunk7_4_checked, root1Node10Step1Chunk7_5_checked, root1Node10Step1Chunk8_0_checked, root1Node10Step1Chunk8_1_checked, root1Node10Step1Chunk8_2_checked, root1Node10Step1Chunk8_3_checked, root1Node10Step1Chunk8_4_checked, root1Node10Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node10Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(4,3)]
  | 6 => [(7,5)]
  | 7 => [(0,3)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(7,4)]
  | 12 => [(6,3)]
  | 13 => [(2,2)]
  | 14 => [(3,3)]
  | 15 => [(5,2)]
  | 16 => [(8,0)]
  | 17 => [(8,3)]
  | 18 => [(4,1)]
  | 19 => [(0,2)]
  | 20 => [(1,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(7,3)]
  | 27 => [(5,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(6,0)]
  | 34 => [(7,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(8,2)]
  | 42 => [(8,0)]
  | 43 => [(7,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(4,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(8,5)]
  | 54 => [(1,0)]
  | 55 => [(7,1)]
  | 56 => [(7,2)]
  | 57 => [(7,4)]
  | 58 => [(6,3)]
  | 59 => [(7,2)]
  | _ => [(4,0)]
def root1Node10Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(7,5)]
  | 7 => some [(0,3)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(7,4)]
  | 12 => some [(6,3)]
  | 13 => some [(2,2)]
  | 14 => some [(3,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(8,3)]
  | 18 => some [(4,1)]
  | 19 => some [(0,2)]
  | 20 => some [(1,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(7,3)]
  | 27 => some [(5,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(7,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(4,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(6,3)]
  | 59 => some [(7,2)]
  | _ => some [(4,0)]
theorem root1Node10Domains2_fast_eq : root1Node10Domains2 = expandDomains root1Node10Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node10Domains2 v = expandDomains root1Node10Domains2Fast v from by decide) v
theorem root1Node10Step2Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2_checked :
    checkReplacement table39 root1Node10Domains1 root1Node10Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node10Step2Chunk0_0_checked, root1Node10Step2Chunk0_1_checked, root1Node10Step2Chunk0_2_checked, root1Node10Step2Chunk0_3_checked, root1Node10Step2Chunk0_4_checked, root1Node10Step2Chunk0_5_checked, root1Node10Step2Chunk1_0_checked, root1Node10Step2Chunk1_1_checked, root1Node10Step2Chunk1_2_checked, root1Node10Step2Chunk1_3_checked, root1Node10Step2Chunk1_4_checked, root1Node10Step2Chunk1_5_checked, root1Node10Step2Chunk2_0_checked, root1Node10Step2Chunk2_1_checked, root1Node10Step2Chunk2_2_checked, root1Node10Step2Chunk2_3_checked, root1Node10Step2Chunk2_4_checked, root1Node10Step2Chunk2_5_checked, root1Node10Step2Chunk3_0_checked, root1Node10Step2Chunk3_1_checked, root1Node10Step2Chunk3_2_checked, root1Node10Step2Chunk3_3_checked, root1Node10Step2Chunk3_4_checked, root1Node10Step2Chunk3_5_checked, root1Node10Step2Chunk4_0_checked, root1Node10Step2Chunk4_1_checked, root1Node10Step2Chunk4_2_checked, root1Node10Step2Chunk4_3_checked, root1Node10Step2Chunk4_4_checked, root1Node10Step2Chunk4_5_checked, root1Node10Step2Chunk5_0_checked, root1Node10Step2Chunk5_1_checked, root1Node10Step2Chunk5_2_checked, root1Node10Step2Chunk5_3_checked, root1Node10Step2Chunk5_4_checked, root1Node10Step2Chunk5_5_checked, root1Node10Step2Chunk6_0_checked, root1Node10Step2Chunk6_1_checked, root1Node10Step2Chunk6_2_checked, root1Node10Step2Chunk6_3_checked, root1Node10Step2Chunk6_4_checked, root1Node10Step2Chunk6_5_checked, root1Node10Step2Chunk7_0_checked, root1Node10Step2Chunk7_1_checked, root1Node10Step2Chunk7_2_checked, root1Node10Step2Chunk7_3_checked, root1Node10Step2Chunk7_4_checked, root1Node10Step2Chunk7_5_checked, root1Node10Step2Chunk8_0_checked, root1Node10Step2Chunk8_1_checked, root1Node10Step2Chunk8_2_checked, root1Node10Step2Chunk8_3_checked, root1Node10Step2Chunk8_4_checked, root1Node10Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root1Node10Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node10Domains2 (.output 4) = true := by decide
def root1Node11Domains0 : Domains 61 State := restrict root1Node1Domains5 2 (7,2)
def root1Node11Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4),(5,4),(7,4)]
  | 1 => some [(0,0),(6,3),(6,4)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,1),(2,3),(4,3)]
  | 6 => some [(0,2),(1,5),(7,5)]
  | 7 => some [(0,3),(1,1),(6,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(0,0),(1,4),(6,4),(7,4)]
  | 12 => some [(0,5),(1,2),(3,2),(6,3)]
  | 13 => some [(2,0),(2,2),(4,0)]
  | 14 => some [(3,3),(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3),(8,3)]
  | 18 => some [(1,5),(4,1),(7,5)]
  | 19 => some [(0,2),(0,3),(6,0),(6,1)]
  | 20 => some [(1,1),(3,1),(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0),(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(7,2)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(4,2),(5,2),(7,0),(8,2)]
  | 28 => some [(5,0),(5,3),(8,3)]
  | 29 => some [(4,5),(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,0),(6,1)]
  | 34 => some [(5,1),(7,1),(8,1)]
  | 35 => some [(1,2),(6,2),(7,2)]
  | 36 => some [(7,4),(8,4)]
  | 37 => some [(0,0),(1,3),(6,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(5,0),(5,3),(8,0),(8,3)]
  | 43 => some [(4,1),(7,1),(8,1)]
  | 44 => some [(0,2),(1,5),(6,5)]
  | 45 => some [(0,4),(1,1),(6,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,0),(0,1),(6,4)]
  | 48 => some [(1,2),(6,2),(7,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(4,5),(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 54 => some [(0,3),(1,0),(6,1)]
  | 55 => some [(2,1),(4,1),(7,1),(8,1)]
  | 56 => some [(4,4),(5,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(1,3),(6,3)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(7,2),(8,2)]
  | _ => some [(0,0),(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(8,0)]
theorem root1Node11Domains0_fast_eq : root1Node11Domains0 = expandDomains root1Node11Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node11Domains0 v = expandDomains root1Node11Domains0Fast v from by decide) v
def root1Node11Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(3,4),(5,4),(7,4)]
  | 1 => [(0,0),(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(2,1),(2,3),(4,3)]
  | 6 => [(0,2),(1,5)]
  | 7 => [(1,1),(6,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(0,0),(1,4),(6,4)]
  | 12 => [(0,5),(1,2),(3,2)]
  | 13 => [(2,0),(4,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(5,0),(8,0)]
  | 17 => [(4,5),(7,3),(8,3)]
  | 18 => [(1,5),(7,5)]
  | 19 => [(0,3),(6,0),(6,1)]
  | 20 => [(3,1),(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(0,0),(1,4),(6,4)]
  | 25 => [(0,5),(1,2),(7,2)]
  | 26 => [(4,5),(7,3)]
  | 27 => [(4,2),(7,0),(8,2)]
  | 28 => [(5,0),(5,3),(8,3)]
  | 29 => [(4,5),(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5),(7,5)]
  | 33 => [(0,3),(6,0),(6,1)]
  | 34 => [(5,1),(7,1),(8,1)]
  | 35 => [(1,2),(6,2),(7,2)]
  | 36 => [(7,4),(8,4)]
  | 37 => [(0,0),(1,3),(6,3)]
  | 38 => [(7,2),(8,2)]
  | 39 => [(4,0),(5,0),(8,0)]
  | 40 => [(4,5),(7,3)]
  | 41 => [(4,2),(7,0),(8,2)]
  | 42 => [(5,0),(5,3),(8,0),(8,3)]
  | 43 => [(4,1),(7,1),(8,1)]
  | 44 => [(0,2),(1,5),(6,5)]
  | 45 => [(0,4),(1,1),(6,1)]
  | 46 => [(5,1),(5,4)]
  | 47 => [(0,0),(0,1),(6,4)]
  | 48 => [(1,2),(6,2),(7,2)]
  | 49 => [(7,4),(8,4)]
  | 50 => [(4,5),(5,2),(5,5),(8,5)]
  | 51 => [(7,0),(8,0)]
  | 52 => [(4,3),(8,3)]
  | 53 => [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 54 => [(0,3),(1,0),(6,1)]
  | 55 => [(2,1),(4,1),(7,1),(8,1)]
  | 56 => [(4,4),(5,4),(7,2),(8,4)]
  | 57 => [(1,4),(7,4)]
  | 58 => [(0,5),(1,3),(6,3)]
  | 59 => [(2,0),(2,2),(2,4),(4,2),(4,4),(7,2),(8,2)]
  | _ => [(0,0),(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(8,0)]
def root1Node11Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4),(5,4),(7,4)]
  | 1 => some [(0,0),(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,1),(2,3),(4,3)]
  | 6 => some [(0,2),(1,5)]
  | 7 => some [(1,1),(6,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(0,0),(1,4),(6,4)]
  | 12 => some [(0,5),(1,2),(3,2)]
  | 13 => some [(2,0),(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3),(8,3)]
  | 18 => some [(1,5),(7,5)]
  | 19 => some [(0,3),(6,0),(6,1)]
  | 20 => some [(3,1),(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0),(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(7,2)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(4,2),(7,0),(8,2)]
  | 28 => some [(5,0),(5,3),(8,3)]
  | 29 => some [(4,5),(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,0),(6,1)]
  | 34 => some [(5,1),(7,1),(8,1)]
  | 35 => some [(1,2),(6,2),(7,2)]
  | 36 => some [(7,4),(8,4)]
  | 37 => some [(0,0),(1,3),(6,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(5,0),(5,3),(8,0),(8,3)]
  | 43 => some [(4,1),(7,1),(8,1)]
  | 44 => some [(0,2),(1,5),(6,5)]
  | 45 => some [(0,4),(1,1),(6,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,0),(0,1),(6,4)]
  | 48 => some [(1,2),(6,2),(7,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(4,5),(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 54 => some [(0,3),(1,0),(6,1)]
  | 55 => some [(2,1),(4,1),(7,1),(8,1)]
  | 56 => some [(4,4),(5,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(1,3),(6,3)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(7,2),(8,2)]
  | _ => some [(0,0),(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(8,0)]
theorem root1Node11Domains1_fast_eq : root1Node11Domains1 = expandDomains root1Node11Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node11Domains1 v = expandDomains root1Node11Domains1Fast v from by decide) v
theorem root1Node11Step1Chunk0_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_0⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk0_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_1⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk0_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_2⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk0_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_3⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk0_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_4⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk0_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_5⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk1_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_0⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk1_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_1⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk1_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_2⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk1_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_3⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk1_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_4⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk1_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_5⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk2_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_0⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk2_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_1⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk2_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_2⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk2_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_3⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk2_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_4⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk2_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_5⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk3_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_0⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk3_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_1⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk3_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_2⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk3_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_3⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk3_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_4⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk3_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_5⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk4_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_0⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk4_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_1⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk4_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_2⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk4_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_3⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk4_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_4⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk4_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_5⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk5_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_0⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk5_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_1⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk5_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_2⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk5_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_3⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk5_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_4⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk5_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_5⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk6_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_0⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk6_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_1⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk6_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_2⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk6_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_3⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk6_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_4⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk6_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_5⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk7_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_0⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk7_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_1⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk7_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_2⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk7_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_3⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk7_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_4⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk7_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_5⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk8_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_0⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk8_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_1⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk8_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_2⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk8_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_3⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk8_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_4⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1Chunk8_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_5⟩
      root1Node11Domains0 root1Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node11Domains0 root1Node11Domains1
    root1Node11Domains0Fast root1Node11Domains1Fast
    root1Node11Domains0_fast_eq root1Node11Domains1_fast_eq (by decide)
theorem root1Node11Step1_checked :
    checkReplacement table5 root1Node11Domains0 root1Node11Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node11Step1Chunk0_0_checked, root1Node11Step1Chunk0_1_checked, root1Node11Step1Chunk0_2_checked, root1Node11Step1Chunk0_3_checked, root1Node11Step1Chunk0_4_checked, root1Node11Step1Chunk0_5_checked, root1Node11Step1Chunk1_0_checked, root1Node11Step1Chunk1_1_checked, root1Node11Step1Chunk1_2_checked, root1Node11Step1Chunk1_3_checked, root1Node11Step1Chunk1_4_checked, root1Node11Step1Chunk1_5_checked, root1Node11Step1Chunk2_0_checked, root1Node11Step1Chunk2_1_checked, root1Node11Step1Chunk2_2_checked, root1Node11Step1Chunk2_3_checked, root1Node11Step1Chunk2_4_checked, root1Node11Step1Chunk2_5_checked, root1Node11Step1Chunk3_0_checked, root1Node11Step1Chunk3_1_checked, root1Node11Step1Chunk3_2_checked, root1Node11Step1Chunk3_3_checked, root1Node11Step1Chunk3_4_checked, root1Node11Step1Chunk3_5_checked, root1Node11Step1Chunk4_0_checked, root1Node11Step1Chunk4_1_checked, root1Node11Step1Chunk4_2_checked, root1Node11Step1Chunk4_3_checked, root1Node11Step1Chunk4_4_checked, root1Node11Step1Chunk4_5_checked, root1Node11Step1Chunk5_0_checked, root1Node11Step1Chunk5_1_checked, root1Node11Step1Chunk5_2_checked, root1Node11Step1Chunk5_3_checked, root1Node11Step1Chunk5_4_checked, root1Node11Step1Chunk5_5_checked, root1Node11Step1Chunk6_0_checked, root1Node11Step1Chunk6_1_checked, root1Node11Step1Chunk6_2_checked, root1Node11Step1Chunk6_3_checked, root1Node11Step1Chunk6_4_checked, root1Node11Step1Chunk6_5_checked, root1Node11Step1Chunk7_0_checked, root1Node11Step1Chunk7_1_checked, root1Node11Step1Chunk7_2_checked, root1Node11Step1Chunk7_3_checked, root1Node11Step1Chunk7_4_checked, root1Node11Step1Chunk7_5_checked, root1Node11Step1Chunk8_0_checked, root1Node11Step1Chunk8_1_checked, root1Node11Step1Chunk8_2_checked, root1Node11Step1Chunk8_3_checked, root1Node11Step1Chunk8_4_checked, root1Node11Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node12Domains0 : Domains 61 State := restrict root1Node11Domains1 1 (0,0)
def root1Node12Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4),(5,4),(7,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,1),(2,3),(4,3)]
  | 6 => some [(0,2),(1,5)]
  | 7 => some [(1,1),(6,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(0,0),(1,4),(6,4)]
  | 12 => some [(0,5),(1,2),(3,2)]
  | 13 => some [(2,0),(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3),(8,3)]
  | 18 => some [(1,5),(7,5)]
  | 19 => some [(0,3),(6,0),(6,1)]
  | 20 => some [(3,1),(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0),(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(7,2)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(4,2),(7,0),(8,2)]
  | 28 => some [(5,0),(5,3),(8,3)]
  | 29 => some [(4,5),(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,0),(6,1)]
  | 34 => some [(5,1),(7,1),(8,1)]
  | 35 => some [(1,2),(6,2),(7,2)]
  | 36 => some [(7,4),(8,4)]
  | 37 => some [(0,0),(1,3),(6,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(5,0),(5,3),(8,0),(8,3)]
  | 43 => some [(4,1),(7,1),(8,1)]
  | 44 => some [(0,2),(1,5),(6,5)]
  | 45 => some [(0,4),(1,1),(6,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,0),(0,1),(6,4)]
  | 48 => some [(1,2),(6,2),(7,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(4,5),(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 54 => some [(0,3),(1,0),(6,1)]
  | 55 => some [(2,1),(4,1),(7,1),(8,1)]
  | 56 => some [(4,4),(5,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(1,3),(6,3)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(7,2),(8,2)]
  | _ => some [(0,0),(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(8,0)]
theorem root1Node12Domains0_fast_eq : root1Node12Domains0 = expandDomains root1Node12Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node12Domains0 v = expandDomains root1Node12Domains0Fast v from by decide) v
def root1Node12Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(4,3)]
  | 6 => [(1,5)]
  | 7 => [(6,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(2,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(8,0)]
  | 17 => [(4,5),(7,3),(8,3)]
  | 18 => [(7,5)]
  | 19 => [(6,0)]
  | 20 => [(3,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(1,4),(6,4)]
  | 25 => [(0,5),(1,2),(7,2)]
  | 26 => [(4,5),(7,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(0,3),(6,0),(6,1)]
  | 34 => [(5,1),(7,1),(8,1)]
  | 35 => [(1,2),(6,2),(7,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(4,2),(7,0),(8,2)]
  | 42 => [(5,0),(5,3),(8,0),(8,3)]
  | 43 => [(4,1),(7,1),(8,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(1,2),(6,2),(7,2)]
  | 49 => [(7,4),(8,4)]
  | 50 => [(4,5),(5,2),(5,5),(8,5)]
  | 51 => [(7,0),(8,0)]
  | 52 => [(4,3),(8,3)]
  | 53 => [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 54 => [(0,3),(1,0),(6,1)]
  | 55 => [(2,1),(4,1),(7,1),(8,1)]
  | 56 => [(4,4),(5,4),(7,2),(8,4)]
  | 57 => [(1,4),(7,4)]
  | 58 => [(0,5),(1,3),(6,3)]
  | 59 => [(2,0),(2,2),(2,4),(4,2),(4,4),(7,2),(8,2)]
  | _ => [(0,0),(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(8,0)]
def root1Node12Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(1,5)]
  | 7 => some [(6,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(4,5),(7,3),(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(3,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(7,2)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3),(6,0),(6,1)]
  | 34 => some [(5,1),(7,1),(8,1)]
  | 35 => some [(1,2),(6,2),(7,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(5,0),(5,3),(8,0),(8,3)]
  | 43 => some [(4,1),(7,1),(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(1,2),(6,2),(7,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(4,5),(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 54 => some [(0,3),(1,0),(6,1)]
  | 55 => some [(2,1),(4,1),(7,1),(8,1)]
  | 56 => some [(4,4),(5,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(1,3),(6,3)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(7,2),(8,2)]
  | _ => some [(0,0),(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(8,0)]
theorem root1Node12Domains1_fast_eq : root1Node12Domains1 = expandDomains root1Node12Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node12Domains1 v = expandDomains root1Node12Domains1Fast v from by decide) v
theorem root1Node12Step1Chunk0_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_0⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk0_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_1⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk0_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_2⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk0_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_3⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk0_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_4⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk0_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_5⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk1_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_0⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk1_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_1⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk1_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_2⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk1_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_3⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk1_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_4⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk1_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_5⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk2_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_0⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk2_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_1⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk2_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_2⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk2_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_3⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk2_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_4⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk2_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_5⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk3_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_0⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk3_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_1⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk3_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_2⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk3_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_3⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk3_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_4⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk3_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_5⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk4_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_0⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk4_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_1⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk4_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_2⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk4_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_3⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk4_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_4⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk4_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_5⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk5_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_0⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk5_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_1⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk5_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_2⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk5_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_3⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk5_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_4⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk5_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_5⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk6_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_0⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk6_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_1⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk6_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_2⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk6_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_3⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk6_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_4⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk6_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_5⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk7_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_0⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk7_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_1⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk7_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_2⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk7_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_3⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk7_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_4⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk7_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_5⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk8_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_0⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk8_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_1⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk8_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_2⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk8_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_3⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk8_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_4⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1Chunk8_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_5⟩
      root1Node12Domains0 root1Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains0 root1Node12Domains1
    root1Node12Domains0Fast root1Node12Domains1Fast
    root1Node12Domains0_fast_eq root1Node12Domains1_fast_eq (by decide)
theorem root1Node12Step1_checked :
    checkReplacement table21 root1Node12Domains0 root1Node12Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node12Step1Chunk0_0_checked, root1Node12Step1Chunk0_1_checked, root1Node12Step1Chunk0_2_checked, root1Node12Step1Chunk0_3_checked, root1Node12Step1Chunk0_4_checked, root1Node12Step1Chunk0_5_checked, root1Node12Step1Chunk1_0_checked, root1Node12Step1Chunk1_1_checked, root1Node12Step1Chunk1_2_checked, root1Node12Step1Chunk1_3_checked, root1Node12Step1Chunk1_4_checked, root1Node12Step1Chunk1_5_checked, root1Node12Step1Chunk2_0_checked, root1Node12Step1Chunk2_1_checked, root1Node12Step1Chunk2_2_checked, root1Node12Step1Chunk2_3_checked, root1Node12Step1Chunk2_4_checked, root1Node12Step1Chunk2_5_checked, root1Node12Step1Chunk3_0_checked, root1Node12Step1Chunk3_1_checked, root1Node12Step1Chunk3_2_checked, root1Node12Step1Chunk3_3_checked, root1Node12Step1Chunk3_4_checked, root1Node12Step1Chunk3_5_checked, root1Node12Step1Chunk4_0_checked, root1Node12Step1Chunk4_1_checked, root1Node12Step1Chunk4_2_checked, root1Node12Step1Chunk4_3_checked, root1Node12Step1Chunk4_4_checked, root1Node12Step1Chunk4_5_checked, root1Node12Step1Chunk5_0_checked, root1Node12Step1Chunk5_1_checked, root1Node12Step1Chunk5_2_checked, root1Node12Step1Chunk5_3_checked, root1Node12Step1Chunk5_4_checked, root1Node12Step1Chunk5_5_checked, root1Node12Step1Chunk6_0_checked, root1Node12Step1Chunk6_1_checked, root1Node12Step1Chunk6_2_checked, root1Node12Step1Chunk6_3_checked, root1Node12Step1Chunk6_4_checked, root1Node12Step1Chunk6_5_checked, root1Node12Step1Chunk7_0_checked, root1Node12Step1Chunk7_1_checked, root1Node12Step1Chunk7_2_checked, root1Node12Step1Chunk7_3_checked, root1Node12Step1Chunk7_4_checked, root1Node12Step1Chunk7_5_checked, root1Node12Step1Chunk8_0_checked, root1Node12Step1Chunk8_1_checked, root1Node12Step1Chunk8_2_checked, root1Node12Step1Chunk8_3_checked, root1Node12Step1Chunk8_4_checked, root1Node12Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
