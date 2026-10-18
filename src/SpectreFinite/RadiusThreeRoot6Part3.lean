module

public import SpectreFinite.RadiusThreeRoot6Part2
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable13

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node3Domains0 : Domains 37 State := restrict root6Node2Domains0 14 (1,4)
def root6Node3Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(5,3)]
  | 7 => some [(5,5)]
  | 8 => some [(7,0)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(1,4)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(6,0)]
  | 22 => some [(4,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(4,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(5,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(7,0)]
  | 34 => some [(8,3)]
  | 35 => some [(8,5)]
  | _ => some [(1,0)]
theorem root6Node3Domains0_fast_eq : root6Node3Domains0 = expandDomains root6Node3Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node3Domains0 v = expandDomains root6Node3Domains0Fast v from by decide) v
def root6Node3Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(1,5)]
  | 4 => [(1,3)]
  | 5 => [(4,2)]
  | 6 => [(5,3)]
  | 7 => [(5,5)]
  | 8 => [(7,0)]
  | 9 => [(6,5)]
  | 10 => [(0,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(1,4)]
  | 15 => [(5,5)]
  | 16 => [(3,0)]
  | 17 => [(2,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(4,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(4,0)]
  | 26 => [(7,3)]
  | 27 => [(8,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(5,1)]
  | 31 => [(0,1)]
  | 32 => [(6,2)]
  | 33 => [(7,0)]
  | 34 => [(8,3)]
  | 35 => [(8,5)]
  | _ => [(1,0)]
def root6Node3Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(5,3)]
  | 7 => some [(5,5)]
  | 8 => some [(7,0)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(1,4)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(4,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(4,0)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(5,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(7,0)]
  | 34 => some [(8,3)]
  | 35 => some [(8,5)]
  | _ => some [(1,0)]
theorem root6Node3Domains1_fast_eq : root6Node3Domains1 = expandDomains root6Node3Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node3Domains1 v = expandDomains root6Node3Domains1Fast v from by decide) v
theorem root6Node3Step1Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root6Node3Domains0 root6Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node3Domains0 root6Node3Domains1
    root6Node3Domains0Fast root6Node3Domains1Fast
    root6Node3Domains0_fast_eq root6Node3Domains1_fast_eq (by decide)
theorem root6Node3Step1_checked :
    checkReplacement table13 root6Node3Domains0 root6Node3Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node3Step1Chunk0_0_checked, root6Node3Step1Chunk0_1_checked, root6Node3Step1Chunk0_2_checked, root6Node3Step1Chunk0_3_checked, root6Node3Step1Chunk0_4_checked, root6Node3Step1Chunk0_5_checked, root6Node3Step1Chunk1_0_checked, root6Node3Step1Chunk1_1_checked, root6Node3Step1Chunk1_2_checked, root6Node3Step1Chunk1_3_checked, root6Node3Step1Chunk1_4_checked, root6Node3Step1Chunk1_5_checked, root6Node3Step1Chunk2_0_checked, root6Node3Step1Chunk2_1_checked, root6Node3Step1Chunk2_2_checked, root6Node3Step1Chunk2_3_checked, root6Node3Step1Chunk2_4_checked, root6Node3Step1Chunk2_5_checked, root6Node3Step1Chunk3_0_checked, root6Node3Step1Chunk3_1_checked, root6Node3Step1Chunk3_2_checked, root6Node3Step1Chunk3_3_checked, root6Node3Step1Chunk3_4_checked, root6Node3Step1Chunk3_5_checked, root6Node3Step1Chunk4_0_checked, root6Node3Step1Chunk4_1_checked, root6Node3Step1Chunk4_2_checked, root6Node3Step1Chunk4_3_checked, root6Node3Step1Chunk4_4_checked, root6Node3Step1Chunk4_5_checked, root6Node3Step1Chunk5_0_checked, root6Node3Step1Chunk5_1_checked, root6Node3Step1Chunk5_2_checked, root6Node3Step1Chunk5_3_checked, root6Node3Step1Chunk5_4_checked, root6Node3Step1Chunk5_5_checked, root6Node3Step1Chunk6_0_checked, root6Node3Step1Chunk6_1_checked, root6Node3Step1Chunk6_2_checked, root6Node3Step1Chunk6_3_checked, root6Node3Step1Chunk6_4_checked, root6Node3Step1Chunk6_5_checked, root6Node3Step1Chunk7_0_checked, root6Node3Step1Chunk7_1_checked, root6Node3Step1Chunk7_2_checked, root6Node3Step1Chunk7_3_checked, root6Node3Step1Chunk7_4_checked, root6Node3Step1Chunk7_5_checked, root6Node3Step1Chunk8_0_checked, root6Node3Step1Chunk8_1_checked, root6Node3Step1Chunk8_2_checked, root6Node3Step1Chunk8_3_checked, root6Node3Step1Chunk8_4_checked, root6Node3Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root6Node3Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node3Domains1 (.output 0) = true := by decide
def root6Node4Domains0 : Domains 37 State := restrict root6Node2Domains0 14 (6,4)
def root6Node4Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(5,3)]
  | 7 => some [(5,5)]
  | 8 => some [(7,0)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(6,4)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(6,0)]
  | 22 => some [(4,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(4,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(5,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(7,0)]
  | 34 => some [(8,3)]
  | 35 => some [(8,5)]
  | _ => some [(1,0)]
theorem root6Node4Domains0_fast_eq : root6Node4Domains0 = expandDomains root6Node4Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node4Domains0 v = expandDomains root6Node4Domains0Fast v from by decide) v
def root6Node4Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(1,5)]
  | 4 => [(1,3)]
  | 5 => [(4,2)]
  | 6 => [(5,3)]
  | 7 => [(5,5)]
  | 8 => [(7,0)]
  | 9 => [(6,5)]
  | 10 => [(0,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(6,4)]
  | 15 => [(5,5)]
  | 16 => [(3,0)]
  | 17 => [(2,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(0,3)]
  | 22 => [(4,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(4,0)]
  | 26 => [(7,3)]
  | 27 => [(4,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(5,1)]
  | 31 => [(0,1)]
  | 32 => [(6,2)]
  | 33 => [(7,0)]
  | 34 => [(8,3)]
  | 35 => [(8,5)]
  | _ => [(1,0)]
def root6Node4Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(5,3)]
  | 7 => some [(5,5)]
  | 8 => some [(7,0)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(6,4)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3)]
  | 22 => some [(4,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(4,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(5,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(7,0)]
  | 34 => some [(8,3)]
  | 35 => some [(8,5)]
  | _ => some [(1,0)]
theorem root6Node4Domains1_fast_eq : root6Node4Domains1 = expandDomains root6Node4Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node4Domains1 v = expandDomains root6Node4Domains1Fast v from by decide) v
theorem root6Node4Step1Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root6Node4Domains0 root6Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node4Domains0 root6Node4Domains1
    root6Node4Domains0Fast root6Node4Domains1Fast
    root6Node4Domains0_fast_eq root6Node4Domains1_fast_eq (by decide)
theorem root6Node4Step1_checked :
    checkReplacement table13 root6Node4Domains0 root6Node4Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node4Step1Chunk0_0_checked, root6Node4Step1Chunk0_1_checked, root6Node4Step1Chunk0_2_checked, root6Node4Step1Chunk0_3_checked, root6Node4Step1Chunk0_4_checked, root6Node4Step1Chunk0_5_checked, root6Node4Step1Chunk1_0_checked, root6Node4Step1Chunk1_1_checked, root6Node4Step1Chunk1_2_checked, root6Node4Step1Chunk1_3_checked, root6Node4Step1Chunk1_4_checked, root6Node4Step1Chunk1_5_checked, root6Node4Step1Chunk2_0_checked, root6Node4Step1Chunk2_1_checked, root6Node4Step1Chunk2_2_checked, root6Node4Step1Chunk2_3_checked, root6Node4Step1Chunk2_4_checked, root6Node4Step1Chunk2_5_checked, root6Node4Step1Chunk3_0_checked, root6Node4Step1Chunk3_1_checked, root6Node4Step1Chunk3_2_checked, root6Node4Step1Chunk3_3_checked, root6Node4Step1Chunk3_4_checked, root6Node4Step1Chunk3_5_checked, root6Node4Step1Chunk4_0_checked, root6Node4Step1Chunk4_1_checked, root6Node4Step1Chunk4_2_checked, root6Node4Step1Chunk4_3_checked, root6Node4Step1Chunk4_4_checked, root6Node4Step1Chunk4_5_checked, root6Node4Step1Chunk5_0_checked, root6Node4Step1Chunk5_1_checked, root6Node4Step1Chunk5_2_checked, root6Node4Step1Chunk5_3_checked, root6Node4Step1Chunk5_4_checked, root6Node4Step1Chunk5_5_checked, root6Node4Step1Chunk6_0_checked, root6Node4Step1Chunk6_1_checked, root6Node4Step1Chunk6_2_checked, root6Node4Step1Chunk6_3_checked, root6Node4Step1Chunk6_4_checked, root6Node4Step1Chunk6_5_checked, root6Node4Step1Chunk7_0_checked, root6Node4Step1Chunk7_1_checked, root6Node4Step1Chunk7_2_checked, root6Node4Step1Chunk7_3_checked, root6Node4Step1Chunk7_4_checked, root6Node4Step1Chunk7_5_checked, root6Node4Step1Chunk8_0_checked, root6Node4Step1Chunk8_1_checked, root6Node4Step1Chunk8_2_checked, root6Node4Step1Chunk8_3_checked, root6Node4Step1Chunk8_4_checked, root6Node4Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root6Node4Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node4Domains1 (.output 1) = true := by decide
def root6Node5Domains0 : Domains 37 State := restrict root6Node1Domains4 3 (6,5)
def root6Node5Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(5,3)]
  | 7 => some [(5,5)]
  | 8 => some [(7,0)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(1,4),(6,4)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(6,0)]
  | 22 => some [(4,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(4,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(5,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(7,0)]
  | 34 => some [(8,3)]
  | 35 => some [(8,5)]
  | _ => some [(1,0)]
theorem root6Node5Domains0_fast_eq : root6Node5Domains0 = expandDomains root6Node5Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node5Domains0 v = expandDomains root6Node5Domains0Fast v from by decide) v
def root6Node5Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(1,3)]
  | 5 => [(4,2)]
  | 6 => [(5,3)]
  | 7 => [(5,5)]
  | 8 => [(7,0)]
  | 9 => [(6,5)]
  | 10 => [(0,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(1,4)]
  | 15 => [(5,5)]
  | 16 => [(3,0)]
  | 17 => [(2,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(4,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(4,0)]
  | 26 => [(7,3)]
  | 27 => [(8,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(5,1)]
  | 31 => [(0,1)]
  | 32 => [(6,2)]
  | 33 => [(7,0)]
  | 34 => [(8,3)]
  | 35 => [(8,5)]
  | _ => [(1,0)]
def root6Node5Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(5,3)]
  | 7 => some [(5,5)]
  | 8 => some [(7,0)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(1,4)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(4,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(4,0)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(5,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(7,0)]
  | 34 => some [(8,3)]
  | 35 => some [(8,5)]
  | _ => some [(1,0)]
theorem root6Node5Domains1_fast_eq : root6Node5Domains1 = expandDomains root6Node5Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node5Domains1 v = expandDomains root6Node5Domains1Fast v from by decide) v
theorem root6Node5Step1Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1_checked :
    checkReplacement table13 root6Node5Domains0 root6Node5Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node5Step1Chunk0_0_checked, root6Node5Step1Chunk0_1_checked, root6Node5Step1Chunk0_2_checked, root6Node5Step1Chunk0_3_checked, root6Node5Step1Chunk0_4_checked, root6Node5Step1Chunk0_5_checked, root6Node5Step1Chunk1_0_checked, root6Node5Step1Chunk1_1_checked, root6Node5Step1Chunk1_2_checked, root6Node5Step1Chunk1_3_checked, root6Node5Step1Chunk1_4_checked, root6Node5Step1Chunk1_5_checked, root6Node5Step1Chunk2_0_checked, root6Node5Step1Chunk2_1_checked, root6Node5Step1Chunk2_2_checked, root6Node5Step1Chunk2_3_checked, root6Node5Step1Chunk2_4_checked, root6Node5Step1Chunk2_5_checked, root6Node5Step1Chunk3_0_checked, root6Node5Step1Chunk3_1_checked, root6Node5Step1Chunk3_2_checked, root6Node5Step1Chunk3_3_checked, root6Node5Step1Chunk3_4_checked, root6Node5Step1Chunk3_5_checked, root6Node5Step1Chunk4_0_checked, root6Node5Step1Chunk4_1_checked, root6Node5Step1Chunk4_2_checked, root6Node5Step1Chunk4_3_checked, root6Node5Step1Chunk4_4_checked, root6Node5Step1Chunk4_5_checked, root6Node5Step1Chunk5_0_checked, root6Node5Step1Chunk5_1_checked, root6Node5Step1Chunk5_2_checked, root6Node5Step1Chunk5_3_checked, root6Node5Step1Chunk5_4_checked, root6Node5Step1Chunk5_5_checked, root6Node5Step1Chunk6_0_checked, root6Node5Step1Chunk6_1_checked, root6Node5Step1Chunk6_2_checked, root6Node5Step1Chunk6_3_checked, root6Node5Step1Chunk6_4_checked, root6Node5Step1Chunk6_5_checked, root6Node5Step1Chunk7_0_checked, root6Node5Step1Chunk7_1_checked, root6Node5Step1Chunk7_2_checked, root6Node5Step1Chunk7_3_checked, root6Node5Step1Chunk7_4_checked, root6Node5Step1Chunk7_5_checked, root6Node5Step1Chunk8_0_checked, root6Node5Step1Chunk8_1_checked, root6Node5Step1Chunk8_2_checked, root6Node5Step1Chunk8_3_checked, root6Node5Step1Chunk8_4_checked, root6Node5Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root6Node5Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node5Domains1 (.output 2) = true := by decide
end SpectreFinite.HexSearch.RadiusThree
