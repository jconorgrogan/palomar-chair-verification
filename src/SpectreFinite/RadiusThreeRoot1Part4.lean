module

public import SpectreFinite.RadiusThreeRoot1Part3
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable26
public import SpectreFinite.RadiusThreeTable4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node3Domains0 : Domains 37 State := restrict root1Node2Domains4 14 (1,4)
def root1Node3Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(6,3)]
  | 5 => some [(2,2)]
  | 6 => some [(3,3)]
  | 7 => some [(5,2)]
  | 8 => some [(8,0)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(1,4)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(6,0)]
  | 22 => some [(8,4)]
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
  | 35 => some [(5,5),(8,5)]
  | _ => some [(1,0)]
theorem root1Node3Domains0_fast_eq : root1Node3Domains0 = expandDomains root1Node3Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node3Domains0 v = expandDomains root1Node3Domains0Fast v from by decide) v
def root1Node3Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(6,3)]
  | 5 => [(2,2)]
  | 6 => [(3,3)]
  | 7 => [(5,2)]
  | 8 => [(8,0)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(1,4)]
  | 15 => [(5,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(8,4)]
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
def root1Node3Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(6,3)]
  | 5 => some [(2,2)]
  | 6 => some [(3,3)]
  | 7 => some [(5,2)]
  | 8 => some [(8,0)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(1,4)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(8,4)]
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
theorem root1Node3Domains1_fast_eq : root1Node3Domains1 = expandDomains root1Node3Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node3Domains1 v = expandDomains root1Node3Domains1Fast v from by decide) v
theorem root1Node3Step1Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1_checked :
    checkReplacement table26 root1Node3Domains0 root1Node3Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node3Step1Chunk0_0_checked, root1Node3Step1Chunk0_1_checked, root1Node3Step1Chunk0_2_checked, root1Node3Step1Chunk0_3_checked, root1Node3Step1Chunk0_4_checked, root1Node3Step1Chunk0_5_checked, root1Node3Step1Chunk1_0_checked, root1Node3Step1Chunk1_1_checked, root1Node3Step1Chunk1_2_checked, root1Node3Step1Chunk1_3_checked, root1Node3Step1Chunk1_4_checked, root1Node3Step1Chunk1_5_checked, root1Node3Step1Chunk2_0_checked, root1Node3Step1Chunk2_1_checked, root1Node3Step1Chunk2_2_checked, root1Node3Step1Chunk2_3_checked, root1Node3Step1Chunk2_4_checked, root1Node3Step1Chunk2_5_checked, root1Node3Step1Chunk3_0_checked, root1Node3Step1Chunk3_1_checked, root1Node3Step1Chunk3_2_checked, root1Node3Step1Chunk3_3_checked, root1Node3Step1Chunk3_4_checked, root1Node3Step1Chunk3_5_checked, root1Node3Step1Chunk4_0_checked, root1Node3Step1Chunk4_1_checked, root1Node3Step1Chunk4_2_checked, root1Node3Step1Chunk4_3_checked, root1Node3Step1Chunk4_4_checked, root1Node3Step1Chunk4_5_checked, root1Node3Step1Chunk5_0_checked, root1Node3Step1Chunk5_1_checked, root1Node3Step1Chunk5_2_checked, root1Node3Step1Chunk5_3_checked, root1Node3Step1Chunk5_4_checked, root1Node3Step1Chunk5_5_checked, root1Node3Step1Chunk6_0_checked, root1Node3Step1Chunk6_1_checked, root1Node3Step1Chunk6_2_checked, root1Node3Step1Chunk6_3_checked, root1Node3Step1Chunk6_4_checked, root1Node3Step1Chunk6_5_checked, root1Node3Step1Chunk7_0_checked, root1Node3Step1Chunk7_1_checked, root1Node3Step1Chunk7_2_checked, root1Node3Step1Chunk7_3_checked, root1Node3Step1Chunk7_4_checked, root1Node3Step1Chunk7_5_checked, root1Node3Step1Chunk8_0_checked, root1Node3Step1Chunk8_1_checked, root1Node3Step1Chunk8_2_checked, root1Node3Step1Chunk8_3_checked, root1Node3Step1Chunk8_4_checked, root1Node3Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root1Node3Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node3Domains1 (.output 0) = true := by decide
def root1Node4Domains0 : Domains 37 State := restrict root1Node2Domains4 14 (6,4)
def root1Node4Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(6,3)]
  | 5 => some [(2,2)]
  | 6 => some [(3,3)]
  | 7 => some [(5,2)]
  | 8 => some [(8,0)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(6,4)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(6,0)]
  | 22 => some [(8,4)]
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
  | 35 => some [(5,5),(8,5)]
  | _ => some [(1,0)]
theorem root1Node4Domains0_fast_eq : root1Node4Domains0 = expandDomains root1Node4Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node4Domains0 v = expandDomains root1Node4Domains0Fast v from by decide) v
def root1Node4Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(6,3)]
  | 5 => [(2,2)]
  | 6 => [(3,3)]
  | 7 => [(5,2)]
  | 8 => [(8,0)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(6,4)]
  | 15 => [(5,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(0,3)]
  | 22 => [(8,4)]
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
  | 35 => [(5,5)]
  | _ => [(1,0)]
def root1Node4Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(6,3)]
  | 5 => some [(2,2)]
  | 6 => some [(3,3)]
  | 7 => some [(5,2)]
  | 8 => some [(8,0)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(6,4)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3)]
  | 22 => some [(8,4)]
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
  | 35 => some [(5,5)]
  | _ => some [(1,0)]
theorem root1Node4Domains1_fast_eq : root1Node4Domains1 = expandDomains root1Node4Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node4Domains1 v = expandDomains root1Node4Domains1Fast v from by decide) v
theorem root1Node4Step1Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root1Node4Domains0 root1Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node4Domains0 root1Node4Domains1
    root1Node4Domains0Fast root1Node4Domains1Fast
    root1Node4Domains0_fast_eq root1Node4Domains1_fast_eq (by decide)
theorem root1Node4Step1_checked :
    checkReplacement table26 root1Node4Domains0 root1Node4Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node4Step1Chunk0_0_checked, root1Node4Step1Chunk0_1_checked, root1Node4Step1Chunk0_2_checked, root1Node4Step1Chunk0_3_checked, root1Node4Step1Chunk0_4_checked, root1Node4Step1Chunk0_5_checked, root1Node4Step1Chunk1_0_checked, root1Node4Step1Chunk1_1_checked, root1Node4Step1Chunk1_2_checked, root1Node4Step1Chunk1_3_checked, root1Node4Step1Chunk1_4_checked, root1Node4Step1Chunk1_5_checked, root1Node4Step1Chunk2_0_checked, root1Node4Step1Chunk2_1_checked, root1Node4Step1Chunk2_2_checked, root1Node4Step1Chunk2_3_checked, root1Node4Step1Chunk2_4_checked, root1Node4Step1Chunk2_5_checked, root1Node4Step1Chunk3_0_checked, root1Node4Step1Chunk3_1_checked, root1Node4Step1Chunk3_2_checked, root1Node4Step1Chunk3_3_checked, root1Node4Step1Chunk3_4_checked, root1Node4Step1Chunk3_5_checked, root1Node4Step1Chunk4_0_checked, root1Node4Step1Chunk4_1_checked, root1Node4Step1Chunk4_2_checked, root1Node4Step1Chunk4_3_checked, root1Node4Step1Chunk4_4_checked, root1Node4Step1Chunk4_5_checked, root1Node4Step1Chunk5_0_checked, root1Node4Step1Chunk5_1_checked, root1Node4Step1Chunk5_2_checked, root1Node4Step1Chunk5_3_checked, root1Node4Step1Chunk5_4_checked, root1Node4Step1Chunk5_5_checked, root1Node4Step1Chunk6_0_checked, root1Node4Step1Chunk6_1_checked, root1Node4Step1Chunk6_2_checked, root1Node4Step1Chunk6_3_checked, root1Node4Step1Chunk6_4_checked, root1Node4Step1Chunk6_5_checked, root1Node4Step1Chunk7_0_checked, root1Node4Step1Chunk7_1_checked, root1Node4Step1Chunk7_2_checked, root1Node4Step1Chunk7_3_checked, root1Node4Step1Chunk7_4_checked, root1Node4Step1Chunk7_5_checked, root1Node4Step1Chunk8_0_checked, root1Node4Step1Chunk8_1_checked, root1Node4Step1Chunk8_2_checked, root1Node4Step1Chunk8_3_checked, root1Node4Step1Chunk8_4_checked, root1Node4Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root1Node4Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node4Domains1 (.output 1) = true := by decide
def root1Node5Domains0 : Domains 37 State := restrict root1Node1Domains4 6 (7,3)
def root1Node5Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5),(7,5)]
  | 1 => some [(0,3),(1,1),(6,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(0,5),(1,2),(3,2),(6,3)]
  | 5 => some [(2,0),(2,2),(4,0)]
  | 6 => some [(7,3)]
  | 7 => some [(5,2)]
  | 8 => some [(5,0),(8,0)]
  | 9 => some [(0,2),(0,3),(6,0),(6,1)]
  | 10 => some [(1,1),(3,1),(5,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0),(1,4),(6,4)]
  | 15 => some [(4,2),(5,2),(7,0),(8,2)]
  | 16 => some [(5,0),(5,3),(8,3)]
  | 17 => some [(4,5),(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(0,3),(6,0),(6,1)]
  | 22 => some [(7,4),(8,4)]
  | 23 => some [(0,0),(1,3),(6,3)]
  | 24 => some [(7,2),(8,2)]
  | 25 => some [(4,0),(5,0),(8,0)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(4,2),(7,0),(8,2)]
  | 28 => some [(0,2),(1,5),(6,5)]
  | 29 => some [(0,4),(1,1),(6,1)]
  | 30 => some [(5,1),(5,4)]
  | 31 => some [(0,0),(0,1),(6,4)]
  | 32 => some [(1,2),(6,2),(7,2)]
  | 33 => some [(7,0),(8,0)]
  | 34 => some [(4,3),(8,3)]
  | 35 => some [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | _ => some [(0,3),(1,0),(6,1)]
theorem root1Node5Domains0_fast_eq : root1Node5Domains0 = expandDomains root1Node5Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node5Domains0 v = expandDomains root1Node5Domains0Fast v from by decide) v
def root1Node5Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,2),(1,5)]
  | 1 => [(1,1),(6,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(0,5),(1,2),(3,2)]
  | 5 => [(2,0),(4,0)]
  | 6 => [(7,3)]
  | 7 => [(5,2)]
  | 8 => [(5,0),(8,0)]
  | 9 => [(0,3),(6,0),(6,1)]
  | 10 => [(3,1),(5,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0),(1,4),(6,4)]
  | 15 => [(4,2),(7,0),(8,2)]
  | 16 => [(5,0),(5,3),(8,3)]
  | 17 => [(4,5),(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5),(7,5)]
  | 21 => [(0,3),(6,0),(6,1)]
  | 22 => [(7,4),(8,4)]
  | 23 => [(0,0),(1,3),(6,3)]
  | 24 => [(7,2),(8,2)]
  | 25 => [(4,0),(5,0),(8,0)]
  | 26 => [(4,5),(7,3)]
  | 27 => [(4,2),(7,0),(8,2)]
  | 28 => [(0,2),(1,5),(6,5)]
  | 29 => [(0,4),(1,1),(6,1)]
  | 30 => [(5,1),(5,4)]
  | 31 => [(0,0),(0,1),(6,4)]
  | 32 => [(1,2),(6,2),(7,2)]
  | 33 => [(7,0),(8,0)]
  | 34 => [(4,3),(8,3)]
  | 35 => [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | _ => [(0,3),(1,0),(6,1)]
def root1Node5Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5)]
  | 1 => some [(1,1),(6,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(0,5),(1,2),(3,2)]
  | 5 => some [(2,0),(4,0)]
  | 6 => some [(7,3)]
  | 7 => some [(5,2)]
  | 8 => some [(5,0),(8,0)]
  | 9 => some [(0,3),(6,0),(6,1)]
  | 10 => some [(3,1),(5,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0),(1,4),(6,4)]
  | 15 => some [(4,2),(7,0),(8,2)]
  | 16 => some [(5,0),(5,3),(8,3)]
  | 17 => some [(4,5),(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(0,3),(6,0),(6,1)]
  | 22 => some [(7,4),(8,4)]
  | 23 => some [(0,0),(1,3),(6,3)]
  | 24 => some [(7,2),(8,2)]
  | 25 => some [(4,0),(5,0),(8,0)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(4,2),(7,0),(8,2)]
  | 28 => some [(0,2),(1,5),(6,5)]
  | 29 => some [(0,4),(1,1),(6,1)]
  | 30 => some [(5,1),(5,4)]
  | 31 => some [(0,0),(0,1),(6,4)]
  | 32 => some [(1,2),(6,2),(7,2)]
  | 33 => some [(7,0),(8,0)]
  | 34 => some [(4,3),(8,3)]
  | 35 => some [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | _ => some [(0,3),(1,0),(6,1)]
theorem root1Node5Domains1_fast_eq : root1Node5Domains1 = expandDomains root1Node5Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node5Domains1 v = expandDomains root1Node5Domains1Fast v from by decide) v
theorem root1Node5Step1Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root1Node5Domains0 root1Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node5Domains0 root1Node5Domains1
    root1Node5Domains0Fast root1Node5Domains1Fast
    root1Node5Domains0_fast_eq root1Node5Domains1_fast_eq (by decide)
theorem root1Node5Step1_checked :
    checkReplacement table4 root1Node5Domains0 root1Node5Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node5Step1Chunk0_0_checked, root1Node5Step1Chunk0_1_checked, root1Node5Step1Chunk0_2_checked, root1Node5Step1Chunk0_3_checked, root1Node5Step1Chunk0_4_checked, root1Node5Step1Chunk0_5_checked, root1Node5Step1Chunk1_0_checked, root1Node5Step1Chunk1_1_checked, root1Node5Step1Chunk1_2_checked, root1Node5Step1Chunk1_3_checked, root1Node5Step1Chunk1_4_checked, root1Node5Step1Chunk1_5_checked, root1Node5Step1Chunk2_0_checked, root1Node5Step1Chunk2_1_checked, root1Node5Step1Chunk2_2_checked, root1Node5Step1Chunk2_3_checked, root1Node5Step1Chunk2_4_checked, root1Node5Step1Chunk2_5_checked, root1Node5Step1Chunk3_0_checked, root1Node5Step1Chunk3_1_checked, root1Node5Step1Chunk3_2_checked, root1Node5Step1Chunk3_3_checked, root1Node5Step1Chunk3_4_checked, root1Node5Step1Chunk3_5_checked, root1Node5Step1Chunk4_0_checked, root1Node5Step1Chunk4_1_checked, root1Node5Step1Chunk4_2_checked, root1Node5Step1Chunk4_3_checked, root1Node5Step1Chunk4_4_checked, root1Node5Step1Chunk4_5_checked, root1Node5Step1Chunk5_0_checked, root1Node5Step1Chunk5_1_checked, root1Node5Step1Chunk5_2_checked, root1Node5Step1Chunk5_3_checked, root1Node5Step1Chunk5_4_checked, root1Node5Step1Chunk5_5_checked, root1Node5Step1Chunk6_0_checked, root1Node5Step1Chunk6_1_checked, root1Node5Step1Chunk6_2_checked, root1Node5Step1Chunk6_3_checked, root1Node5Step1Chunk6_4_checked, root1Node5Step1Chunk6_5_checked, root1Node5Step1Chunk7_0_checked, root1Node5Step1Chunk7_1_checked, root1Node5Step1Chunk7_2_checked, root1Node5Step1Chunk7_3_checked, root1Node5Step1Chunk7_4_checked, root1Node5Step1Chunk7_5_checked, root1Node5Step1Chunk8_0_checked, root1Node5Step1Chunk8_1_checked, root1Node5Step1Chunk8_2_checked, root1Node5Step1Chunk8_3_checked, root1Node5Step1Chunk8_4_checked, root1Node5Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
