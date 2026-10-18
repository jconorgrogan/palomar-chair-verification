module

public import SpectreFinite.RadiusThreeRoot8Part32
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable17
public import SpectreFinite.RadiusThreeTable25

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node66Domains0 : Domains 37 State := restrict root8Node65Domains1 32 (4,1)
def root8Node66Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(5,4)]
  | 5 => some [(1,4)]
  | 6 => some [(0,5)]
  | 7 => some [(4,4)]
  | 8 => some [(6,4)]
  | 9 => some [(4,3)]
  | 10 => some [(7,5)]
  | 11 => some [(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2)]
  | 21 => some [(5,3)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(6,4)]
  | 26 => some [(1,2)]
  | 27 => some [(7,4)]
  | 28 => some [(7,0)]
  | 29 => some [(4,3)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3)]
  | 32 => some [(4,1)]
  | 33 => some [(7,4)]
  | 34 => some [(1,3),(6,3)]
  | 35 => some [(2,2),(4,2)]
  | _ => some [(3,3),(5,3)]
theorem root8Node66Domains0_fast_eq : root8Node66Domains0 = expandDomains root8Node66Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node66Domains0 v = expandDomains root8Node66Domains0Fast v from by decide) v
def root8Node66Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(7,0)]
  | 4 => [(5,4)]
  | 5 => [(1,4)]
  | 6 => [(0,5)]
  | 7 => [(4,4)]
  | 8 => [(6,4)]
  | 9 => [(4,3)]
  | 10 => [(7,5)]
  | 11 => [(6,0)]
  | 12 => [(7,1)]
  | 13 => [(7,5)]
  | 14 => [(0,3)]
  | 15 => [(7,4)]
  | 16 => [(1,3)]
  | 17 => [(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2)]
  | 21 => [(5,3)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(6,4)]
  | 26 => [(1,2)]
  | 27 => [(7,4)]
  | 28 => [(7,0)]
  | 29 => [(4,3)]
  | 30 => [(7,5)]
  | 31 => [(0,3)]
  | 32 => [(4,1)]
  | 33 => [(7,4)]
  | 34 => [(6,3)]
  | 35 => [(2,2)]
  | _ => [(3,3)]
def root8Node66Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(5,4)]
  | 5 => some [(1,4)]
  | 6 => some [(0,5)]
  | 7 => some [(4,4)]
  | 8 => some [(6,4)]
  | 9 => some [(4,3)]
  | 10 => some [(7,5)]
  | 11 => some [(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2)]
  | 21 => some [(5,3)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(6,4)]
  | 26 => some [(1,2)]
  | 27 => some [(7,4)]
  | 28 => some [(7,0)]
  | 29 => some [(4,3)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3)]
  | 32 => some [(4,1)]
  | 33 => some [(7,4)]
  | 34 => some [(6,3)]
  | 35 => some [(2,2)]
  | _ => some [(3,3)]
theorem root8Node66Domains1_fast_eq : root8Node66Domains1 = expandDomains root8Node66Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node66Domains1 v = expandDomains root8Node66Domains1Fast v from by decide) v
theorem root8Node66Step1Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1_checked :
    checkReplacement table25 root8Node66Domains0 root8Node66Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node66Step1Chunk0_0_checked, root8Node66Step1Chunk0_1_checked, root8Node66Step1Chunk0_2_checked, root8Node66Step1Chunk0_3_checked, root8Node66Step1Chunk0_4_checked, root8Node66Step1Chunk0_5_checked, root8Node66Step1Chunk1_0_checked, root8Node66Step1Chunk1_1_checked, root8Node66Step1Chunk1_2_checked, root8Node66Step1Chunk1_3_checked, root8Node66Step1Chunk1_4_checked, root8Node66Step1Chunk1_5_checked, root8Node66Step1Chunk2_0_checked, root8Node66Step1Chunk2_1_checked, root8Node66Step1Chunk2_2_checked, root8Node66Step1Chunk2_3_checked, root8Node66Step1Chunk2_4_checked, root8Node66Step1Chunk2_5_checked, root8Node66Step1Chunk3_0_checked, root8Node66Step1Chunk3_1_checked, root8Node66Step1Chunk3_2_checked, root8Node66Step1Chunk3_3_checked, root8Node66Step1Chunk3_4_checked, root8Node66Step1Chunk3_5_checked, root8Node66Step1Chunk4_0_checked, root8Node66Step1Chunk4_1_checked, root8Node66Step1Chunk4_2_checked, root8Node66Step1Chunk4_3_checked, root8Node66Step1Chunk4_4_checked, root8Node66Step1Chunk4_5_checked, root8Node66Step1Chunk5_0_checked, root8Node66Step1Chunk5_1_checked, root8Node66Step1Chunk5_2_checked, root8Node66Step1Chunk5_3_checked, root8Node66Step1Chunk5_4_checked, root8Node66Step1Chunk5_5_checked, root8Node66Step1Chunk6_0_checked, root8Node66Step1Chunk6_1_checked, root8Node66Step1Chunk6_2_checked, root8Node66Step1Chunk6_3_checked, root8Node66Step1Chunk6_4_checked, root8Node66Step1Chunk6_5_checked, root8Node66Step1Chunk7_0_checked, root8Node66Step1Chunk7_1_checked, root8Node66Step1Chunk7_2_checked, root8Node66Step1Chunk7_3_checked, root8Node66Step1Chunk7_4_checked, root8Node66Step1Chunk7_5_checked, root8Node66Step1Chunk8_0_checked, root8Node66Step1Chunk8_1_checked, root8Node66Step1Chunk8_2_checked, root8Node66Step1Chunk8_3_checked, root8Node66Step1Chunk8_4_checked, root8Node66Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node66Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node66Domains1 (.output 32) = true := by decide
def root8Node67Domains0 : Domains 37 State := restrict root8Node65Domains1 32 (8,1)
def root8Node67Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(5,4)]
  | 5 => some [(1,4)]
  | 6 => some [(0,5)]
  | 7 => some [(4,4)]
  | 8 => some [(6,4)]
  | 9 => some [(4,3)]
  | 10 => some [(7,5)]
  | 11 => some [(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2)]
  | 21 => some [(5,3)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(6,4)]
  | 26 => some [(1,2)]
  | 27 => some [(7,4)]
  | 28 => some [(7,0)]
  | 29 => some [(4,3)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3)]
  | 32 => some [(8,1)]
  | 33 => some [(7,4)]
  | 34 => some [(1,3),(6,3)]
  | 35 => some [(2,2),(4,2)]
  | _ => some [(3,3),(5,3)]
theorem root8Node67Domains0_fast_eq : root8Node67Domains0 = expandDomains root8Node67Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node67Domains0 v = expandDomains root8Node67Domains0Fast v from by decide) v
def root8Node67Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(7,0)]
  | 4 => [(5,4)]
  | 5 => [(1,4)]
  | 6 => [(0,5)]
  | 7 => [(4,4)]
  | 8 => [(6,4)]
  | 9 => [(4,3)]
  | 10 => [(7,5)]
  | 11 => [(6,0)]
  | 12 => [(7,1)]
  | 13 => [(7,5)]
  | 14 => [(0,3)]
  | 15 => [(7,4)]
  | 16 => [(1,3)]
  | 17 => [(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2)]
  | 21 => [(5,3)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(6,4)]
  | 26 => [(1,2)]
  | 27 => [(7,4)]
  | 28 => [(7,0)]
  | 29 => [(4,3)]
  | 30 => [(7,5)]
  | 31 => [(0,3)]
  | 32 => [(8,1)]
  | 33 => [(7,4)]
  | 34 => [(1,3)]
  | 35 => [(4,2)]
  | _ => [(5,3)]
def root8Node67Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(5,4)]
  | 5 => some [(1,4)]
  | 6 => some [(0,5)]
  | 7 => some [(4,4)]
  | 8 => some [(6,4)]
  | 9 => some [(4,3)]
  | 10 => some [(7,5)]
  | 11 => some [(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2)]
  | 21 => some [(5,3)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(6,4)]
  | 26 => some [(1,2)]
  | 27 => some [(7,4)]
  | 28 => some [(7,0)]
  | 29 => some [(4,3)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3)]
  | 32 => some [(8,1)]
  | 33 => some [(7,4)]
  | 34 => some [(1,3)]
  | 35 => some [(4,2)]
  | _ => some [(5,3)]
theorem root8Node67Domains1_fast_eq : root8Node67Domains1 = expandDomains root8Node67Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node67Domains1 v = expandDomains root8Node67Domains1Fast v from by decide) v
theorem root8Node67Step1Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1_checked :
    checkReplacement table25 root8Node67Domains0 root8Node67Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node67Step1Chunk0_0_checked, root8Node67Step1Chunk0_1_checked, root8Node67Step1Chunk0_2_checked, root8Node67Step1Chunk0_3_checked, root8Node67Step1Chunk0_4_checked, root8Node67Step1Chunk0_5_checked, root8Node67Step1Chunk1_0_checked, root8Node67Step1Chunk1_1_checked, root8Node67Step1Chunk1_2_checked, root8Node67Step1Chunk1_3_checked, root8Node67Step1Chunk1_4_checked, root8Node67Step1Chunk1_5_checked, root8Node67Step1Chunk2_0_checked, root8Node67Step1Chunk2_1_checked, root8Node67Step1Chunk2_2_checked, root8Node67Step1Chunk2_3_checked, root8Node67Step1Chunk2_4_checked, root8Node67Step1Chunk2_5_checked, root8Node67Step1Chunk3_0_checked, root8Node67Step1Chunk3_1_checked, root8Node67Step1Chunk3_2_checked, root8Node67Step1Chunk3_3_checked, root8Node67Step1Chunk3_4_checked, root8Node67Step1Chunk3_5_checked, root8Node67Step1Chunk4_0_checked, root8Node67Step1Chunk4_1_checked, root8Node67Step1Chunk4_2_checked, root8Node67Step1Chunk4_3_checked, root8Node67Step1Chunk4_4_checked, root8Node67Step1Chunk4_5_checked, root8Node67Step1Chunk5_0_checked, root8Node67Step1Chunk5_1_checked, root8Node67Step1Chunk5_2_checked, root8Node67Step1Chunk5_3_checked, root8Node67Step1Chunk5_4_checked, root8Node67Step1Chunk5_5_checked, root8Node67Step1Chunk6_0_checked, root8Node67Step1Chunk6_1_checked, root8Node67Step1Chunk6_2_checked, root8Node67Step1Chunk6_3_checked, root8Node67Step1Chunk6_4_checked, root8Node67Step1Chunk6_5_checked, root8Node67Step1Chunk7_0_checked, root8Node67Step1Chunk7_1_checked, root8Node67Step1Chunk7_2_checked, root8Node67Step1Chunk7_3_checked, root8Node67Step1Chunk7_4_checked, root8Node67Step1Chunk7_5_checked, root8Node67Step1Chunk8_0_checked, root8Node67Step1Chunk8_1_checked, root8Node67Step1Chunk8_2_checked, root8Node67Step1Chunk8_3_checked, root8Node67Step1Chunk8_4_checked, root8Node67Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node67Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node67Domains1 (.output 33) = true := by decide
def root8Node68Domains0 : Domains 37 State := restrict root8Node60Domains1 4 (8,4)
def root8Node68Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,4)]
  | 5 => some [(1,4)]
  | 6 => some [(0,5)]
  | 7 => some [(4,4)]
  | 8 => some [(1,4),(6,4)]
  | 9 => some [(4,3),(7,1)]
  | 10 => some [(7,5)]
  | 11 => some [(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3),(6,0)]
  | 15 => some [(4,0),(7,4)]
  | 16 => some [(1,3),(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2),(8,2)]
  | 21 => some [(5,0),(5,3)]
  | 22 => some [(0,1),(6,5)]
  | 23 => some [(0,4),(6,2)]
  | 24 => some [(5,4),(8,4)]
  | 25 => some [(6,4)]
  | 26 => some [(1,2)]
  | 27 => some [(7,4),(8,4)]
  | 28 => some [(1,0),(7,0)]
  | 29 => some [(4,3),(7,1)]
  | 30 => some [(3,5),(7,5)]
  | 31 => some [(0,3)]
  | 32 => some [(4,1),(8,1)]
  | 33 => some [(1,4),(4,0),(7,4),(8,0)]
  | 34 => some [(0,5),(1,3),(6,3),(7,3)]
  | 35 => some [(2,2),(2,4),(4,2)]
  | _ => some [(1,3),(3,3),(5,3)]
theorem root8Node68Domains0_fast_eq : root8Node68Domains0 = expandDomains root8Node68Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node68Domains0 v = expandDomains root8Node68Domains0Fast v from by decide) v
def root8Node68Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(7,0)]
  | 4 => [(8,4)]
  | 5 => [(1,4)]
  | 6 => [(0,5)]
  | 7 => [(4,4)]
  | 8 => [(1,4),(6,4)]
  | 9 => [(7,1)]
  | 10 => [(7,5)]
  | 11 => [(6,0)]
  | 12 => [(7,1)]
  | 13 => [(7,5)]
  | 14 => [(0,3),(6,0)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2),(8,2)]
  | 21 => [(5,0),(5,3)]
  | 22 => [(0,1)]
  | 23 => [(6,2)]
  | 24 => [(8,4)]
  | 25 => [(6,4)]
  | 26 => [(1,2)]
  | 27 => [(7,4),(8,4)]
  | 28 => [(1,0)]
  | 29 => [(7,1)]
  | 30 => [(7,5)]
  | 31 => [(0,3)]
  | 32 => [(4,1),(8,1)]
  | 33 => [(1,4),(4,0),(7,4),(8,0)]
  | 34 => [(0,5),(1,3),(6,3),(7,3)]
  | 35 => [(2,2),(2,4),(4,2)]
  | _ => [(1,3),(3,3),(5,3)]
def root8Node68Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,4)]
  | 5 => some [(1,4)]
  | 6 => some [(0,5)]
  | 7 => some [(4,4)]
  | 8 => some [(1,4),(6,4)]
  | 9 => some [(7,1)]
  | 10 => some [(7,5)]
  | 11 => some [(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3),(6,0)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2),(8,2)]
  | 21 => some [(5,0),(5,3)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(6,4)]
  | 26 => some [(1,2)]
  | 27 => some [(7,4),(8,4)]
  | 28 => some [(1,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3)]
  | 32 => some [(4,1),(8,1)]
  | 33 => some [(1,4),(4,0),(7,4),(8,0)]
  | 34 => some [(0,5),(1,3),(6,3),(7,3)]
  | 35 => some [(2,2),(2,4),(4,2)]
  | _ => some [(1,3),(3,3),(5,3)]
theorem root8Node68Domains1_fast_eq : root8Node68Domains1 = expandDomains root8Node68Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node68Domains1 v = expandDomains root8Node68Domains1Fast v from by decide) v
theorem root8Node68Step1Chunk0_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_0⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk0_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_1⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk0_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_2⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk0_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_3⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk0_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_4⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk0_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_5⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk1_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_0⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk1_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_1⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk1_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_2⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk1_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_3⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk1_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_4⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk1_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_5⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk2_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_0⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk2_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_1⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk2_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_2⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk2_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_3⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk2_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_4⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk2_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_5⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk3_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_0⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk3_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_1⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk3_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_2⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk3_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_3⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk3_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_4⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk3_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_5⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk4_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_0⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk4_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_1⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk4_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_2⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk4_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_3⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk4_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_4⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk4_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_5⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk5_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_0⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk5_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_1⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk5_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_2⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk5_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_3⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk5_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_4⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk5_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_5⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk6_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_0⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk6_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_1⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk6_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_2⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk6_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_3⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk6_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_4⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk6_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_5⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk7_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_0⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk7_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_1⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk7_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_2⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk7_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_3⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk7_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_4⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk7_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_5⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk8_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_0⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk8_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_1⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk8_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_2⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk8_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_3⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk8_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_4⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk8_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_5⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1_checked :
    checkReplacement table17 root8Node68Domains0 root8Node68Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node68Step1Chunk0_0_checked, root8Node68Step1Chunk0_1_checked, root8Node68Step1Chunk0_2_checked, root8Node68Step1Chunk0_3_checked, root8Node68Step1Chunk0_4_checked, root8Node68Step1Chunk0_5_checked, root8Node68Step1Chunk1_0_checked, root8Node68Step1Chunk1_1_checked, root8Node68Step1Chunk1_2_checked, root8Node68Step1Chunk1_3_checked, root8Node68Step1Chunk1_4_checked, root8Node68Step1Chunk1_5_checked, root8Node68Step1Chunk2_0_checked, root8Node68Step1Chunk2_1_checked, root8Node68Step1Chunk2_2_checked, root8Node68Step1Chunk2_3_checked, root8Node68Step1Chunk2_4_checked, root8Node68Step1Chunk2_5_checked, root8Node68Step1Chunk3_0_checked, root8Node68Step1Chunk3_1_checked, root8Node68Step1Chunk3_2_checked, root8Node68Step1Chunk3_3_checked, root8Node68Step1Chunk3_4_checked, root8Node68Step1Chunk3_5_checked, root8Node68Step1Chunk4_0_checked, root8Node68Step1Chunk4_1_checked, root8Node68Step1Chunk4_2_checked, root8Node68Step1Chunk4_3_checked, root8Node68Step1Chunk4_4_checked, root8Node68Step1Chunk4_5_checked, root8Node68Step1Chunk5_0_checked, root8Node68Step1Chunk5_1_checked, root8Node68Step1Chunk5_2_checked, root8Node68Step1Chunk5_3_checked, root8Node68Step1Chunk5_4_checked, root8Node68Step1Chunk5_5_checked, root8Node68Step1Chunk6_0_checked, root8Node68Step1Chunk6_1_checked, root8Node68Step1Chunk6_2_checked, root8Node68Step1Chunk6_3_checked, root8Node68Step1Chunk6_4_checked, root8Node68Step1Chunk6_5_checked, root8Node68Step1Chunk7_0_checked, root8Node68Step1Chunk7_1_checked, root8Node68Step1Chunk7_2_checked, root8Node68Step1Chunk7_3_checked, root8Node68Step1Chunk7_4_checked, root8Node68Step1Chunk7_5_checked, root8Node68Step1Chunk8_0_checked, root8Node68Step1Chunk8_1_checked, root8Node68Step1Chunk8_2_checked, root8Node68Step1Chunk8_3_checked, root8Node68Step1Chunk8_4_checked, root8Node68Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
