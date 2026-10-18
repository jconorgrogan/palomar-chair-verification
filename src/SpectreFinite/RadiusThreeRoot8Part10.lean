module

public import SpectreFinite.RadiusThreeRoot8Part9
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable10
public import SpectreFinite.RadiusThreeTable25

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node17Domains0 : Domains 37 State := restrict root8Node16Domains1 34 (1,3)
def root8Node17Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(8,1)]
  | 14 => some [(6,5)]
  | 15 => some [(2,4)]
  | 16 => some [(1,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(7,0)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(1,4)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(7,0)]
  | 29 => some [(4,3)]
  | 30 => some [(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,4)]
  | 34 => some [(1,3)]
  | 35 => some [(7,2),(8,2)]
  | _ => some [(4,0),(8,0)]
theorem root8Node17Domains0_fast_eq : root8Node17Domains0 = expandDomains root8Node17Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node17Domains0 v = expandDomains root8Node17Domains0Fast v from by decide) v
def root8Node17Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(6,3)]
  | 7 => [(7,2)]
  | 8 => [(7,4)]
  | 9 => [(0,3)]
  | 10 => [(4,1)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(8,1)]
  | 14 => [(6,5)]
  | 15 => [(2,4)]
  | 16 => [(1,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(7,0)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(1,4)]
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(7,0)]
  | 29 => [(4,3)]
  | 30 => [(7,5)]
  | 31 => [(6,0)]
  | 32 => [(7,1)]
  | 33 => [(7,4)]
  | 34 => [(1,3)]
  | 35 => [(8,2)]
  | _ => [(8,0)]
def root8Node17Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(8,1)]
  | 14 => some [(6,5)]
  | 15 => some [(2,4)]
  | 16 => some [(1,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(7,0)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(1,4)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(7,0)]
  | 29 => some [(4,3)]
  | 30 => some [(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,4)]
  | 34 => some [(1,3)]
  | 35 => some [(8,2)]
  | _ => some [(8,0)]
theorem root8Node17Domains1_fast_eq : root8Node17Domains1 = expandDomains root8Node17Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node17Domains1 v = expandDomains root8Node17Domains1Fast v from by decide) v
theorem root8Node17Step1Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root8Node17Domains0 root8Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node17Domains0 root8Node17Domains1
    root8Node17Domains0Fast root8Node17Domains1Fast
    root8Node17Domains0_fast_eq root8Node17Domains1_fast_eq (by decide)
theorem root8Node17Step1_checked :
    checkReplacement table25 root8Node17Domains0 root8Node17Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node17Step1Chunk0_0_checked, root8Node17Step1Chunk0_1_checked, root8Node17Step1Chunk0_2_checked, root8Node17Step1Chunk0_3_checked, root8Node17Step1Chunk0_4_checked, root8Node17Step1Chunk0_5_checked, root8Node17Step1Chunk1_0_checked, root8Node17Step1Chunk1_1_checked, root8Node17Step1Chunk1_2_checked, root8Node17Step1Chunk1_3_checked, root8Node17Step1Chunk1_4_checked, root8Node17Step1Chunk1_5_checked, root8Node17Step1Chunk2_0_checked, root8Node17Step1Chunk2_1_checked, root8Node17Step1Chunk2_2_checked, root8Node17Step1Chunk2_3_checked, root8Node17Step1Chunk2_4_checked, root8Node17Step1Chunk2_5_checked, root8Node17Step1Chunk3_0_checked, root8Node17Step1Chunk3_1_checked, root8Node17Step1Chunk3_2_checked, root8Node17Step1Chunk3_3_checked, root8Node17Step1Chunk3_4_checked, root8Node17Step1Chunk3_5_checked, root8Node17Step1Chunk4_0_checked, root8Node17Step1Chunk4_1_checked, root8Node17Step1Chunk4_2_checked, root8Node17Step1Chunk4_3_checked, root8Node17Step1Chunk4_4_checked, root8Node17Step1Chunk4_5_checked, root8Node17Step1Chunk5_0_checked, root8Node17Step1Chunk5_1_checked, root8Node17Step1Chunk5_2_checked, root8Node17Step1Chunk5_3_checked, root8Node17Step1Chunk5_4_checked, root8Node17Step1Chunk5_5_checked, root8Node17Step1Chunk6_0_checked, root8Node17Step1Chunk6_1_checked, root8Node17Step1Chunk6_2_checked, root8Node17Step1Chunk6_3_checked, root8Node17Step1Chunk6_4_checked, root8Node17Step1Chunk6_5_checked, root8Node17Step1Chunk7_0_checked, root8Node17Step1Chunk7_1_checked, root8Node17Step1Chunk7_2_checked, root8Node17Step1Chunk7_3_checked, root8Node17Step1Chunk7_4_checked, root8Node17Step1Chunk7_5_checked, root8Node17Step1Chunk8_0_checked, root8Node17Step1Chunk8_1_checked, root8Node17Step1Chunk8_2_checked, root8Node17Step1Chunk8_3_checked, root8Node17Step1Chunk8_4_checked, root8Node17Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node17Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node17Domains1 (.output 7) = true := by decide
def root8Node18Domains0 : Domains 37 State := restrict root8Node16Domains1 34 (6,3)
def root8Node18Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(8,1)]
  | 14 => some [(6,5)]
  | 15 => some [(2,4)]
  | 16 => some [(1,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(7,0)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(1,4)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(7,0)]
  | 29 => some [(4,3)]
  | 30 => some [(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,4)]
  | 34 => some [(6,3)]
  | 35 => some [(7,2),(8,2)]
  | _ => some [(4,0),(8,0)]
theorem root8Node18Domains0_fast_eq : root8Node18Domains0 = expandDomains root8Node18Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node18Domains0 v = expandDomains root8Node18Domains0Fast v from by decide) v
def root8Node18Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(6,3)]
  | 7 => [(7,2)]
  | 8 => [(7,4)]
  | 9 => [(0,3)]
  | 10 => [(4,1)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(8,1)]
  | 14 => [(6,5)]
  | 15 => [(2,4)]
  | 16 => [(1,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(7,0)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(1,4)]
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(7,0)]
  | 29 => [(4,3)]
  | 30 => [(7,5)]
  | 31 => [(6,0)]
  | 32 => [(7,1)]
  | 33 => [(7,4)]
  | 34 => [(6,3)]
  | 35 => [(7,2)]
  | _ => [(4,0)]
def root8Node18Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(8,1)]
  | 14 => some [(6,5)]
  | 15 => some [(2,4)]
  | 16 => some [(1,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(7,0)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(1,4)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(7,0)]
  | 29 => some [(4,3)]
  | 30 => some [(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,4)]
  | 34 => some [(6,3)]
  | 35 => some [(7,2)]
  | _ => some [(4,0)]
theorem root8Node18Domains1_fast_eq : root8Node18Domains1 = expandDomains root8Node18Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node18Domains1 v = expandDomains root8Node18Domains1Fast v from by decide) v
theorem root8Node18Step1Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root8Node18Domains0 root8Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node18Domains0 root8Node18Domains1
    root8Node18Domains0Fast root8Node18Domains1Fast
    root8Node18Domains0_fast_eq root8Node18Domains1_fast_eq (by decide)
theorem root8Node18Step1_checked :
    checkReplacement table25 root8Node18Domains0 root8Node18Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node18Step1Chunk0_0_checked, root8Node18Step1Chunk0_1_checked, root8Node18Step1Chunk0_2_checked, root8Node18Step1Chunk0_3_checked, root8Node18Step1Chunk0_4_checked, root8Node18Step1Chunk0_5_checked, root8Node18Step1Chunk1_0_checked, root8Node18Step1Chunk1_1_checked, root8Node18Step1Chunk1_2_checked, root8Node18Step1Chunk1_3_checked, root8Node18Step1Chunk1_4_checked, root8Node18Step1Chunk1_5_checked, root8Node18Step1Chunk2_0_checked, root8Node18Step1Chunk2_1_checked, root8Node18Step1Chunk2_2_checked, root8Node18Step1Chunk2_3_checked, root8Node18Step1Chunk2_4_checked, root8Node18Step1Chunk2_5_checked, root8Node18Step1Chunk3_0_checked, root8Node18Step1Chunk3_1_checked, root8Node18Step1Chunk3_2_checked, root8Node18Step1Chunk3_3_checked, root8Node18Step1Chunk3_4_checked, root8Node18Step1Chunk3_5_checked, root8Node18Step1Chunk4_0_checked, root8Node18Step1Chunk4_1_checked, root8Node18Step1Chunk4_2_checked, root8Node18Step1Chunk4_3_checked, root8Node18Step1Chunk4_4_checked, root8Node18Step1Chunk4_5_checked, root8Node18Step1Chunk5_0_checked, root8Node18Step1Chunk5_1_checked, root8Node18Step1Chunk5_2_checked, root8Node18Step1Chunk5_3_checked, root8Node18Step1Chunk5_4_checked, root8Node18Step1Chunk5_5_checked, root8Node18Step1Chunk6_0_checked, root8Node18Step1Chunk6_1_checked, root8Node18Step1Chunk6_2_checked, root8Node18Step1Chunk6_3_checked, root8Node18Step1Chunk6_4_checked, root8Node18Step1Chunk6_5_checked, root8Node18Step1Chunk7_0_checked, root8Node18Step1Chunk7_1_checked, root8Node18Step1Chunk7_2_checked, root8Node18Step1Chunk7_3_checked, root8Node18Step1Chunk7_4_checked, root8Node18Step1Chunk7_5_checked, root8Node18Step1Chunk8_0_checked, root8Node18Step1Chunk8_1_checked, root8Node18Step1Chunk8_2_checked, root8Node18Step1Chunk8_3_checked, root8Node18Step1Chunk8_4_checked, root8Node18Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node18Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node18Domains1 (.output 8) = true := by decide
def root8Node19Domains0 : Domains 37 State := restrict root8Node1Domains4 0 (7,0)
def root8Node19Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3),(5,3),(8,3)]
  | 2 => some [(7,5),(8,5)]
  | 3 => some [(1,0),(6,0),(7,0)]
  | 4 => some [(1,2),(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(4,0),(7,4)]
  | 9 => some [(0,3),(1,1),(6,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(4,1),(5,1),(8,1)]
  | 14 => some [(0,1),(0,2),(6,5)]
  | 15 => some [(2,0),(2,2),(2,4),(4,0)]
  | 16 => some [(1,3),(3,3),(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(5,2),(5,5)]
  | 21 => some [(1,0),(3,0),(5,0),(7,0)]
  | 22 => some [(0,1),(6,5)]
  | 23 => some [(0,4),(6,2)]
  | 24 => some [(5,4),(8,4)]
  | 25 => some [(1,4),(6,4)]
  | 26 => some [(0,5),(1,2)]
  | 27 => some [(4,4),(8,4)]
  | 28 => some [(1,0),(7,0)]
  | 29 => some [(4,3),(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3),(6,0)]
  | 32 => some [(7,1),(8,1)]
  | 33 => some [(4,0),(7,4),(8,0)]
  | 34 => some [(1,3),(6,3),(7,3)]
  | 35 => some [(4,2),(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(5,3),(8,0)]
theorem root8Node19Domains0_fast_eq : root8Node19Domains0 = expandDomains root8Node19Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node19Domains0 v = expandDomains root8Node19Domains0Fast v from by decide) v
def root8Node19Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3),(8,3)]
  | 2 => [(7,5),(8,5)]
  | 3 => [(1,0),(6,0),(7,0)]
  | 4 => [(7,2)]
  | 5 => [(7,4)]
  | 6 => [(6,3)]
  | 7 => [(7,2)]
  | 8 => [(4,0),(7,4)]
  | 9 => [(1,1),(6,1)]
  | 10 => [(4,1)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(4,1),(5,1),(8,1)]
  | 14 => [(0,1),(0,2),(6,5)]
  | 15 => [(2,0),(4,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(5,2),(5,5)]
  | 21 => [(1,0),(3,0),(5,0),(7,0)]
  | 22 => [(0,1)]
  | 23 => [(6,2)]
  | 24 => [(8,4)]
  | 25 => [(1,4),(6,4)]
  | 26 => [(0,5),(1,2)]
  | 27 => [(4,4),(8,4)]
  | 28 => [(1,0),(7,0)]
  | 29 => [(4,3),(7,1)]
  | 30 => [(7,5)]
  | 31 => [(0,3),(6,0)]
  | 32 => [(7,1),(8,1)]
  | 33 => [(4,0),(7,4),(8,0)]
  | 34 => [(1,3),(6,3),(7,3)]
  | 35 => [(4,2),(7,2),(8,2)]
  | _ => [(4,0),(5,0),(5,3),(8,0)]
def root8Node19Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3),(8,3)]
  | 2 => some [(7,5),(8,5)]
  | 3 => some [(1,0),(6,0),(7,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(4,0),(7,4)]
  | 9 => some [(1,1),(6,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(4,1),(5,1),(8,1)]
  | 14 => some [(0,1),(0,2),(6,5)]
  | 15 => some [(2,0),(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(5,2),(5,5)]
  | 21 => some [(1,0),(3,0),(5,0),(7,0)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(1,4),(6,4)]
  | 26 => some [(0,5),(1,2)]
  | 27 => some [(4,4),(8,4)]
  | 28 => some [(1,0),(7,0)]
  | 29 => some [(4,3),(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3),(6,0)]
  | 32 => some [(7,1),(8,1)]
  | 33 => some [(4,0),(7,4),(8,0)]
  | 34 => some [(1,3),(6,3),(7,3)]
  | 35 => some [(4,2),(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(5,3),(8,0)]
theorem root8Node19Domains1_fast_eq : root8Node19Domains1 = expandDomains root8Node19Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node19Domains1 v = expandDomains root8Node19Domains1Fast v from by decide) v
theorem root8Node19Step1Chunk0_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_0⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk0_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_1⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk0_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_2⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk0_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_3⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk0_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_4⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk0_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_5⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk1_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_0⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk1_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_1⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk1_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_2⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk1_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_3⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk1_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_4⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk1_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_5⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk2_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_0⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk2_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_1⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk2_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_2⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk2_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_3⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk2_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_4⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk2_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_5⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk3_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_0⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk3_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_1⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk3_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_2⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk3_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_3⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk3_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_4⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk3_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_5⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk4_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_0⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk4_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_1⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk4_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_2⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk4_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_3⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk4_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_4⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk4_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_5⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk5_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_0⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk5_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_1⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk5_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_2⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk5_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_3⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk5_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_4⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk5_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_5⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk6_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_0⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk6_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_1⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk6_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_2⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk6_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_3⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk6_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_4⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk6_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_5⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk7_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_0⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk7_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_1⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk7_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_2⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk7_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_3⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk7_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_4⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk7_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_5⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk8_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_0⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk8_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_1⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk8_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_2⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk8_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_3⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk8_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_4⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1Chunk8_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_5⟩
      root8Node19Domains0 root8Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node19Domains0 root8Node19Domains1
    root8Node19Domains0Fast root8Node19Domains1Fast
    root8Node19Domains0_fast_eq root8Node19Domains1_fast_eq (by decide)
theorem root8Node19Step1_checked :
    checkReplacement table10 root8Node19Domains0 root8Node19Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node19Step1Chunk0_0_checked, root8Node19Step1Chunk0_1_checked, root8Node19Step1Chunk0_2_checked, root8Node19Step1Chunk0_3_checked, root8Node19Step1Chunk0_4_checked, root8Node19Step1Chunk0_5_checked, root8Node19Step1Chunk1_0_checked, root8Node19Step1Chunk1_1_checked, root8Node19Step1Chunk1_2_checked, root8Node19Step1Chunk1_3_checked, root8Node19Step1Chunk1_4_checked, root8Node19Step1Chunk1_5_checked, root8Node19Step1Chunk2_0_checked, root8Node19Step1Chunk2_1_checked, root8Node19Step1Chunk2_2_checked, root8Node19Step1Chunk2_3_checked, root8Node19Step1Chunk2_4_checked, root8Node19Step1Chunk2_5_checked, root8Node19Step1Chunk3_0_checked, root8Node19Step1Chunk3_1_checked, root8Node19Step1Chunk3_2_checked, root8Node19Step1Chunk3_3_checked, root8Node19Step1Chunk3_4_checked, root8Node19Step1Chunk3_5_checked, root8Node19Step1Chunk4_0_checked, root8Node19Step1Chunk4_1_checked, root8Node19Step1Chunk4_2_checked, root8Node19Step1Chunk4_3_checked, root8Node19Step1Chunk4_4_checked, root8Node19Step1Chunk4_5_checked, root8Node19Step1Chunk5_0_checked, root8Node19Step1Chunk5_1_checked, root8Node19Step1Chunk5_2_checked, root8Node19Step1Chunk5_3_checked, root8Node19Step1Chunk5_4_checked, root8Node19Step1Chunk5_5_checked, root8Node19Step1Chunk6_0_checked, root8Node19Step1Chunk6_1_checked, root8Node19Step1Chunk6_2_checked, root8Node19Step1Chunk6_3_checked, root8Node19Step1Chunk6_4_checked, root8Node19Step1Chunk6_5_checked, root8Node19Step1Chunk7_0_checked, root8Node19Step1Chunk7_1_checked, root8Node19Step1Chunk7_2_checked, root8Node19Step1Chunk7_3_checked, root8Node19Step1Chunk7_4_checked, root8Node19Step1Chunk7_5_checked, root8Node19Step1Chunk8_0_checked, root8Node19Step1Chunk8_1_checked, root8Node19Step1Chunk8_2_checked, root8Node19Step1Chunk8_3_checked, root8Node19Step1Chunk8_4_checked, root8Node19Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
