module

public import SpectreFinite.RadiusThreeRoot8Part13
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable22
public import SpectreFinite.RadiusThreeTable4
public import SpectreFinite.RadiusThreeTable8

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node24Domains0 : Domains 37 State := restrict root8Node22Domains2 9 (6,1)
def root8Node24Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(4,0)]
  | 9 => some [(6,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(5,1)]
  | 14 => some [(0,1)]
  | 15 => some [(2,0),(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(1,0)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(1,4)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(1,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(4,0),(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(8,2)]
  | _ => some [(5,0)]
theorem root8Node24Domains0_fast_eq : root8Node24Domains0 = expandDomains root8Node24Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node24Domains0 v = expandDomains root8Node24Domains0Fast v from by decide) v
def root8Node24Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,2)]
  | 5 => [(7,4)]
  | 6 => [(6,3)]
  | 7 => [(7,2)]
  | 8 => [(4,0)]
  | 9 => [(6,1)]
  | 10 => [(4,1)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(2,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(1,0)]
  | 22 => [(0,1)]
  | 23 => [(6,2)]
  | 24 => [(8,4)]
  | 25 => [(1,4)]
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(1,0)]
  | 29 => [(7,1)]
  | 30 => [(7,5)]
  | 31 => [(6,0)]
  | 32 => [(7,1)]
  | 33 => [(4,0)]
  | 34 => [(7,3)]
  | 35 => [(8,2)]
  | _ => [(5,0)]
def root8Node24Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(4,0)]
  | 9 => some [(6,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(5,1)]
  | 14 => some [(0,1)]
  | 15 => some [(2,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(1,0)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(1,4)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(1,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(4,0)]
  | 34 => some [(7,3)]
  | 35 => some [(8,2)]
  | _ => some [(5,0)]
theorem root8Node24Domains1_fast_eq : root8Node24Domains1 = expandDomains root8Node24Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node24Domains1 v = expandDomains root8Node24Domains1Fast v from by decide) v
theorem root8Node24Step1Chunk0_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_0⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk0_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_1⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk0_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_2⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk0_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_3⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk0_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_4⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk0_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_5⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk1_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_0⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk1_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_1⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk1_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_2⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk1_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_3⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk1_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_4⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk1_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_5⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk2_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_0⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk2_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_1⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk2_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_2⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk2_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_3⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk2_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_4⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk2_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_5⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk3_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_0⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk3_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_1⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk3_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_2⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk3_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_3⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk3_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_4⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk3_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_5⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk4_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_0⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk4_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_1⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk4_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_2⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk4_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_3⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk4_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_4⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk4_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_5⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk5_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_0⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk5_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_1⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk5_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_2⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk5_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_3⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk5_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_4⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk5_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_5⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk6_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_0⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk6_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_1⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk6_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_2⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk6_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_3⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk6_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_4⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk6_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_5⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk7_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_0⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk7_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_1⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk7_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_2⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk7_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_3⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk7_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_4⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk7_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_5⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk8_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_0⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk8_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_1⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk8_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_2⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk8_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_3⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk8_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_4⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1Chunk8_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_5⟩
      root8Node24Domains0 root8Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node24Domains0 root8Node24Domains1
    root8Node24Domains0Fast root8Node24Domains1Fast
    root8Node24Domains0_fast_eq root8Node24Domains1_fast_eq (by decide)
theorem root8Node24Step1_checked :
    checkReplacement table22 root8Node24Domains0 root8Node24Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node24Step1Chunk0_0_checked, root8Node24Step1Chunk0_1_checked, root8Node24Step1Chunk0_2_checked, root8Node24Step1Chunk0_3_checked, root8Node24Step1Chunk0_4_checked, root8Node24Step1Chunk0_5_checked, root8Node24Step1Chunk1_0_checked, root8Node24Step1Chunk1_1_checked, root8Node24Step1Chunk1_2_checked, root8Node24Step1Chunk1_3_checked, root8Node24Step1Chunk1_4_checked, root8Node24Step1Chunk1_5_checked, root8Node24Step1Chunk2_0_checked, root8Node24Step1Chunk2_1_checked, root8Node24Step1Chunk2_2_checked, root8Node24Step1Chunk2_3_checked, root8Node24Step1Chunk2_4_checked, root8Node24Step1Chunk2_5_checked, root8Node24Step1Chunk3_0_checked, root8Node24Step1Chunk3_1_checked, root8Node24Step1Chunk3_2_checked, root8Node24Step1Chunk3_3_checked, root8Node24Step1Chunk3_4_checked, root8Node24Step1Chunk3_5_checked, root8Node24Step1Chunk4_0_checked, root8Node24Step1Chunk4_1_checked, root8Node24Step1Chunk4_2_checked, root8Node24Step1Chunk4_3_checked, root8Node24Step1Chunk4_4_checked, root8Node24Step1Chunk4_5_checked, root8Node24Step1Chunk5_0_checked, root8Node24Step1Chunk5_1_checked, root8Node24Step1Chunk5_2_checked, root8Node24Step1Chunk5_3_checked, root8Node24Step1Chunk5_4_checked, root8Node24Step1Chunk5_5_checked, root8Node24Step1Chunk6_0_checked, root8Node24Step1Chunk6_1_checked, root8Node24Step1Chunk6_2_checked, root8Node24Step1Chunk6_3_checked, root8Node24Step1Chunk6_4_checked, root8Node24Step1Chunk6_5_checked, root8Node24Step1Chunk7_0_checked, root8Node24Step1Chunk7_1_checked, root8Node24Step1Chunk7_2_checked, root8Node24Step1Chunk7_3_checked, root8Node24Step1Chunk7_4_checked, root8Node24Step1Chunk7_5_checked, root8Node24Step1Chunk8_0_checked, root8Node24Step1Chunk8_1_checked, root8Node24Step1Chunk8_2_checked, root8Node24Step1Chunk8_3_checked, root8Node24Step1Chunk8_4_checked, root8Node24Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node24Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node24Domains1 (.output 11) = true := by decide
def root8Node25Domains0 : Domains 37 State := restrict root8Node21Domains1 3 (7,0)
def root8Node25Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
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
  | 28 => some [(1,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3),(6,0)]
  | 32 => some [(7,1),(8,1)]
  | 33 => some [(4,0),(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(4,2),(8,2)]
  | _ => some [(5,0),(5,3),(8,0)]
theorem root8Node25Domains0_fast_eq : root8Node25Domains0 = expandDomains root8Node25Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node25Domains0 v = expandDomains root8Node25Domains0Fast v from by decide) v
def root8Node25Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(7,2)]
  | 5 => [(7,4)]
  | 6 => [(6,3)]
  | 7 => [(7,2)]
  | 8 => [(7,4)]
  | 9 => [(1,1),(6,1)]
  | 10 => [(4,1)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(4,1),(8,1)]
  | 14 => [(0,2),(6,5)]
  | 15 => [(2,0),(4,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(5,2),(5,5)]
  | 21 => [(3,0),(5,0),(7,0)]
  | 22 => [(0,1)]
  | 23 => [(6,2)]
  | 24 => [(8,4)]
  | 25 => [(1,4),(6,4)]
  | 26 => [(0,5),(1,2)]
  | 27 => [(4,4),(8,4)]
  | 28 => [(1,0)]
  | 29 => [(7,1)]
  | 30 => [(7,5)]
  | 31 => [(0,3),(6,0)]
  | 32 => [(7,1),(8,1)]
  | 33 => [(4,0),(8,0)]
  | 34 => [(7,3)]
  | 35 => [(4,2),(8,2)]
  | _ => [(5,0),(5,3),(8,0)]
def root8Node25Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(1,1),(6,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(4,1),(8,1)]
  | 14 => some [(0,2),(6,5)]
  | 15 => some [(2,0),(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(5,2),(5,5)]
  | 21 => some [(3,0),(5,0),(7,0)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(1,4),(6,4)]
  | 26 => some [(0,5),(1,2)]
  | 27 => some [(4,4),(8,4)]
  | 28 => some [(1,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3),(6,0)]
  | 32 => some [(7,1),(8,1)]
  | 33 => some [(4,0),(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(4,2),(8,2)]
  | _ => some [(5,0),(5,3),(8,0)]
theorem root8Node25Domains1_fast_eq : root8Node25Domains1 = expandDomains root8Node25Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node25Domains1 v = expandDomains root8Node25Domains1Fast v from by decide) v
theorem root8Node25Step1Chunk0_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_0⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk0_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_1⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk0_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_2⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk0_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_3⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk0_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_4⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk0_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_5⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk1_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_0⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk1_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_1⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk1_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_2⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk1_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_3⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk1_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_4⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk1_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_5⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk2_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_0⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk2_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_1⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk2_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_2⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk2_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_3⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk2_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_4⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk2_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_5⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk3_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_0⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk3_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_1⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk3_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_2⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk3_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_3⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk3_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_4⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk3_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_5⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk4_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_0⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk4_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_1⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk4_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_2⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk4_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_3⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk4_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_4⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk4_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_5⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk5_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_0⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk5_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_1⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk5_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_2⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk5_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_3⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk5_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_4⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk5_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_5⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk6_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_0⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk6_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_1⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk6_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_2⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk6_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_3⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk6_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_4⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk6_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_5⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk7_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_0⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk7_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_1⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk7_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_2⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk7_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_3⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk7_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_4⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk7_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_5⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk8_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_0⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk8_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_1⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk8_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_2⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk8_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_3⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk8_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_4⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1Chunk8_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_5⟩
      root8Node25Domains0 root8Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node25Domains0 root8Node25Domains1
    root8Node25Domains0Fast root8Node25Domains1Fast
    root8Node25Domains0_fast_eq root8Node25Domains1_fast_eq (by decide)
theorem root8Node25Step1_checked :
    checkReplacement table8 root8Node25Domains0 root8Node25Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node25Step1Chunk0_0_checked, root8Node25Step1Chunk0_1_checked, root8Node25Step1Chunk0_2_checked, root8Node25Step1Chunk0_3_checked, root8Node25Step1Chunk0_4_checked, root8Node25Step1Chunk0_5_checked, root8Node25Step1Chunk1_0_checked, root8Node25Step1Chunk1_1_checked, root8Node25Step1Chunk1_2_checked, root8Node25Step1Chunk1_3_checked, root8Node25Step1Chunk1_4_checked, root8Node25Step1Chunk1_5_checked, root8Node25Step1Chunk2_0_checked, root8Node25Step1Chunk2_1_checked, root8Node25Step1Chunk2_2_checked, root8Node25Step1Chunk2_3_checked, root8Node25Step1Chunk2_4_checked, root8Node25Step1Chunk2_5_checked, root8Node25Step1Chunk3_0_checked, root8Node25Step1Chunk3_1_checked, root8Node25Step1Chunk3_2_checked, root8Node25Step1Chunk3_3_checked, root8Node25Step1Chunk3_4_checked, root8Node25Step1Chunk3_5_checked, root8Node25Step1Chunk4_0_checked, root8Node25Step1Chunk4_1_checked, root8Node25Step1Chunk4_2_checked, root8Node25Step1Chunk4_3_checked, root8Node25Step1Chunk4_4_checked, root8Node25Step1Chunk4_5_checked, root8Node25Step1Chunk5_0_checked, root8Node25Step1Chunk5_1_checked, root8Node25Step1Chunk5_2_checked, root8Node25Step1Chunk5_3_checked, root8Node25Step1Chunk5_4_checked, root8Node25Step1Chunk5_5_checked, root8Node25Step1Chunk6_0_checked, root8Node25Step1Chunk6_1_checked, root8Node25Step1Chunk6_2_checked, root8Node25Step1Chunk6_3_checked, root8Node25Step1Chunk6_4_checked, root8Node25Step1Chunk6_5_checked, root8Node25Step1Chunk7_0_checked, root8Node25Step1Chunk7_1_checked, root8Node25Step1Chunk7_2_checked, root8Node25Step1Chunk7_3_checked, root8Node25Step1Chunk7_4_checked, root8Node25Step1Chunk7_5_checked, root8Node25Step1Chunk8_0_checked, root8Node25Step1Chunk8_1_checked, root8Node25Step1Chunk8_2_checked, root8Node25Step1Chunk8_3_checked, root8Node25Step1Chunk8_4_checked, root8Node25Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node26Domains0 : Domains 37 State := restrict root8Node25Domains1 9 (1,1)
def root8Node26Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(1,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(4,1),(8,1)]
  | 14 => some [(0,2),(6,5)]
  | 15 => some [(2,0),(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(5,2),(5,5)]
  | 21 => some [(3,0),(5,0),(7,0)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(1,4),(6,4)]
  | 26 => some [(0,5),(1,2)]
  | 27 => some [(4,4),(8,4)]
  | 28 => some [(1,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3),(6,0)]
  | 32 => some [(7,1),(8,1)]
  | 33 => some [(4,0),(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(4,2),(8,2)]
  | _ => some [(5,0),(5,3),(8,0)]
theorem root8Node26Domains0_fast_eq : root8Node26Domains0 = expandDomains root8Node26Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node26Domains0 v = expandDomains root8Node26Domains0Fast v from by decide) v
def root8Node26Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(7,2)]
  | 5 => [(7,4)]
  | 6 => [(6,3)]
  | 7 => [(7,2)]
  | 8 => [(7,4)]
  | 9 => [(1,1)]
  | 10 => [(4,1)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(4,1),(8,1)]
  | 14 => [(0,2),(6,5)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(5,2),(5,5)]
  | 21 => [(3,0),(5,0),(7,0)]
  | 22 => [(0,1)]
  | 23 => [(6,2)]
  | 24 => [(8,4)]
  | 25 => [(1,4),(6,4)]
  | 26 => [(0,5),(1,2)]
  | 27 => [(4,4),(8,4)]
  | 28 => [(1,0)]
  | 29 => [(7,1)]
  | 30 => [(7,5)]
  | 31 => [(0,3),(6,0)]
  | 32 => [(7,1),(8,1)]
  | 33 => [(4,0),(8,0)]
  | 34 => [(7,3)]
  | 35 => [(4,2),(8,2)]
  | _ => [(5,0),(5,3),(8,0)]
def root8Node26Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(1,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(4,1),(8,1)]
  | 14 => some [(0,2),(6,5)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(5,2),(5,5)]
  | 21 => some [(3,0),(5,0),(7,0)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(1,4),(6,4)]
  | 26 => some [(0,5),(1,2)]
  | 27 => some [(4,4),(8,4)]
  | 28 => some [(1,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3),(6,0)]
  | 32 => some [(7,1),(8,1)]
  | 33 => some [(4,0),(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(4,2),(8,2)]
  | _ => some [(5,0),(5,3),(8,0)]
theorem root8Node26Domains1_fast_eq : root8Node26Domains1 = expandDomains root8Node26Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node26Domains1 v = expandDomains root8Node26Domains1Fast v from by decide) v
theorem root8Node26Step1Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root8Node26Domains0 root8Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node26Domains0 root8Node26Domains1
    root8Node26Domains0Fast root8Node26Domains1Fast
    root8Node26Domains0_fast_eq root8Node26Domains1_fast_eq (by decide)
theorem root8Node26Step1_checked :
    checkReplacement table4 root8Node26Domains0 root8Node26Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node26Step1Chunk0_0_checked, root8Node26Step1Chunk0_1_checked, root8Node26Step1Chunk0_2_checked, root8Node26Step1Chunk0_3_checked, root8Node26Step1Chunk0_4_checked, root8Node26Step1Chunk0_5_checked, root8Node26Step1Chunk1_0_checked, root8Node26Step1Chunk1_1_checked, root8Node26Step1Chunk1_2_checked, root8Node26Step1Chunk1_3_checked, root8Node26Step1Chunk1_4_checked, root8Node26Step1Chunk1_5_checked, root8Node26Step1Chunk2_0_checked, root8Node26Step1Chunk2_1_checked, root8Node26Step1Chunk2_2_checked, root8Node26Step1Chunk2_3_checked, root8Node26Step1Chunk2_4_checked, root8Node26Step1Chunk2_5_checked, root8Node26Step1Chunk3_0_checked, root8Node26Step1Chunk3_1_checked, root8Node26Step1Chunk3_2_checked, root8Node26Step1Chunk3_3_checked, root8Node26Step1Chunk3_4_checked, root8Node26Step1Chunk3_5_checked, root8Node26Step1Chunk4_0_checked, root8Node26Step1Chunk4_1_checked, root8Node26Step1Chunk4_2_checked, root8Node26Step1Chunk4_3_checked, root8Node26Step1Chunk4_4_checked, root8Node26Step1Chunk4_5_checked, root8Node26Step1Chunk5_0_checked, root8Node26Step1Chunk5_1_checked, root8Node26Step1Chunk5_2_checked, root8Node26Step1Chunk5_3_checked, root8Node26Step1Chunk5_4_checked, root8Node26Step1Chunk5_5_checked, root8Node26Step1Chunk6_0_checked, root8Node26Step1Chunk6_1_checked, root8Node26Step1Chunk6_2_checked, root8Node26Step1Chunk6_3_checked, root8Node26Step1Chunk6_4_checked, root8Node26Step1Chunk6_5_checked, root8Node26Step1Chunk7_0_checked, root8Node26Step1Chunk7_1_checked, root8Node26Step1Chunk7_2_checked, root8Node26Step1Chunk7_3_checked, root8Node26Step1Chunk7_4_checked, root8Node26Step1Chunk7_5_checked, root8Node26Step1Chunk8_0_checked, root8Node26Step1Chunk8_1_checked, root8Node26Step1Chunk8_2_checked, root8Node26Step1Chunk8_3_checked, root8Node26Step1Chunk8_4_checked, root8Node26Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
