module

public import SpectreFinite.RadiusThreeRoot6Part19
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable13
public import SpectreFinite.RadiusThreeTable2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node36Domains0 : Domains 37 State := restrict root6Node35Domains2 14 (1,4)
def root6Node36Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(5,5)]
  | 5 => some [(7,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(7,0)]
  | 9 => some [(0,5)]
  | 10 => some [(4,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(1,4)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(6,0)]
  | 22 => some [(4,0)]
  | 23 => some [(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(8,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2),(8,2)]
  | 28 => some [(0,1)]
  | 29 => some [(6,2)]
  | 30 => some [(8,4)]
  | 31 => some [(6,4)]
  | 32 => some [(1,2)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(7,5)]
  | _ => some [(0,3)]
theorem root6Node36Domains0_fast_eq : root6Node36Domains0 = expandDomains root6Node36Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node36Domains0 v = expandDomains root6Node36Domains0Fast v from by decide) v
def root6Node36Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(5,5)]
  | 5 => [(7,0)]
  | 6 => [(8,3)]
  | 7 => [(5,5)]
  | 8 => [(7,0)]
  | 9 => [(0,5)]
  | 10 => [(4,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(1,4)]
  | 15 => [(6,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(4,0)]
  | 23 => [(7,3)]
  | 24 => [(8,2)]
  | 25 => [(8,0)]
  | 26 => [(7,3)]
  | 27 => [(8,2)]
  | 28 => [(0,1)]
  | 29 => [(6,2)]
  | 30 => [(8,4)]
  | 31 => [(6,4)]
  | 32 => [(1,2)]
  | 33 => [(1,0)]
  | 34 => [(7,1)]
  | 35 => [(7,5)]
  | _ => [(0,3)]
def root6Node36Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(5,5)]
  | 5 => some [(7,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(7,0)]
  | 9 => some [(0,5)]
  | 10 => some [(4,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(1,4)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(4,0)]
  | 23 => some [(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(8,0)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(0,1)]
  | 29 => some [(6,2)]
  | 30 => some [(8,4)]
  | 31 => some [(6,4)]
  | 32 => some [(1,2)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(7,5)]
  | _ => some [(0,3)]
theorem root6Node36Domains1_fast_eq : root6Node36Domains1 = expandDomains root6Node36Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node36Domains1 v = expandDomains root6Node36Domains1Fast v from by decide) v
theorem root6Node36Step1Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root6Node36Domains0 root6Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains0 root6Node36Domains1
    root6Node36Domains0Fast root6Node36Domains1Fast
    root6Node36Domains0_fast_eq root6Node36Domains1_fast_eq (by decide)
theorem root6Node36Step1_checked :
    checkReplacement table13 root6Node36Domains0 root6Node36Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node36Step1Chunk0_0_checked, root6Node36Step1Chunk0_1_checked, root6Node36Step1Chunk0_2_checked, root6Node36Step1Chunk0_3_checked, root6Node36Step1Chunk0_4_checked, root6Node36Step1Chunk0_5_checked, root6Node36Step1Chunk1_0_checked, root6Node36Step1Chunk1_1_checked, root6Node36Step1Chunk1_2_checked, root6Node36Step1Chunk1_3_checked, root6Node36Step1Chunk1_4_checked, root6Node36Step1Chunk1_5_checked, root6Node36Step1Chunk2_0_checked, root6Node36Step1Chunk2_1_checked, root6Node36Step1Chunk2_2_checked, root6Node36Step1Chunk2_3_checked, root6Node36Step1Chunk2_4_checked, root6Node36Step1Chunk2_5_checked, root6Node36Step1Chunk3_0_checked, root6Node36Step1Chunk3_1_checked, root6Node36Step1Chunk3_2_checked, root6Node36Step1Chunk3_3_checked, root6Node36Step1Chunk3_4_checked, root6Node36Step1Chunk3_5_checked, root6Node36Step1Chunk4_0_checked, root6Node36Step1Chunk4_1_checked, root6Node36Step1Chunk4_2_checked, root6Node36Step1Chunk4_3_checked, root6Node36Step1Chunk4_4_checked, root6Node36Step1Chunk4_5_checked, root6Node36Step1Chunk5_0_checked, root6Node36Step1Chunk5_1_checked, root6Node36Step1Chunk5_2_checked, root6Node36Step1Chunk5_3_checked, root6Node36Step1Chunk5_4_checked, root6Node36Step1Chunk5_5_checked, root6Node36Step1Chunk6_0_checked, root6Node36Step1Chunk6_1_checked, root6Node36Step1Chunk6_2_checked, root6Node36Step1Chunk6_3_checked, root6Node36Step1Chunk6_4_checked, root6Node36Step1Chunk6_5_checked, root6Node36Step1Chunk7_0_checked, root6Node36Step1Chunk7_1_checked, root6Node36Step1Chunk7_2_checked, root6Node36Step1Chunk7_3_checked, root6Node36Step1Chunk7_4_checked, root6Node36Step1Chunk7_5_checked, root6Node36Step1Chunk8_0_checked, root6Node36Step1Chunk8_1_checked, root6Node36Step1Chunk8_2_checked, root6Node36Step1Chunk8_3_checked, root6Node36Step1Chunk8_4_checked, root6Node36Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root6Node36Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node36Domains1 (.output 17) = true := by decide
def root6Node37Domains0 : Domains 37 State := restrict root6Node35Domains2 14 (6,4)
def root6Node37Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(5,5)]
  | 5 => some [(7,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(7,0)]
  | 9 => some [(0,5)]
  | 10 => some [(4,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(6,4)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(6,0)]
  | 22 => some [(4,0)]
  | 23 => some [(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(8,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2),(8,2)]
  | 28 => some [(0,1)]
  | 29 => some [(6,2)]
  | 30 => some [(8,4)]
  | 31 => some [(6,4)]
  | 32 => some [(1,2)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(7,5)]
  | _ => some [(0,3)]
theorem root6Node37Domains0_fast_eq : root6Node37Domains0 = expandDomains root6Node37Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node37Domains0 v = expandDomains root6Node37Domains0Fast v from by decide) v
def root6Node37Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(5,5)]
  | 5 => [(7,0)]
  | 6 => [(8,3)]
  | 7 => [(5,5)]
  | 8 => [(7,0)]
  | 9 => [(0,5)]
  | 10 => [(4,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(6,4)]
  | 15 => [(6,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(0,3)]
  | 22 => [(4,0)]
  | 23 => [(7,3)]
  | 24 => [(8,2)]
  | 25 => [(8,0)]
  | 26 => [(7,3)]
  | 27 => [(4,2)]
  | 28 => [(0,1)]
  | 29 => [(6,2)]
  | 30 => [(8,4)]
  | 31 => [(6,4)]
  | 32 => [(1,2)]
  | 33 => [(1,0)]
  | 34 => [(7,1)]
  | 35 => [(7,5)]
  | _ => [(0,3)]
def root6Node37Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(5,5)]
  | 5 => some [(7,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(7,0)]
  | 9 => some [(0,5)]
  | 10 => some [(4,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(6,4)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3)]
  | 22 => some [(4,0)]
  | 23 => some [(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(8,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(0,1)]
  | 29 => some [(6,2)]
  | 30 => some [(8,4)]
  | 31 => some [(6,4)]
  | 32 => some [(1,2)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(7,5)]
  | _ => some [(0,3)]
theorem root6Node37Domains1_fast_eq : root6Node37Domains1 = expandDomains root6Node37Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node37Domains1 v = expandDomains root6Node37Domains1Fast v from by decide) v
theorem root6Node37Step1Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1_checked :
    checkReplacement table13 root6Node37Domains0 root6Node37Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node37Step1Chunk0_0_checked, root6Node37Step1Chunk0_1_checked, root6Node37Step1Chunk0_2_checked, root6Node37Step1Chunk0_3_checked, root6Node37Step1Chunk0_4_checked, root6Node37Step1Chunk0_5_checked, root6Node37Step1Chunk1_0_checked, root6Node37Step1Chunk1_1_checked, root6Node37Step1Chunk1_2_checked, root6Node37Step1Chunk1_3_checked, root6Node37Step1Chunk1_4_checked, root6Node37Step1Chunk1_5_checked, root6Node37Step1Chunk2_0_checked, root6Node37Step1Chunk2_1_checked, root6Node37Step1Chunk2_2_checked, root6Node37Step1Chunk2_3_checked, root6Node37Step1Chunk2_4_checked, root6Node37Step1Chunk2_5_checked, root6Node37Step1Chunk3_0_checked, root6Node37Step1Chunk3_1_checked, root6Node37Step1Chunk3_2_checked, root6Node37Step1Chunk3_3_checked, root6Node37Step1Chunk3_4_checked, root6Node37Step1Chunk3_5_checked, root6Node37Step1Chunk4_0_checked, root6Node37Step1Chunk4_1_checked, root6Node37Step1Chunk4_2_checked, root6Node37Step1Chunk4_3_checked, root6Node37Step1Chunk4_4_checked, root6Node37Step1Chunk4_5_checked, root6Node37Step1Chunk5_0_checked, root6Node37Step1Chunk5_1_checked, root6Node37Step1Chunk5_2_checked, root6Node37Step1Chunk5_3_checked, root6Node37Step1Chunk5_4_checked, root6Node37Step1Chunk5_5_checked, root6Node37Step1Chunk6_0_checked, root6Node37Step1Chunk6_1_checked, root6Node37Step1Chunk6_2_checked, root6Node37Step1Chunk6_3_checked, root6Node37Step1Chunk6_4_checked, root6Node37Step1Chunk6_5_checked, root6Node37Step1Chunk7_0_checked, root6Node37Step1Chunk7_1_checked, root6Node37Step1Chunk7_2_checked, root6Node37Step1Chunk7_3_checked, root6Node37Step1Chunk7_4_checked, root6Node37Step1Chunk7_5_checked, root6Node37Step1Chunk8_0_checked, root6Node37Step1Chunk8_1_checked, root6Node37Step1Chunk8_2_checked, root6Node37Step1Chunk8_3_checked, root6Node37Step1Chunk8_4_checked, root6Node37Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root6Node37Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node37Domains1 (.output 18) = true := by decide
def root6Node38Domains0 : Domains 37 State := restrict root6Node30Domains3 0 (6,5)
def root6Node38Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4),(6,1)]
  | 2 => some [(5,1),(5,4),(8,1)]
  | 3 => some [(0,0),(0,1),(6,4),(6,5)]
  | 4 => some [(5,5)]
  | 5 => some [(7,0)]
  | 6 => some [(4,3),(8,3)]
  | 7 => some [(1,5),(3,5),(5,5)]
  | 8 => some [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 9 => some [(0,5)]
  | 10 => some [(4,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0),(2,4),(4,4)]
  | 14 => some [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(3,1),(7,1)]
  | 20 => some [(0,1),(1,5),(6,5),(7,5)]
  | 21 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 22 => some [(4,0),(8,0)]
  | 23 => some [(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(5,0),(8,0)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(1,0),(4,2),(7,0),(8,2)]
  | 28 => some [(0,1),(6,4)]
  | 29 => some [(1,2),(6,2)]
  | 30 => some [(8,4)]
  | 31 => some [(0,0),(6,4)]
  | 32 => some [(1,2),(7,2)]
  | 33 => some [(0,3),(1,0)]
  | 34 => some [(7,1),(8,1)]
  | 35 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root6Node38Domains0_fast_eq : root6Node38Domains0 = expandDomains root6Node38Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node38Domains0 v = expandDomains root6Node38Domains0Fast v from by decide) v
def root6Node38Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(0,0),(6,4)]
  | 4 => [(5,5)]
  | 5 => [(7,0)]
  | 6 => [(4,3)]
  | 7 => [(1,5),(3,5)]
  | 8 => [(0,3),(6,1)]
  | 9 => [(0,5)]
  | 10 => [(4,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(2,0),(2,4)]
  | 14 => [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 15 => [(6,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(3,1),(7,1)]
  | 20 => [(0,1),(1,5),(6,5),(7,5)]
  | 21 => [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 22 => [(4,0),(8,0)]
  | 23 => [(7,3)]
  | 24 => [(8,2)]
  | 25 => [(5,0),(8,0)]
  | 26 => [(4,5),(7,3)]
  | 27 => [(1,0),(4,2),(7,0),(8,2)]
  | 28 => [(0,1),(6,4)]
  | 29 => [(1,2),(6,2)]
  | 30 => [(8,4)]
  | 31 => [(0,0),(6,4)]
  | 32 => [(1,2),(7,2)]
  | 33 => [(0,3),(1,0)]
  | 34 => [(7,1),(8,1)]
  | 35 => [(1,5),(7,5)]
  | _ => [(0,3),(6,1)]
def root6Node38Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,0),(6,4)]
  | 4 => some [(5,5)]
  | 5 => some [(7,0)]
  | 6 => some [(4,3)]
  | 7 => some [(1,5),(3,5)]
  | 8 => some [(0,3),(6,1)]
  | 9 => some [(0,5)]
  | 10 => some [(4,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0),(2,4)]
  | 14 => some [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(3,1),(7,1)]
  | 20 => some [(0,1),(1,5),(6,5),(7,5)]
  | 21 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 22 => some [(4,0),(8,0)]
  | 23 => some [(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(5,0),(8,0)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(1,0),(4,2),(7,0),(8,2)]
  | 28 => some [(0,1),(6,4)]
  | 29 => some [(1,2),(6,2)]
  | 30 => some [(8,4)]
  | 31 => some [(0,0),(6,4)]
  | 32 => some [(1,2),(7,2)]
  | 33 => some [(0,3),(1,0)]
  | 34 => some [(7,1),(8,1)]
  | 35 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root6Node38Domains1_fast_eq : root6Node38Domains1 = expandDomains root6Node38Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node38Domains1 v = expandDomains root6Node38Domains1Fast v from by decide) v
theorem root6Node38Step1Chunk0_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_0⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk0_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_1⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk0_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_2⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk0_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_3⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk0_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_4⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk0_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_5⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk1_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_0⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk1_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_1⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk1_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_2⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk1_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_3⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk1_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_4⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk1_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_5⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk2_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_0⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk2_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_1⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk2_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_2⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk2_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_3⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk2_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_4⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk2_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_5⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk3_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_0⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk3_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_1⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk3_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_2⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk3_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_3⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk3_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_4⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk3_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_5⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk4_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_0⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk4_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_1⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk4_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_2⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk4_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_3⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk4_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_4⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk4_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_5⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk5_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_0⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk5_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_1⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk5_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_2⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk5_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_3⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk5_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_4⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk5_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_5⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk6_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_0⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk6_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_1⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk6_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_2⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk6_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_3⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk6_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_4⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk6_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_5⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk7_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_0⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk7_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_1⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk7_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_2⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk7_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_3⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk7_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_4⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk7_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_5⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk8_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_0⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk8_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_1⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk8_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_2⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk8_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_3⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk8_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_4⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk8_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_5⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1_checked :
    checkReplacement table2 root6Node38Domains0 root6Node38Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node38Step1Chunk0_0_checked, root6Node38Step1Chunk0_1_checked, root6Node38Step1Chunk0_2_checked, root6Node38Step1Chunk0_3_checked, root6Node38Step1Chunk0_4_checked, root6Node38Step1Chunk0_5_checked, root6Node38Step1Chunk1_0_checked, root6Node38Step1Chunk1_1_checked, root6Node38Step1Chunk1_2_checked, root6Node38Step1Chunk1_3_checked, root6Node38Step1Chunk1_4_checked, root6Node38Step1Chunk1_5_checked, root6Node38Step1Chunk2_0_checked, root6Node38Step1Chunk2_1_checked, root6Node38Step1Chunk2_2_checked, root6Node38Step1Chunk2_3_checked, root6Node38Step1Chunk2_4_checked, root6Node38Step1Chunk2_5_checked, root6Node38Step1Chunk3_0_checked, root6Node38Step1Chunk3_1_checked, root6Node38Step1Chunk3_2_checked, root6Node38Step1Chunk3_3_checked, root6Node38Step1Chunk3_4_checked, root6Node38Step1Chunk3_5_checked, root6Node38Step1Chunk4_0_checked, root6Node38Step1Chunk4_1_checked, root6Node38Step1Chunk4_2_checked, root6Node38Step1Chunk4_3_checked, root6Node38Step1Chunk4_4_checked, root6Node38Step1Chunk4_5_checked, root6Node38Step1Chunk5_0_checked, root6Node38Step1Chunk5_1_checked, root6Node38Step1Chunk5_2_checked, root6Node38Step1Chunk5_3_checked, root6Node38Step1Chunk5_4_checked, root6Node38Step1Chunk5_5_checked, root6Node38Step1Chunk6_0_checked, root6Node38Step1Chunk6_1_checked, root6Node38Step1Chunk6_2_checked, root6Node38Step1Chunk6_3_checked, root6Node38Step1Chunk6_4_checked, root6Node38Step1Chunk6_5_checked, root6Node38Step1Chunk7_0_checked, root6Node38Step1Chunk7_1_checked, root6Node38Step1Chunk7_2_checked, root6Node38Step1Chunk7_3_checked, root6Node38Step1Chunk7_4_checked, root6Node38Step1Chunk7_5_checked, root6Node38Step1Chunk8_0_checked, root6Node38Step1Chunk8_1_checked, root6Node38Step1Chunk8_2_checked, root6Node38Step1Chunk8_3_checked, root6Node38Step1Chunk8_4_checked, root6Node38Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
