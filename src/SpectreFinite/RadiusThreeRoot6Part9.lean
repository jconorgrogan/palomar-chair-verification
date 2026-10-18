module

public import SpectreFinite.RadiusThreeRoot6Part8
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable23

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node15Domains0 : Domains 37 State := restrict root6Node14Domains2 9 (0,4)
def root6Node15Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(5,2)]
  | 5 => some [(8,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(3,0)]
  | 9 => some [(0,4)]
  | 10 => some [(5,4),(8,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(0,0)]
  | 15 => some [(1,0),(7,0)]
  | 16 => some [(4,3),(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5)]
  | 21 => some [(6,1)]
  | 22 => some [(4,0),(7,4),(8,0)]
  | 23 => some [(1,3),(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(5,0)]
  | 26 => some [(4,5)]
  | 27 => some [(7,0)]
  | 28 => some [(0,1),(6,4),(6,5)]
  | 29 => some [(0,4),(1,2),(6,2)]
  | 30 => some [(5,4),(8,4)]
  | 31 => some [(0,0)]
  | 32 => some [(7,2)]
  | 33 => some [(0,3),(1,0),(7,0)]
  | 34 => some [(4,3),(7,1),(8,1)]
  | 35 => some [(1,5)]
  | _ => some [(6,1)]
theorem root6Node15Domains0_fast_eq : root6Node15Domains0 = expandDomains root6Node15Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node15Domains0 v = expandDomains root6Node15Domains0Fast v from by decide) v
def root6Node15Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(5,2)]
  | 5 => [(8,0)]
  | 6 => [(8,3)]
  | 7 => [(5,5)]
  | 8 => [(3,0)]
  | 9 => [(0,4)]
  | 10 => [(5,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5)]
  | 21 => [(6,1)]
  | 22 => [(7,4)]
  | 23 => [(1,3)]
  | 24 => [(8,2)]
  | 25 => [(5,0)]
  | 26 => [(4,5)]
  | 27 => [(7,0)]
  | 28 => [(6,5)]
  | 29 => [(0,4)]
  | 30 => [(5,4)]
  | 31 => [(0,0)]
  | 32 => [(7,2)]
  | 33 => [(7,0)]
  | 34 => [(4,3)]
  | 35 => [(1,5)]
  | _ => [(6,1)]
def root6Node15Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(5,2)]
  | 5 => some [(8,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(3,0)]
  | 9 => some [(0,4)]
  | 10 => some [(5,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5)]
  | 21 => some [(6,1)]
  | 22 => some [(7,4)]
  | 23 => some [(1,3)]
  | 24 => some [(8,2)]
  | 25 => some [(5,0)]
  | 26 => some [(4,5)]
  | 27 => some [(7,0)]
  | 28 => some [(6,5)]
  | 29 => some [(0,4)]
  | 30 => some [(5,4)]
  | 31 => some [(0,0)]
  | 32 => some [(7,2)]
  | 33 => some [(7,0)]
  | 34 => some [(4,3)]
  | 35 => some [(1,5)]
  | _ => some [(6,1)]
theorem root6Node15Domains1_fast_eq : root6Node15Domains1 = expandDomains root6Node15Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node15Domains1 v = expandDomains root6Node15Domains1Fast v from by decide) v
theorem root6Node15Step1Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1_checked :
    checkReplacement table23 root6Node15Domains0 root6Node15Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node15Step1Chunk0_0_checked, root6Node15Step1Chunk0_1_checked, root6Node15Step1Chunk0_2_checked, root6Node15Step1Chunk0_3_checked, root6Node15Step1Chunk0_4_checked, root6Node15Step1Chunk0_5_checked, root6Node15Step1Chunk1_0_checked, root6Node15Step1Chunk1_1_checked, root6Node15Step1Chunk1_2_checked, root6Node15Step1Chunk1_3_checked, root6Node15Step1Chunk1_4_checked, root6Node15Step1Chunk1_5_checked, root6Node15Step1Chunk2_0_checked, root6Node15Step1Chunk2_1_checked, root6Node15Step1Chunk2_2_checked, root6Node15Step1Chunk2_3_checked, root6Node15Step1Chunk2_4_checked, root6Node15Step1Chunk2_5_checked, root6Node15Step1Chunk3_0_checked, root6Node15Step1Chunk3_1_checked, root6Node15Step1Chunk3_2_checked, root6Node15Step1Chunk3_3_checked, root6Node15Step1Chunk3_4_checked, root6Node15Step1Chunk3_5_checked, root6Node15Step1Chunk4_0_checked, root6Node15Step1Chunk4_1_checked, root6Node15Step1Chunk4_2_checked, root6Node15Step1Chunk4_3_checked, root6Node15Step1Chunk4_4_checked, root6Node15Step1Chunk4_5_checked, root6Node15Step1Chunk5_0_checked, root6Node15Step1Chunk5_1_checked, root6Node15Step1Chunk5_2_checked, root6Node15Step1Chunk5_3_checked, root6Node15Step1Chunk5_4_checked, root6Node15Step1Chunk5_5_checked, root6Node15Step1Chunk6_0_checked, root6Node15Step1Chunk6_1_checked, root6Node15Step1Chunk6_2_checked, root6Node15Step1Chunk6_3_checked, root6Node15Step1Chunk6_4_checked, root6Node15Step1Chunk6_5_checked, root6Node15Step1Chunk7_0_checked, root6Node15Step1Chunk7_1_checked, root6Node15Step1Chunk7_2_checked, root6Node15Step1Chunk7_3_checked, root6Node15Step1Chunk7_4_checked, root6Node15Step1Chunk7_5_checked, root6Node15Step1Chunk8_0_checked, root6Node15Step1Chunk8_1_checked, root6Node15Step1Chunk8_2_checked, root6Node15Step1Chunk8_3_checked, root6Node15Step1Chunk8_4_checked, root6Node15Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root6Node15Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node15Domains1 (.output 6) = true := by decide
def root6Node16Domains0 : Domains 37 State := restrict root6Node14Domains2 9 (6,2)
def root6Node16Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(5,2)]
  | 5 => some [(8,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(3,0)]
  | 9 => some [(6,2)]
  | 10 => some [(5,4),(8,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(0,0)]
  | 15 => some [(1,0),(7,0)]
  | 16 => some [(4,3),(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5)]
  | 21 => some [(6,1)]
  | 22 => some [(4,0),(7,4),(8,0)]
  | 23 => some [(1,3),(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(5,0)]
  | 26 => some [(4,5)]
  | 27 => some [(7,0)]
  | 28 => some [(0,1),(6,4),(6,5)]
  | 29 => some [(0,4),(1,2),(6,2)]
  | 30 => some [(5,4),(8,4)]
  | 31 => some [(0,0)]
  | 32 => some [(7,2)]
  | 33 => some [(0,3),(1,0),(7,0)]
  | 34 => some [(4,3),(7,1),(8,1)]
  | 35 => some [(1,5)]
  | _ => some [(6,1)]
theorem root6Node16Domains0_fast_eq : root6Node16Domains0 = expandDomains root6Node16Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node16Domains0 v = expandDomains root6Node16Domains0Fast v from by decide) v
def root6Node16Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(5,2)]
  | 5 => [(8,0)]
  | 6 => [(8,3)]
  | 7 => [(5,5)]
  | 8 => [(3,0)]
  | 9 => [(6,2)]
  | 10 => [(8,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0)]
  | 15 => [(1,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5)]
  | 21 => [(6,1)]
  | 22 => [(4,0),(8,0)]
  | 23 => [(7,3)]
  | 24 => [(8,2)]
  | 25 => [(5,0)]
  | 26 => [(4,5)]
  | 27 => [(7,0)]
  | 28 => [(0,1),(6,4)]
  | 29 => [(1,2),(6,2)]
  | 30 => [(8,4)]
  | 31 => [(0,0)]
  | 32 => [(7,2)]
  | 33 => [(0,3),(1,0)]
  | 34 => [(7,1),(8,1)]
  | 35 => [(1,5)]
  | _ => [(6,1)]
def root6Node16Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(5,2)]
  | 5 => some [(8,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(3,0)]
  | 9 => some [(6,2)]
  | 10 => some [(8,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(0,0)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5)]
  | 21 => some [(6,1)]
  | 22 => some [(4,0),(8,0)]
  | 23 => some [(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(5,0)]
  | 26 => some [(4,5)]
  | 27 => some [(7,0)]
  | 28 => some [(0,1),(6,4)]
  | 29 => some [(1,2),(6,2)]
  | 30 => some [(8,4)]
  | 31 => some [(0,0)]
  | 32 => some [(7,2)]
  | 33 => some [(0,3),(1,0)]
  | 34 => some [(7,1),(8,1)]
  | 35 => some [(1,5)]
  | _ => some [(6,1)]
theorem root6Node16Domains1_fast_eq : root6Node16Domains1 = expandDomains root6Node16Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node16Domains1 v = expandDomains root6Node16Domains1Fast v from by decide) v
theorem root6Node16Step1Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root6Node16Domains0 root6Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node16Domains0 root6Node16Domains1
    root6Node16Domains0Fast root6Node16Domains1Fast
    root6Node16Domains0_fast_eq root6Node16Domains1_fast_eq (by decide)
theorem root6Node16Step1_checked :
    checkReplacement table23 root6Node16Domains0 root6Node16Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node16Step1Chunk0_0_checked, root6Node16Step1Chunk0_1_checked, root6Node16Step1Chunk0_2_checked, root6Node16Step1Chunk0_3_checked, root6Node16Step1Chunk0_4_checked, root6Node16Step1Chunk0_5_checked, root6Node16Step1Chunk1_0_checked, root6Node16Step1Chunk1_1_checked, root6Node16Step1Chunk1_2_checked, root6Node16Step1Chunk1_3_checked, root6Node16Step1Chunk1_4_checked, root6Node16Step1Chunk1_5_checked, root6Node16Step1Chunk2_0_checked, root6Node16Step1Chunk2_1_checked, root6Node16Step1Chunk2_2_checked, root6Node16Step1Chunk2_3_checked, root6Node16Step1Chunk2_4_checked, root6Node16Step1Chunk2_5_checked, root6Node16Step1Chunk3_0_checked, root6Node16Step1Chunk3_1_checked, root6Node16Step1Chunk3_2_checked, root6Node16Step1Chunk3_3_checked, root6Node16Step1Chunk3_4_checked, root6Node16Step1Chunk3_5_checked, root6Node16Step1Chunk4_0_checked, root6Node16Step1Chunk4_1_checked, root6Node16Step1Chunk4_2_checked, root6Node16Step1Chunk4_3_checked, root6Node16Step1Chunk4_4_checked, root6Node16Step1Chunk4_5_checked, root6Node16Step1Chunk5_0_checked, root6Node16Step1Chunk5_1_checked, root6Node16Step1Chunk5_2_checked, root6Node16Step1Chunk5_3_checked, root6Node16Step1Chunk5_4_checked, root6Node16Step1Chunk5_5_checked, root6Node16Step1Chunk6_0_checked, root6Node16Step1Chunk6_1_checked, root6Node16Step1Chunk6_2_checked, root6Node16Step1Chunk6_3_checked, root6Node16Step1Chunk6_4_checked, root6Node16Step1Chunk6_5_checked, root6Node16Step1Chunk7_0_checked, root6Node16Step1Chunk7_1_checked, root6Node16Step1Chunk7_2_checked, root6Node16Step1Chunk7_3_checked, root6Node16Step1Chunk7_4_checked, root6Node16Step1Chunk7_5_checked, root6Node16Step1Chunk8_0_checked, root6Node16Step1Chunk8_1_checked, root6Node16Step1Chunk8_2_checked, root6Node16Step1Chunk8_3_checked, root6Node16Step1Chunk8_4_checked, root6Node16Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node17Domains0 : Domains 37 State := restrict root6Node16Domains1 22 (4,0)
def root6Node17Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(5,2)]
  | 5 => some [(8,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(3,0)]
  | 9 => some [(6,2)]
  | 10 => some [(8,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(0,0)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5)]
  | 21 => some [(6,1)]
  | 22 => some [(4,0)]
  | 23 => some [(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(5,0)]
  | 26 => some [(4,5)]
  | 27 => some [(7,0)]
  | 28 => some [(0,1),(6,4)]
  | 29 => some [(1,2),(6,2)]
  | 30 => some [(8,4)]
  | 31 => some [(0,0)]
  | 32 => some [(7,2)]
  | 33 => some [(0,3),(1,0)]
  | 34 => some [(7,1),(8,1)]
  | 35 => some [(1,5)]
  | _ => some [(6,1)]
theorem root6Node17Domains0_fast_eq : root6Node17Domains0 = expandDomains root6Node17Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node17Domains0 v = expandDomains root6Node17Domains0Fast v from by decide) v
def root6Node17Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(5,2)]
  | 5 => [(8,0)]
  | 6 => [(8,3)]
  | 7 => [(5,5)]
  | 8 => [(3,0)]
  | 9 => [(6,2)]
  | 10 => [(8,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0)]
  | 15 => [(1,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5)]
  | 21 => [(6,1)]
  | 22 => [(4,0)]
  | 23 => [(7,3)]
  | 24 => [(8,2)]
  | 25 => [(5,0)]
  | 26 => [(4,5)]
  | 27 => [(7,0)]
  | 28 => [(0,1)]
  | 29 => [(6,2)]
  | 30 => [(8,4)]
  | 31 => [(0,0)]
  | 32 => [(7,2)]
  | 33 => [(1,0)]
  | 34 => [(7,1)]
  | 35 => [(1,5)]
  | _ => [(6,1)]
def root6Node17Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(5,2)]
  | 5 => some [(8,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(3,0)]
  | 9 => some [(6,2)]
  | 10 => some [(8,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(0,0)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5)]
  | 21 => some [(6,1)]
  | 22 => some [(4,0)]
  | 23 => some [(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(5,0)]
  | 26 => some [(4,5)]
  | 27 => some [(7,0)]
  | 28 => some [(0,1)]
  | 29 => some [(6,2)]
  | 30 => some [(8,4)]
  | 31 => some [(0,0)]
  | 32 => some [(7,2)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,5)]
  | _ => some [(6,1)]
theorem root6Node17Domains1_fast_eq : root6Node17Domains1 = expandDomains root6Node17Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node17Domains1 v = expandDomains root6Node17Domains1Fast v from by decide) v
theorem root6Node17Step1Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root6Node17Domains0 root6Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node17Domains0 root6Node17Domains1
    root6Node17Domains0Fast root6Node17Domains1Fast
    root6Node17Domains0_fast_eq root6Node17Domains1_fast_eq (by decide)
theorem root6Node17Step1_checked :
    checkReplacement table23 root6Node17Domains0 root6Node17Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node17Step1Chunk0_0_checked, root6Node17Step1Chunk0_1_checked, root6Node17Step1Chunk0_2_checked, root6Node17Step1Chunk0_3_checked, root6Node17Step1Chunk0_4_checked, root6Node17Step1Chunk0_5_checked, root6Node17Step1Chunk1_0_checked, root6Node17Step1Chunk1_1_checked, root6Node17Step1Chunk1_2_checked, root6Node17Step1Chunk1_3_checked, root6Node17Step1Chunk1_4_checked, root6Node17Step1Chunk1_5_checked, root6Node17Step1Chunk2_0_checked, root6Node17Step1Chunk2_1_checked, root6Node17Step1Chunk2_2_checked, root6Node17Step1Chunk2_3_checked, root6Node17Step1Chunk2_4_checked, root6Node17Step1Chunk2_5_checked, root6Node17Step1Chunk3_0_checked, root6Node17Step1Chunk3_1_checked, root6Node17Step1Chunk3_2_checked, root6Node17Step1Chunk3_3_checked, root6Node17Step1Chunk3_4_checked, root6Node17Step1Chunk3_5_checked, root6Node17Step1Chunk4_0_checked, root6Node17Step1Chunk4_1_checked, root6Node17Step1Chunk4_2_checked, root6Node17Step1Chunk4_3_checked, root6Node17Step1Chunk4_4_checked, root6Node17Step1Chunk4_5_checked, root6Node17Step1Chunk5_0_checked, root6Node17Step1Chunk5_1_checked, root6Node17Step1Chunk5_2_checked, root6Node17Step1Chunk5_3_checked, root6Node17Step1Chunk5_4_checked, root6Node17Step1Chunk5_5_checked, root6Node17Step1Chunk6_0_checked, root6Node17Step1Chunk6_1_checked, root6Node17Step1Chunk6_2_checked, root6Node17Step1Chunk6_3_checked, root6Node17Step1Chunk6_4_checked, root6Node17Step1Chunk6_5_checked, root6Node17Step1Chunk7_0_checked, root6Node17Step1Chunk7_1_checked, root6Node17Step1Chunk7_2_checked, root6Node17Step1Chunk7_3_checked, root6Node17Step1Chunk7_4_checked, root6Node17Step1Chunk7_5_checked, root6Node17Step1Chunk8_0_checked, root6Node17Step1Chunk8_1_checked, root6Node17Step1Chunk8_2_checked, root6Node17Step1Chunk8_3_checked, root6Node17Step1Chunk8_4_checked, root6Node17Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root6Node17Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node17Domains1 (.output 7) = true := by decide
end SpectreFinite.HexSearch.RadiusThree
