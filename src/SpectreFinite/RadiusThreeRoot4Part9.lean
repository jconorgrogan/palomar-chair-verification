module

public import SpectreFinite.RadiusThreeRoot4Part8
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable16
public import SpectreFinite.RadiusThreeTable25

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node14Domains0 : Domains 37 State := restrict root4Node13Domains1 34 (1,3)
def root4Node14Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(0,4)]
  | 5 => some [(3,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(7,0)]
  | 10 => some [(2,3)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(4,1)]
  | 14 => some [(0,2)]
  | 15 => some [(4,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(8,0)]
  | 22 => some [(7,5)]
  | 23 => some [(0,3)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(8,4)]
  | 28 => some [(4,2)]
  | 29 => some [(5,3)]
  | 30 => some [(8,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,4)]
  | 34 => some [(1,3)]
  | 35 => some [(7,2),(8,2)]
  | _ => some [(4,0),(8,0)]
theorem root4Node14Domains0_fast_eq : root4Node14Domains0 = expandDomains root4Node14Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node14Domains0 v = expandDomains root4Node14Domains0Fast v from by decide) v
def root4Node14Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(0,4)]
  | 5 => [(3,4)]
  | 6 => [(6,3)]
  | 7 => [(7,2)]
  | 8 => [(7,4)]
  | 9 => [(7,0)]
  | 10 => [(2,3)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(4,1)]
  | 14 => [(0,2)]
  | 15 => [(4,4)]
  | 16 => [(6,4)]
  | 17 => [(1,2)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(5,2)]
  | 21 => [(8,0)]
  | 22 => [(7,5)]
  | 23 => [(0,3)]
  | 24 => [(5,1)]
  | 25 => [(0,1)]
  | 26 => [(6,2)]
  | 27 => [(8,4)]
  | 28 => [(4,2)]
  | 29 => [(5,3)]
  | 30 => [(8,5)]
  | 31 => [(1,0)]
  | 32 => [(7,1)]
  | 33 => [(7,4)]
  | 34 => [(1,3)]
  | 35 => [(8,2)]
  | _ => [(8,0)]
def root4Node14Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(0,4)]
  | 5 => some [(3,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(7,0)]
  | 10 => some [(2,3)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(4,1)]
  | 14 => some [(0,2)]
  | 15 => some [(4,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(8,0)]
  | 22 => some [(7,5)]
  | 23 => some [(0,3)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(8,4)]
  | 28 => some [(4,2)]
  | 29 => some [(5,3)]
  | 30 => some [(8,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,4)]
  | 34 => some [(1,3)]
  | 35 => some [(8,2)]
  | _ => some [(8,0)]
theorem root4Node14Domains1_fast_eq : root4Node14Domains1 = expandDomains root4Node14Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node14Domains1 v = expandDomains root4Node14Domains1Fast v from by decide) v
theorem root4Node14Step1Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root4Node14Domains0 root4Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node14Domains0 root4Node14Domains1
    root4Node14Domains0Fast root4Node14Domains1Fast
    root4Node14Domains0_fast_eq root4Node14Domains1_fast_eq (by decide)
theorem root4Node14Step1_checked :
    checkReplacement table25 root4Node14Domains0 root4Node14Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node14Step1Chunk0_0_checked, root4Node14Step1Chunk0_1_checked, root4Node14Step1Chunk0_2_checked, root4Node14Step1Chunk0_3_checked, root4Node14Step1Chunk0_4_checked, root4Node14Step1Chunk0_5_checked, root4Node14Step1Chunk1_0_checked, root4Node14Step1Chunk1_1_checked, root4Node14Step1Chunk1_2_checked, root4Node14Step1Chunk1_3_checked, root4Node14Step1Chunk1_4_checked, root4Node14Step1Chunk1_5_checked, root4Node14Step1Chunk2_0_checked, root4Node14Step1Chunk2_1_checked, root4Node14Step1Chunk2_2_checked, root4Node14Step1Chunk2_3_checked, root4Node14Step1Chunk2_4_checked, root4Node14Step1Chunk2_5_checked, root4Node14Step1Chunk3_0_checked, root4Node14Step1Chunk3_1_checked, root4Node14Step1Chunk3_2_checked, root4Node14Step1Chunk3_3_checked, root4Node14Step1Chunk3_4_checked, root4Node14Step1Chunk3_5_checked, root4Node14Step1Chunk4_0_checked, root4Node14Step1Chunk4_1_checked, root4Node14Step1Chunk4_2_checked, root4Node14Step1Chunk4_3_checked, root4Node14Step1Chunk4_4_checked, root4Node14Step1Chunk4_5_checked, root4Node14Step1Chunk5_0_checked, root4Node14Step1Chunk5_1_checked, root4Node14Step1Chunk5_2_checked, root4Node14Step1Chunk5_3_checked, root4Node14Step1Chunk5_4_checked, root4Node14Step1Chunk5_5_checked, root4Node14Step1Chunk6_0_checked, root4Node14Step1Chunk6_1_checked, root4Node14Step1Chunk6_2_checked, root4Node14Step1Chunk6_3_checked, root4Node14Step1Chunk6_4_checked, root4Node14Step1Chunk6_5_checked, root4Node14Step1Chunk7_0_checked, root4Node14Step1Chunk7_1_checked, root4Node14Step1Chunk7_2_checked, root4Node14Step1Chunk7_3_checked, root4Node14Step1Chunk7_4_checked, root4Node14Step1Chunk7_5_checked, root4Node14Step1Chunk8_0_checked, root4Node14Step1Chunk8_1_checked, root4Node14Step1Chunk8_2_checked, root4Node14Step1Chunk8_3_checked, root4Node14Step1Chunk8_4_checked, root4Node14Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root4Node14Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node14Domains1 (.output 5) = true := by decide
def root4Node15Domains0 : Domains 37 State := restrict root4Node13Domains1 34 (6,3)
def root4Node15Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(0,4)]
  | 5 => some [(3,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(7,0)]
  | 10 => some [(2,3)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(4,1)]
  | 14 => some [(0,2)]
  | 15 => some [(4,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(8,0)]
  | 22 => some [(7,5)]
  | 23 => some [(0,3)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(8,4)]
  | 28 => some [(4,2)]
  | 29 => some [(5,3)]
  | 30 => some [(8,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,4)]
  | 34 => some [(6,3)]
  | 35 => some [(7,2),(8,2)]
  | _ => some [(4,0),(8,0)]
theorem root4Node15Domains0_fast_eq : root4Node15Domains0 = expandDomains root4Node15Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node15Domains0 v = expandDomains root4Node15Domains0Fast v from by decide) v
def root4Node15Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(0,4)]
  | 5 => [(3,4)]
  | 6 => [(6,3)]
  | 7 => [(7,2)]
  | 8 => [(7,4)]
  | 9 => [(7,0)]
  | 10 => [(2,3)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(4,1)]
  | 14 => [(0,2)]
  | 15 => [(4,4)]
  | 16 => [(6,4)]
  | 17 => [(1,2)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(5,2)]
  | 21 => [(8,0)]
  | 22 => [(7,5)]
  | 23 => [(0,3)]
  | 24 => [(5,1)]
  | 25 => [(0,1)]
  | 26 => [(6,2)]
  | 27 => [(8,4)]
  | 28 => [(4,2)]
  | 29 => [(5,3)]
  | 30 => [(8,5)]
  | 31 => [(1,0)]
  | 32 => [(7,1)]
  | 33 => [(7,4)]
  | 34 => [(6,3)]
  | 35 => [(7,2)]
  | _ => [(4,0)]
def root4Node15Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(0,4)]
  | 5 => some [(3,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(7,0)]
  | 10 => some [(2,3)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(4,1)]
  | 14 => some [(0,2)]
  | 15 => some [(4,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(8,0)]
  | 22 => some [(7,5)]
  | 23 => some [(0,3)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(8,4)]
  | 28 => some [(4,2)]
  | 29 => some [(5,3)]
  | 30 => some [(8,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,4)]
  | 34 => some [(6,3)]
  | 35 => some [(7,2)]
  | _ => some [(4,0)]
theorem root4Node15Domains1_fast_eq : root4Node15Domains1 = expandDomains root4Node15Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node15Domains1 v = expandDomains root4Node15Domains1Fast v from by decide) v
theorem root4Node15Step1Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root4Node15Domains0 root4Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node15Domains0 root4Node15Domains1
    root4Node15Domains0Fast root4Node15Domains1Fast
    root4Node15Domains0_fast_eq root4Node15Domains1_fast_eq (by decide)
theorem root4Node15Step1_checked :
    checkReplacement table25 root4Node15Domains0 root4Node15Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node15Step1Chunk0_0_checked, root4Node15Step1Chunk0_1_checked, root4Node15Step1Chunk0_2_checked, root4Node15Step1Chunk0_3_checked, root4Node15Step1Chunk0_4_checked, root4Node15Step1Chunk0_5_checked, root4Node15Step1Chunk1_0_checked, root4Node15Step1Chunk1_1_checked, root4Node15Step1Chunk1_2_checked, root4Node15Step1Chunk1_3_checked, root4Node15Step1Chunk1_4_checked, root4Node15Step1Chunk1_5_checked, root4Node15Step1Chunk2_0_checked, root4Node15Step1Chunk2_1_checked, root4Node15Step1Chunk2_2_checked, root4Node15Step1Chunk2_3_checked, root4Node15Step1Chunk2_4_checked, root4Node15Step1Chunk2_5_checked, root4Node15Step1Chunk3_0_checked, root4Node15Step1Chunk3_1_checked, root4Node15Step1Chunk3_2_checked, root4Node15Step1Chunk3_3_checked, root4Node15Step1Chunk3_4_checked, root4Node15Step1Chunk3_5_checked, root4Node15Step1Chunk4_0_checked, root4Node15Step1Chunk4_1_checked, root4Node15Step1Chunk4_2_checked, root4Node15Step1Chunk4_3_checked, root4Node15Step1Chunk4_4_checked, root4Node15Step1Chunk4_5_checked, root4Node15Step1Chunk5_0_checked, root4Node15Step1Chunk5_1_checked, root4Node15Step1Chunk5_2_checked, root4Node15Step1Chunk5_3_checked, root4Node15Step1Chunk5_4_checked, root4Node15Step1Chunk5_5_checked, root4Node15Step1Chunk6_0_checked, root4Node15Step1Chunk6_1_checked, root4Node15Step1Chunk6_2_checked, root4Node15Step1Chunk6_3_checked, root4Node15Step1Chunk6_4_checked, root4Node15Step1Chunk6_5_checked, root4Node15Step1Chunk7_0_checked, root4Node15Step1Chunk7_1_checked, root4Node15Step1Chunk7_2_checked, root4Node15Step1Chunk7_3_checked, root4Node15Step1Chunk7_4_checked, root4Node15Step1Chunk7_5_checked, root4Node15Step1Chunk8_0_checked, root4Node15Step1Chunk8_1_checked, root4Node15Step1Chunk8_2_checked, root4Node15Step1Chunk8_3_checked, root4Node15Step1Chunk8_4_checked, root4Node15Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root4Node15Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node15Domains1 (.output 6) = true := by decide
def root4Node16Domains0 : Domains 37 State := restrict root4Node10Domains3 4 (6,2)
def root4Node16Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(6,2)]
  | 5 => some [(3,4),(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(1,0),(7,0)]
  | 10 => some [(2,1),(2,3)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(4,1)]
  | 14 => some [(0,2)]
  | 15 => some [(4,4)]
  | 16 => some [(0,0),(6,4)]
  | 17 => some [(1,2),(3,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(5,0),(8,0)]
  | 22 => some [(1,5),(7,5)]
  | 23 => some [(0,3),(6,1)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(8,4)]
  | 28 => some [(4,2),(7,0)]
  | 29 => some [(5,3),(8,3)]
  | 30 => some [(8,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,4)]
  | 34 => some [(1,3),(6,3)]
  | 35 => some [(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(8,0)]
theorem root4Node16Domains0_fast_eq : root4Node16Domains0 = expandDomains root4Node16Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node16Domains0 v = expandDomains root4Node16Domains0Fast v from by decide) v
def root4Node16Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(6,2)]
  | 5 => [(7,4)]
  | 6 => [(6,3)]
  | 7 => [(7,2)]
  | 8 => [(7,4)]
  | 9 => [(1,0)]
  | 10 => [(2,1)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(4,1)]
  | 14 => [(0,2)]
  | 15 => [(4,4)]
  | 16 => [(0,0)]
  | 17 => [(3,2)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(5,2)]
  | 21 => [(5,0),(8,0)]
  | 22 => [(1,5)]
  | 23 => [(6,1)]
  | 24 => [(5,1)]
  | 25 => [(0,1)]
  | 26 => [(6,2)]
  | 27 => [(8,4)]
  | 28 => [(7,0)]
  | 29 => [(8,3)]
  | 30 => [(8,5)]
  | 31 => [(1,0)]
  | 32 => [(7,1)]
  | 33 => [(7,4)]
  | 34 => [(1,3),(6,3)]
  | 35 => [(7,2),(8,2)]
  | _ => [(4,0),(5,0),(8,0)]
def root4Node16Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(6,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(1,0)]
  | 10 => some [(2,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(4,1)]
  | 14 => some [(0,2)]
  | 15 => some [(4,4)]
  | 16 => some [(0,0)]
  | 17 => some [(3,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(5,0),(8,0)]
  | 22 => some [(1,5)]
  | 23 => some [(6,1)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(8,4)]
  | 28 => some [(7,0)]
  | 29 => some [(8,3)]
  | 30 => some [(8,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,4)]
  | 34 => some [(1,3),(6,3)]
  | 35 => some [(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(8,0)]
theorem root4Node16Domains1_fast_eq : root4Node16Domains1 = expandDomains root4Node16Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node16Domains1 v = expandDomains root4Node16Domains1Fast v from by decide) v
theorem root4Node16Step1Chunk0_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_0⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk0_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_1⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk0_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_2⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk0_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_3⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk0_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_4⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk0_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_5⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk1_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_0⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk1_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_1⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk1_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_2⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk1_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_3⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk1_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_4⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk1_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_5⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk2_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_0⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk2_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_1⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk2_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_2⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk2_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_3⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk2_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_4⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk2_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_5⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk3_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_0⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk3_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_1⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk3_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_2⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk3_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_3⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk3_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_4⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk3_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_5⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk4_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_0⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk4_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_1⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk4_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_2⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk4_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_3⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk4_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_4⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk4_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_5⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk5_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_0⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk5_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_1⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk5_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_2⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk5_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_3⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk5_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_4⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk5_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_5⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk6_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_0⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk6_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_1⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk6_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_2⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk6_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_3⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk6_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_4⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk6_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_5⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk7_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_0⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk7_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_1⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk7_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_2⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk7_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_3⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk7_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_4⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk7_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_5⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk8_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_0⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk8_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_1⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk8_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_2⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk8_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_3⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk8_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_4⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk8_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_5⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1_checked :
    checkReplacement table16 root4Node16Domains0 root4Node16Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node16Step1Chunk0_0_checked, root4Node16Step1Chunk0_1_checked, root4Node16Step1Chunk0_2_checked, root4Node16Step1Chunk0_3_checked, root4Node16Step1Chunk0_4_checked, root4Node16Step1Chunk0_5_checked, root4Node16Step1Chunk1_0_checked, root4Node16Step1Chunk1_1_checked, root4Node16Step1Chunk1_2_checked, root4Node16Step1Chunk1_3_checked, root4Node16Step1Chunk1_4_checked, root4Node16Step1Chunk1_5_checked, root4Node16Step1Chunk2_0_checked, root4Node16Step1Chunk2_1_checked, root4Node16Step1Chunk2_2_checked, root4Node16Step1Chunk2_3_checked, root4Node16Step1Chunk2_4_checked, root4Node16Step1Chunk2_5_checked, root4Node16Step1Chunk3_0_checked, root4Node16Step1Chunk3_1_checked, root4Node16Step1Chunk3_2_checked, root4Node16Step1Chunk3_3_checked, root4Node16Step1Chunk3_4_checked, root4Node16Step1Chunk3_5_checked, root4Node16Step1Chunk4_0_checked, root4Node16Step1Chunk4_1_checked, root4Node16Step1Chunk4_2_checked, root4Node16Step1Chunk4_3_checked, root4Node16Step1Chunk4_4_checked, root4Node16Step1Chunk4_5_checked, root4Node16Step1Chunk5_0_checked, root4Node16Step1Chunk5_1_checked, root4Node16Step1Chunk5_2_checked, root4Node16Step1Chunk5_3_checked, root4Node16Step1Chunk5_4_checked, root4Node16Step1Chunk5_5_checked, root4Node16Step1Chunk6_0_checked, root4Node16Step1Chunk6_1_checked, root4Node16Step1Chunk6_2_checked, root4Node16Step1Chunk6_3_checked, root4Node16Step1Chunk6_4_checked, root4Node16Step1Chunk6_5_checked, root4Node16Step1Chunk7_0_checked, root4Node16Step1Chunk7_1_checked, root4Node16Step1Chunk7_2_checked, root4Node16Step1Chunk7_3_checked, root4Node16Step1Chunk7_4_checked, root4Node16Step1Chunk7_5_checked, root4Node16Step1Chunk8_0_checked, root4Node16Step1Chunk8_1_checked, root4Node16Step1Chunk8_2_checked, root4Node16Step1Chunk8_3_checked, root4Node16Step1Chunk8_4_checked, root4Node16Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
