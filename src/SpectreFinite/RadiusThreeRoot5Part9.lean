module

public import SpectreFinite.RadiusThreeRoot5Part8
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable2
public import SpectreFinite.RadiusThreeTable3
public import SpectreFinite.RadiusThreeTable8

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node14Domains0 : Domains 37 State := restrict root5Node13Domains1 1 (4,3)
def root5Node14Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(1,5),(3,5),(5,5),(7,5)]
  | 3 => some [(0,3),(1,0),(3,0),(6,1)]
  | 4 => some [(4,4),(7,2)]
  | 5 => some [(1,4),(7,4)]
  | 6 => some [(0,5),(6,3)]
  | 7 => some [(2,0),(2,2),(2,4),(4,4)]
  | 8 => some [(0,0),(1,3),(3,3),(7,3)]
  | 9 => some [(1,1),(6,1),(7,1)]
  | 10 => some [(4,1),(7,5)]
  | 11 => some [(0,2),(6,0)]
  | 12 => some [(1,1),(3,1),(7,1)]
  | 13 => some [(0,1),(1,5),(6,5)]
  | 14 => some [(0,4),(6,1),(6,2)]
  | 15 => some [(4,0),(7,0),(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2),(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0),(7,0)]
  | 21 => some [(4,3),(7,1),(8,3)]
  | 22 => some [(0,1),(6,4)]
  | 23 => some [(1,2),(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(0,3),(1,0)]
  | 29 => some [(7,1),(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(4,1),(5,1),(8,1)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(5,5),(8,5)]
  | 35 => some [(7,0)]
  | _ => some [(7,3),(8,3)]
theorem root5Node14Domains0_fast_eq : root5Node14Domains0 = expandDomains root5Node14Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node14Domains0 v = expandDomains root5Node14Domains0Fast v from by decide) v
def root5Node14Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(1,5),(3,5),(7,5)]
  | 3 => [(0,3),(6,1)]
  | 4 => [(4,4),(7,2)]
  | 5 => [(1,4),(7,4)]
  | 6 => [(0,5),(6,3)]
  | 7 => [(2,0),(2,2),(2,4)]
  | 8 => [(1,3),(3,3),(7,3)]
  | 9 => [(1,1),(6,1),(7,1)]
  | 10 => [(4,1),(7,5)]
  | 11 => [(0,2),(6,0)]
  | 12 => [(1,1),(3,1),(7,1)]
  | 13 => [(0,1),(6,5)]
  | 14 => [(0,4),(6,2)]
  | 15 => [(4,0),(7,0),(8,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2),(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(1,0),(7,0)]
  | 21 => [(4,3),(7,1),(8,3)]
  | 22 => [(0,1),(6,4)]
  | 23 => [(1,2),(6,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(0,3),(1,0)]
  | 29 => [(7,1),(8,1)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(4,1),(5,1),(8,1)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5),(5,5),(8,5)]
  | 35 => [(7,0)]
  | _ => [(7,3),(8,3)]
def root5Node14Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(1,5),(3,5),(7,5)]
  | 3 => some [(0,3),(6,1)]
  | 4 => some [(4,4),(7,2)]
  | 5 => some [(1,4),(7,4)]
  | 6 => some [(0,5),(6,3)]
  | 7 => some [(2,0),(2,2),(2,4)]
  | 8 => some [(1,3),(3,3),(7,3)]
  | 9 => some [(1,1),(6,1),(7,1)]
  | 10 => some [(4,1),(7,5)]
  | 11 => some [(0,2),(6,0)]
  | 12 => some [(1,1),(3,1),(7,1)]
  | 13 => some [(0,1),(6,5)]
  | 14 => some [(0,4),(6,2)]
  | 15 => some [(4,0),(7,0),(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2),(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0),(7,0)]
  | 21 => some [(4,3),(7,1),(8,3)]
  | 22 => some [(0,1),(6,4)]
  | 23 => some [(1,2),(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(0,3),(1,0)]
  | 29 => some [(7,1),(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(4,1),(5,1),(8,1)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(5,5),(8,5)]
  | 35 => some [(7,0)]
  | _ => some [(7,3),(8,3)]
theorem root5Node14Domains1_fast_eq : root5Node14Domains1 = expandDomains root5Node14Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node14Domains1 v = expandDomains root5Node14Domains1Fast v from by decide) v
theorem root5Node14Step1Chunk0_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk0_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk0_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk0_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk0_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk0_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk1_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk1_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk1_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk1_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk1_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk1_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk2_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk2_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk2_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk2_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk2_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk2_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk3_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk3_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk3_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk3_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk3_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk3_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk4_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk4_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk4_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk4_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk4_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk4_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk5_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk5_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk5_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk5_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk5_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk5_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk6_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk6_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk6_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk6_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk6_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk6_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk7_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk7_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk7_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk7_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk7_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk7_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk8_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk8_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk8_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk8_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk8_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk8_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1_checked :
    checkReplacement table3 root5Node14Domains0 root5Node14Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node14Step1Chunk0_0_checked, root5Node14Step1Chunk0_1_checked, root5Node14Step1Chunk0_2_checked, root5Node14Step1Chunk0_3_checked, root5Node14Step1Chunk0_4_checked, root5Node14Step1Chunk0_5_checked, root5Node14Step1Chunk1_0_checked, root5Node14Step1Chunk1_1_checked, root5Node14Step1Chunk1_2_checked, root5Node14Step1Chunk1_3_checked, root5Node14Step1Chunk1_4_checked, root5Node14Step1Chunk1_5_checked, root5Node14Step1Chunk2_0_checked, root5Node14Step1Chunk2_1_checked, root5Node14Step1Chunk2_2_checked, root5Node14Step1Chunk2_3_checked, root5Node14Step1Chunk2_4_checked, root5Node14Step1Chunk2_5_checked, root5Node14Step1Chunk3_0_checked, root5Node14Step1Chunk3_1_checked, root5Node14Step1Chunk3_2_checked, root5Node14Step1Chunk3_3_checked, root5Node14Step1Chunk3_4_checked, root5Node14Step1Chunk3_5_checked, root5Node14Step1Chunk4_0_checked, root5Node14Step1Chunk4_1_checked, root5Node14Step1Chunk4_2_checked, root5Node14Step1Chunk4_3_checked, root5Node14Step1Chunk4_4_checked, root5Node14Step1Chunk4_5_checked, root5Node14Step1Chunk5_0_checked, root5Node14Step1Chunk5_1_checked, root5Node14Step1Chunk5_2_checked, root5Node14Step1Chunk5_3_checked, root5Node14Step1Chunk5_4_checked, root5Node14Step1Chunk5_5_checked, root5Node14Step1Chunk6_0_checked, root5Node14Step1Chunk6_1_checked, root5Node14Step1Chunk6_2_checked, root5Node14Step1Chunk6_3_checked, root5Node14Step1Chunk6_4_checked, root5Node14Step1Chunk6_5_checked, root5Node14Step1Chunk7_0_checked, root5Node14Step1Chunk7_1_checked, root5Node14Step1Chunk7_2_checked, root5Node14Step1Chunk7_3_checked, root5Node14Step1Chunk7_4_checked, root5Node14Step1Chunk7_5_checked, root5Node14Step1Chunk8_0_checked, root5Node14Step1Chunk8_1_checked, root5Node14Step1Chunk8_2_checked, root5Node14Step1Chunk8_3_checked, root5Node14Step1Chunk8_4_checked, root5Node14Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node14Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(1,5),(3,5),(7,5)]
  | 3 => [(0,3),(6,1)]
  | 4 => [(4,4),(7,2)]
  | 5 => [(1,4),(7,4)]
  | 6 => [(0,5),(6,3)]
  | 7 => [(2,0),(2,2),(2,4)]
  | 8 => [(1,3),(3,3),(7,3)]
  | 9 => [(1,1),(6,1),(7,1)]
  | 10 => [(4,1),(7,5)]
  | 11 => [(0,2),(6,0)]
  | 12 => [(1,1),(3,1),(7,1)]
  | 13 => [(0,1),(6,5)]
  | 14 => [(0,4),(6,2)]
  | 15 => [(4,0),(7,0),(8,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2),(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(1,0),(7,0)]
  | 21 => [(4,3),(7,1)]
  | 22 => [(0,1),(6,4)]
  | 23 => [(1,2),(6,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(0,3),(1,0)]
  | 29 => [(7,1),(8,1)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(4,1),(5,1),(8,1)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5),(5,5),(8,5)]
  | 35 => [(7,0)]
  | _ => [(7,3),(8,3)]
def root5Node14Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(1,5),(3,5),(7,5)]
  | 3 => some [(0,3),(6,1)]
  | 4 => some [(4,4),(7,2)]
  | 5 => some [(1,4),(7,4)]
  | 6 => some [(0,5),(6,3)]
  | 7 => some [(2,0),(2,2),(2,4)]
  | 8 => some [(1,3),(3,3),(7,3)]
  | 9 => some [(1,1),(6,1),(7,1)]
  | 10 => some [(4,1),(7,5)]
  | 11 => some [(0,2),(6,0)]
  | 12 => some [(1,1),(3,1),(7,1)]
  | 13 => some [(0,1),(6,5)]
  | 14 => some [(0,4),(6,2)]
  | 15 => some [(4,0),(7,0),(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2),(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0),(7,0)]
  | 21 => some [(4,3),(7,1)]
  | 22 => some [(0,1),(6,4)]
  | 23 => some [(1,2),(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(0,3),(1,0)]
  | 29 => some [(7,1),(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(4,1),(5,1),(8,1)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(5,5),(8,5)]
  | 35 => some [(7,0)]
  | _ => some [(7,3),(8,3)]
theorem root5Node14Domains2_fast_eq : root5Node14Domains2 = expandDomains root5Node14Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node14Domains2 v = expandDomains root5Node14Domains2Fast v from by decide) v
theorem root5Node14Step2Chunk0_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_0⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk0_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_1⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk0_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_2⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk0_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_3⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk0_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_4⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk0_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_5⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk1_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_0⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk1_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_1⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk1_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_2⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk1_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_3⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk1_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_4⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk1_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_5⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk2_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_0⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk2_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_1⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk2_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_2⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk2_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_3⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk2_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_4⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk2_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_5⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk3_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_0⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk3_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_1⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk3_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_2⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk3_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_3⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk3_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_4⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk3_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_5⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk4_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_0⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk4_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_1⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk4_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_2⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk4_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_3⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk4_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_4⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk4_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_5⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk5_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_0⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk5_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_1⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk5_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_2⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk5_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_3⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk5_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_4⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk5_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_5⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk6_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_0⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk6_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_1⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk6_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_2⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk6_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_3⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk6_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_4⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk6_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_5⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk7_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_0⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk7_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_1⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk7_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_2⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk7_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_3⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk7_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_4⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk7_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_5⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk8_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_0⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk8_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_1⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk8_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_2⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk8_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_3⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk8_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_4⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk8_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_5⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2_checked :
    checkReplacement table8 root5Node14Domains1 root5Node14Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node14Step2Chunk0_0_checked, root5Node14Step2Chunk0_1_checked, root5Node14Step2Chunk0_2_checked, root5Node14Step2Chunk0_3_checked, root5Node14Step2Chunk0_4_checked, root5Node14Step2Chunk0_5_checked, root5Node14Step2Chunk1_0_checked, root5Node14Step2Chunk1_1_checked, root5Node14Step2Chunk1_2_checked, root5Node14Step2Chunk1_3_checked, root5Node14Step2Chunk1_4_checked, root5Node14Step2Chunk1_5_checked, root5Node14Step2Chunk2_0_checked, root5Node14Step2Chunk2_1_checked, root5Node14Step2Chunk2_2_checked, root5Node14Step2Chunk2_3_checked, root5Node14Step2Chunk2_4_checked, root5Node14Step2Chunk2_5_checked, root5Node14Step2Chunk3_0_checked, root5Node14Step2Chunk3_1_checked, root5Node14Step2Chunk3_2_checked, root5Node14Step2Chunk3_3_checked, root5Node14Step2Chunk3_4_checked, root5Node14Step2Chunk3_5_checked, root5Node14Step2Chunk4_0_checked, root5Node14Step2Chunk4_1_checked, root5Node14Step2Chunk4_2_checked, root5Node14Step2Chunk4_3_checked, root5Node14Step2Chunk4_4_checked, root5Node14Step2Chunk4_5_checked, root5Node14Step2Chunk5_0_checked, root5Node14Step2Chunk5_1_checked, root5Node14Step2Chunk5_2_checked, root5Node14Step2Chunk5_3_checked, root5Node14Step2Chunk5_4_checked, root5Node14Step2Chunk5_5_checked, root5Node14Step2Chunk6_0_checked, root5Node14Step2Chunk6_1_checked, root5Node14Step2Chunk6_2_checked, root5Node14Step2Chunk6_3_checked, root5Node14Step2Chunk6_4_checked, root5Node14Step2Chunk6_5_checked, root5Node14Step2Chunk7_0_checked, root5Node14Step2Chunk7_1_checked, root5Node14Step2Chunk7_2_checked, root5Node14Step2Chunk7_3_checked, root5Node14Step2Chunk7_4_checked, root5Node14Step2Chunk7_5_checked, root5Node14Step2Chunk8_0_checked, root5Node14Step2Chunk8_1_checked, root5Node14Step2Chunk8_2_checked, root5Node14Step2Chunk8_3_checked, root5Node14Step2Chunk8_4_checked, root5Node14Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node15Domains0 : Domains 37 State := restrict root5Node14Domains2 3 (0,3)
def root5Node15Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(1,5),(3,5),(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(4,4),(7,2)]
  | 5 => some [(1,4),(7,4)]
  | 6 => some [(0,5),(6,3)]
  | 7 => some [(2,0),(2,2),(2,4)]
  | 8 => some [(1,3),(3,3),(7,3)]
  | 9 => some [(1,1),(6,1),(7,1)]
  | 10 => some [(4,1),(7,5)]
  | 11 => some [(0,2),(6,0)]
  | 12 => some [(1,1),(3,1),(7,1)]
  | 13 => some [(0,1),(6,5)]
  | 14 => some [(0,4),(6,2)]
  | 15 => some [(4,0),(7,0),(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2),(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0),(7,0)]
  | 21 => some [(4,3),(7,1)]
  | 22 => some [(0,1),(6,4)]
  | 23 => some [(1,2),(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(0,3),(1,0)]
  | 29 => some [(7,1),(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(4,1),(5,1),(8,1)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(5,5),(8,5)]
  | 35 => some [(7,0)]
  | _ => some [(7,3),(8,3)]
theorem root5Node15Domains0_fast_eq : root5Node15Domains0 = expandDomains root5Node15Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node15Domains0 v = expandDomains root5Node15Domains0Fast v from by decide) v
def root5Node15Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(3,5),(7,5)]
  | 3 => [(0,3)]
  | 4 => [(4,4),(7,2)]
  | 5 => [(1,4),(7,4)]
  | 6 => [(0,5),(6,3)]
  | 7 => [(2,2),(2,4)]
  | 8 => [(1,3),(3,3)]
  | 9 => [(1,1),(6,1),(7,1)]
  | 10 => [(4,1),(7,5)]
  | 11 => [(0,2),(6,0)]
  | 12 => [(1,1),(7,1)]
  | 13 => [(0,1),(6,5)]
  | 14 => [(0,4),(6,2)]
  | 15 => [(4,0),(7,0),(8,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2),(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(1,0),(7,0)]
  | 21 => [(4,3),(7,1)]
  | 22 => [(0,1),(6,4)]
  | 23 => [(1,2),(6,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(0,3),(1,0)]
  | 29 => [(7,1),(8,1)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(4,1),(5,1),(8,1)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5),(5,5),(8,5)]
  | 35 => [(7,0)]
  | _ => [(7,3),(8,3)]
def root5Node15Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(3,5),(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(4,4),(7,2)]
  | 5 => some [(1,4),(7,4)]
  | 6 => some [(0,5),(6,3)]
  | 7 => some [(2,2),(2,4)]
  | 8 => some [(1,3),(3,3)]
  | 9 => some [(1,1),(6,1),(7,1)]
  | 10 => some [(4,1),(7,5)]
  | 11 => some [(0,2),(6,0)]
  | 12 => some [(1,1),(7,1)]
  | 13 => some [(0,1),(6,5)]
  | 14 => some [(0,4),(6,2)]
  | 15 => some [(4,0),(7,0),(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2),(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0),(7,0)]
  | 21 => some [(4,3),(7,1)]
  | 22 => some [(0,1),(6,4)]
  | 23 => some [(1,2),(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(0,3),(1,0)]
  | 29 => some [(7,1),(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(4,1),(5,1),(8,1)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(5,5),(8,5)]
  | 35 => some [(7,0)]
  | _ => some [(7,3),(8,3)]
theorem root5Node15Domains1_fast_eq : root5Node15Domains1 = expandDomains root5Node15Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node15Domains1 v = expandDomains root5Node15Domains1Fast v from by decide) v
theorem root5Node15Step1Chunk0_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk0_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk0_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk0_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk0_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk0_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk1_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk1_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk1_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk1_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk1_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk1_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk2_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk2_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk2_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk2_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk2_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk2_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk3_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk3_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk3_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk3_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk3_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk3_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk4_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk4_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk4_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk4_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk4_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk4_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk5_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk5_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk5_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk5_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk5_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk5_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk6_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk6_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk6_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk6_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk6_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk6_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk7_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk7_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk7_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk7_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk7_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk7_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk8_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk8_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk8_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk8_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk8_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk8_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1_checked :
    checkReplacement table2 root5Node15Domains0 root5Node15Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node15Step1Chunk0_0_checked, root5Node15Step1Chunk0_1_checked, root5Node15Step1Chunk0_2_checked, root5Node15Step1Chunk0_3_checked, root5Node15Step1Chunk0_4_checked, root5Node15Step1Chunk0_5_checked, root5Node15Step1Chunk1_0_checked, root5Node15Step1Chunk1_1_checked, root5Node15Step1Chunk1_2_checked, root5Node15Step1Chunk1_3_checked, root5Node15Step1Chunk1_4_checked, root5Node15Step1Chunk1_5_checked, root5Node15Step1Chunk2_0_checked, root5Node15Step1Chunk2_1_checked, root5Node15Step1Chunk2_2_checked, root5Node15Step1Chunk2_3_checked, root5Node15Step1Chunk2_4_checked, root5Node15Step1Chunk2_5_checked, root5Node15Step1Chunk3_0_checked, root5Node15Step1Chunk3_1_checked, root5Node15Step1Chunk3_2_checked, root5Node15Step1Chunk3_3_checked, root5Node15Step1Chunk3_4_checked, root5Node15Step1Chunk3_5_checked, root5Node15Step1Chunk4_0_checked, root5Node15Step1Chunk4_1_checked, root5Node15Step1Chunk4_2_checked, root5Node15Step1Chunk4_3_checked, root5Node15Step1Chunk4_4_checked, root5Node15Step1Chunk4_5_checked, root5Node15Step1Chunk5_0_checked, root5Node15Step1Chunk5_1_checked, root5Node15Step1Chunk5_2_checked, root5Node15Step1Chunk5_3_checked, root5Node15Step1Chunk5_4_checked, root5Node15Step1Chunk5_5_checked, root5Node15Step1Chunk6_0_checked, root5Node15Step1Chunk6_1_checked, root5Node15Step1Chunk6_2_checked, root5Node15Step1Chunk6_3_checked, root5Node15Step1Chunk6_4_checked, root5Node15Step1Chunk6_5_checked, root5Node15Step1Chunk7_0_checked, root5Node15Step1Chunk7_1_checked, root5Node15Step1Chunk7_2_checked, root5Node15Step1Chunk7_3_checked, root5Node15Step1Chunk7_4_checked, root5Node15Step1Chunk7_5_checked, root5Node15Step1Chunk8_0_checked, root5Node15Step1Chunk8_1_checked, root5Node15Step1Chunk8_2_checked, root5Node15Step1Chunk8_3_checked, root5Node15Step1Chunk8_4_checked, root5Node15Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
