module

public import SpectreFinite.RadiusThreeRoot8Part26
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable1
public import SpectreFinite.RadiusThreeTable10
public import SpectreFinite.RadiusThreeTable5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node52Domains0 : Domains 37 State := restrict root8Node36Domains3 1 (8,3)
def root8Node52Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(7,0),(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,2),(5,5),(8,2)]
  | 3 => some [(7,0),(8,0)]
  | 4 => some [(4,4),(5,1),(5,4),(8,4)]
  | 5 => some [(0,1),(1,4)]
  | 6 => some [(0,5),(6,2)]
  | 7 => some [(4,4),(8,4)]
  | 8 => some [(1,4),(6,4)]
  | 9 => some [(4,3),(5,3),(7,1),(8,3)]
  | 10 => some [(7,5),(8,5)]
  | 11 => some [(1,0),(6,0)]
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
theorem root8Node52Domains0_fast_eq : root8Node52Domains0 = expandDomains root8Node52Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node52Domains0 v = expandDomains root8Node52Domains0Fast v from by decide) v
def root8Node52Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0),(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(7,0),(8,0)]
  | 4 => [(4,4),(5,4),(8,4)]
  | 5 => [(1,4)]
  | 6 => [(0,5)]
  | 7 => [(4,4)]
  | 8 => [(1,4),(6,4)]
  | 9 => [(4,3),(7,1)]
  | 10 => [(7,5)]
  | 11 => [(6,0)]
  | 12 => [(7,1)]
  | 13 => [(7,5)]
  | 14 => [(0,3),(6,0)]
  | 15 => [(4,0),(7,4)]
  | 16 => [(1,3),(7,3)]
  | 17 => [(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2),(8,2)]
  | 21 => [(5,0),(5,3)]
  | 22 => [(0,1),(6,5)]
  | 23 => [(0,4),(6,2)]
  | 24 => [(5,4),(8,4)]
  | 25 => [(6,4)]
  | 26 => [(1,2)]
  | 27 => [(7,4),(8,4)]
  | 28 => [(1,0),(7,0)]
  | 29 => [(4,3),(7,1)]
  | 30 => [(3,5),(7,5)]
  | 31 => [(0,3)]
  | 32 => [(4,1),(8,1)]
  | 33 => [(1,4),(4,0),(7,4),(8,0)]
  | 34 => [(0,5),(1,3),(6,3),(7,3)]
  | 35 => [(2,2),(2,4),(4,2)]
  | _ => [(1,3),(3,3),(5,3)]
def root8Node52Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0),(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0),(8,0)]
  | 4 => some [(4,4),(5,4),(8,4)]
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
theorem root8Node52Domains1_fast_eq : root8Node52Domains1 = expandDomains root8Node52Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node52Domains1 v = expandDomains root8Node52Domains1Fast v from by decide) v
theorem root8Node52Step1Chunk0_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_0⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk0_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_1⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk0_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_2⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk0_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_3⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk0_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_4⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk0_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_5⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk1_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_0⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk1_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_1⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk1_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_2⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk1_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_3⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk1_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_4⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk1_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_5⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk2_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_0⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk2_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_1⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk2_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_2⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk2_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_3⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk2_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_4⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk2_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_5⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk3_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_0⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk3_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_1⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk3_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_2⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk3_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_3⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk3_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_4⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk3_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_5⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk4_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_0⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk4_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_1⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk4_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_2⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk4_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_3⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk4_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_4⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk4_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_5⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk5_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_0⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk5_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_1⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk5_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_2⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk5_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_3⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk5_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_4⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk5_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_5⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk6_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_0⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk6_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_1⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk6_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_2⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk6_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_3⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk6_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_4⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk6_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_5⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk7_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_0⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk7_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_1⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk7_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_2⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk7_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_3⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk7_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_4⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk7_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_5⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk8_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_0⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk8_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_1⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk8_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_2⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk8_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_3⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk8_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_4⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk8_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_5⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1_checked :
    checkReplacement table5 root8Node52Domains0 root8Node52Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node52Step1Chunk0_0_checked, root8Node52Step1Chunk0_1_checked, root8Node52Step1Chunk0_2_checked, root8Node52Step1Chunk0_3_checked, root8Node52Step1Chunk0_4_checked, root8Node52Step1Chunk0_5_checked, root8Node52Step1Chunk1_0_checked, root8Node52Step1Chunk1_1_checked, root8Node52Step1Chunk1_2_checked, root8Node52Step1Chunk1_3_checked, root8Node52Step1Chunk1_4_checked, root8Node52Step1Chunk1_5_checked, root8Node52Step1Chunk2_0_checked, root8Node52Step1Chunk2_1_checked, root8Node52Step1Chunk2_2_checked, root8Node52Step1Chunk2_3_checked, root8Node52Step1Chunk2_4_checked, root8Node52Step1Chunk2_5_checked, root8Node52Step1Chunk3_0_checked, root8Node52Step1Chunk3_1_checked, root8Node52Step1Chunk3_2_checked, root8Node52Step1Chunk3_3_checked, root8Node52Step1Chunk3_4_checked, root8Node52Step1Chunk3_5_checked, root8Node52Step1Chunk4_0_checked, root8Node52Step1Chunk4_1_checked, root8Node52Step1Chunk4_2_checked, root8Node52Step1Chunk4_3_checked, root8Node52Step1Chunk4_4_checked, root8Node52Step1Chunk4_5_checked, root8Node52Step1Chunk5_0_checked, root8Node52Step1Chunk5_1_checked, root8Node52Step1Chunk5_2_checked, root8Node52Step1Chunk5_3_checked, root8Node52Step1Chunk5_4_checked, root8Node52Step1Chunk5_5_checked, root8Node52Step1Chunk6_0_checked, root8Node52Step1Chunk6_1_checked, root8Node52Step1Chunk6_2_checked, root8Node52Step1Chunk6_3_checked, root8Node52Step1Chunk6_4_checked, root8Node52Step1Chunk6_5_checked, root8Node52Step1Chunk7_0_checked, root8Node52Step1Chunk7_1_checked, root8Node52Step1Chunk7_2_checked, root8Node52Step1Chunk7_3_checked, root8Node52Step1Chunk7_4_checked, root8Node52Step1Chunk7_5_checked, root8Node52Step1Chunk8_0_checked, root8Node52Step1Chunk8_1_checked, root8Node52Step1Chunk8_2_checked, root8Node52Step1Chunk8_3_checked, root8Node52Step1Chunk8_4_checked, root8Node52Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node52Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0),(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(7,0)]
  | 4 => [(4,4),(5,4),(8,4)]
  | 5 => [(1,4)]
  | 6 => [(0,5)]
  | 7 => [(4,4)]
  | 8 => [(1,4),(6,4)]
  | 9 => [(4,3),(7,1)]
  | 10 => [(7,5)]
  | 11 => [(6,0)]
  | 12 => [(7,1)]
  | 13 => [(7,5)]
  | 14 => [(0,3),(6,0)]
  | 15 => [(4,0),(7,4)]
  | 16 => [(1,3),(7,3)]
  | 17 => [(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2),(8,2)]
  | 21 => [(5,0),(5,3)]
  | 22 => [(0,1),(6,5)]
  | 23 => [(0,4),(6,2)]
  | 24 => [(5,4),(8,4)]
  | 25 => [(6,4)]
  | 26 => [(1,2)]
  | 27 => [(7,4),(8,4)]
  | 28 => [(1,0),(7,0)]
  | 29 => [(4,3),(7,1)]
  | 30 => [(3,5),(7,5)]
  | 31 => [(0,3)]
  | 32 => [(4,1),(8,1)]
  | 33 => [(1,4),(4,0),(7,4),(8,0)]
  | 34 => [(0,5),(1,3),(6,3),(7,3)]
  | 35 => [(2,2),(2,4),(4,2)]
  | _ => [(1,3),(3,3),(5,3)]
def root8Node52Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0),(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,4),(5,4),(8,4)]
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
theorem root8Node52Domains2_fast_eq : root8Node52Domains2 = expandDomains root8Node52Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node52Domains2 v = expandDomains root8Node52Domains2Fast v from by decide) v
theorem root8Node52Step2Chunk0_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_0⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk0_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_1⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk0_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_2⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk0_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_3⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk0_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_4⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk0_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_5⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk1_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_0⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk1_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_1⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk1_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_2⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk1_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_3⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk1_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_4⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk1_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_5⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk2_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_0⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk2_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_1⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk2_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_2⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk2_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_3⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk2_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_4⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk2_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_5⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk3_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_0⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk3_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_1⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk3_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_2⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk3_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_3⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk3_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_4⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk3_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_5⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk4_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_0⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk4_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_1⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk4_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_2⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk4_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_3⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk4_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_4⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk4_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_5⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk5_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_0⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk5_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_1⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk5_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_2⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk5_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_3⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk5_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_4⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk5_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_5⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk6_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_0⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk6_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_1⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk6_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_2⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk6_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_3⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk6_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_4⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk6_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_5⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk7_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_0⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk7_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_1⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk7_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_2⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk7_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_3⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk7_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_4⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk7_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_5⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk8_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_0⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk8_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_1⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk8_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_2⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk8_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_3⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk8_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_4⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk8_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_5⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2_checked :
    checkReplacement table1 root8Node52Domains1 root8Node52Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node52Step2Chunk0_0_checked, root8Node52Step2Chunk0_1_checked, root8Node52Step2Chunk0_2_checked, root8Node52Step2Chunk0_3_checked, root8Node52Step2Chunk0_4_checked, root8Node52Step2Chunk0_5_checked, root8Node52Step2Chunk1_0_checked, root8Node52Step2Chunk1_1_checked, root8Node52Step2Chunk1_2_checked, root8Node52Step2Chunk1_3_checked, root8Node52Step2Chunk1_4_checked, root8Node52Step2Chunk1_5_checked, root8Node52Step2Chunk2_0_checked, root8Node52Step2Chunk2_1_checked, root8Node52Step2Chunk2_2_checked, root8Node52Step2Chunk2_3_checked, root8Node52Step2Chunk2_4_checked, root8Node52Step2Chunk2_5_checked, root8Node52Step2Chunk3_0_checked, root8Node52Step2Chunk3_1_checked, root8Node52Step2Chunk3_2_checked, root8Node52Step2Chunk3_3_checked, root8Node52Step2Chunk3_4_checked, root8Node52Step2Chunk3_5_checked, root8Node52Step2Chunk4_0_checked, root8Node52Step2Chunk4_1_checked, root8Node52Step2Chunk4_2_checked, root8Node52Step2Chunk4_3_checked, root8Node52Step2Chunk4_4_checked, root8Node52Step2Chunk4_5_checked, root8Node52Step2Chunk5_0_checked, root8Node52Step2Chunk5_1_checked, root8Node52Step2Chunk5_2_checked, root8Node52Step2Chunk5_3_checked, root8Node52Step2Chunk5_4_checked, root8Node52Step2Chunk5_5_checked, root8Node52Step2Chunk6_0_checked, root8Node52Step2Chunk6_1_checked, root8Node52Step2Chunk6_2_checked, root8Node52Step2Chunk6_3_checked, root8Node52Step2Chunk6_4_checked, root8Node52Step2Chunk6_5_checked, root8Node52Step2Chunk7_0_checked, root8Node52Step2Chunk7_1_checked, root8Node52Step2Chunk7_2_checked, root8Node52Step2Chunk7_3_checked, root8Node52Step2Chunk7_4_checked, root8Node52Step2Chunk7_5_checked, root8Node52Step2Chunk8_0_checked, root8Node52Step2Chunk8_1_checked, root8Node52Step2Chunk8_2_checked, root8Node52Step2Chunk8_3_checked, root8Node52Step2Chunk8_4_checked, root8Node52Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node53Domains0 : Domains 37 State := restrict root8Node52Domains2 0 (7,0)
def root8Node53Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,4),(5,4),(8,4)]
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
theorem root8Node53Domains0_fast_eq : root8Node53Domains0 = expandDomains root8Node53Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node53Domains0 v = expandDomains root8Node53Domains0Fast v from by decide) v
def root8Node53Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(7,0)]
  | 4 => [(4,4)]
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
  | 28 => [(1,0),(7,0)]
  | 29 => [(4,3),(7,1)]
  | 30 => [(3,5),(7,5)]
  | 31 => [(0,3)]
  | 32 => [(4,1),(8,1)]
  | 33 => [(1,4),(4,0),(7,4),(8,0)]
  | 34 => [(0,5),(1,3),(6,3),(7,3)]
  | 35 => [(2,2),(2,4),(4,2)]
  | _ => [(1,3),(3,3),(5,3)]
def root8Node53Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,4)]
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
  | 28 => some [(1,0),(7,0)]
  | 29 => some [(4,3),(7,1)]
  | 30 => some [(3,5),(7,5)]
  | 31 => some [(0,3)]
  | 32 => some [(4,1),(8,1)]
  | 33 => some [(1,4),(4,0),(7,4),(8,0)]
  | 34 => some [(0,5),(1,3),(6,3),(7,3)]
  | 35 => some [(2,2),(2,4),(4,2)]
  | _ => some [(1,3),(3,3),(5,3)]
theorem root8Node53Domains1_fast_eq : root8Node53Domains1 = expandDomains root8Node53Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node53Domains1 v = expandDomains root8Node53Domains1Fast v from by decide) v
theorem root8Node53Step1Chunk0_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_0⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk0_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_1⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk0_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_2⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk0_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_3⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk0_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_4⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk0_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_5⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk1_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_0⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk1_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_1⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk1_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_2⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk1_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_3⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk1_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_4⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk1_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_5⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk2_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_0⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk2_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_1⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk2_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_2⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk2_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_3⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk2_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_4⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk2_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_5⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk3_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_0⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk3_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_1⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk3_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_2⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk3_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_3⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk3_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_4⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk3_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_5⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk4_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_0⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk4_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_1⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk4_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_2⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk4_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_3⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk4_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_4⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk4_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_5⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk5_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_0⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk5_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_1⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk5_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_2⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk5_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_3⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk5_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_4⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk5_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_5⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk6_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_0⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk6_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_1⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk6_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_2⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk6_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_3⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk6_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_4⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk6_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_5⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk7_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_0⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk7_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_1⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk7_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_2⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk7_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_3⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk7_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_4⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk7_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_5⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk8_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_0⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk8_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_1⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk8_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_2⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk8_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_3⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk8_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_4⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk8_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_5⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1_checked :
    checkReplacement table10 root8Node53Domains0 root8Node53Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node53Step1Chunk0_0_checked, root8Node53Step1Chunk0_1_checked, root8Node53Step1Chunk0_2_checked, root8Node53Step1Chunk0_3_checked, root8Node53Step1Chunk0_4_checked, root8Node53Step1Chunk0_5_checked, root8Node53Step1Chunk1_0_checked, root8Node53Step1Chunk1_1_checked, root8Node53Step1Chunk1_2_checked, root8Node53Step1Chunk1_3_checked, root8Node53Step1Chunk1_4_checked, root8Node53Step1Chunk1_5_checked, root8Node53Step1Chunk2_0_checked, root8Node53Step1Chunk2_1_checked, root8Node53Step1Chunk2_2_checked, root8Node53Step1Chunk2_3_checked, root8Node53Step1Chunk2_4_checked, root8Node53Step1Chunk2_5_checked, root8Node53Step1Chunk3_0_checked, root8Node53Step1Chunk3_1_checked, root8Node53Step1Chunk3_2_checked, root8Node53Step1Chunk3_3_checked, root8Node53Step1Chunk3_4_checked, root8Node53Step1Chunk3_5_checked, root8Node53Step1Chunk4_0_checked, root8Node53Step1Chunk4_1_checked, root8Node53Step1Chunk4_2_checked, root8Node53Step1Chunk4_3_checked, root8Node53Step1Chunk4_4_checked, root8Node53Step1Chunk4_5_checked, root8Node53Step1Chunk5_0_checked, root8Node53Step1Chunk5_1_checked, root8Node53Step1Chunk5_2_checked, root8Node53Step1Chunk5_3_checked, root8Node53Step1Chunk5_4_checked, root8Node53Step1Chunk5_5_checked, root8Node53Step1Chunk6_0_checked, root8Node53Step1Chunk6_1_checked, root8Node53Step1Chunk6_2_checked, root8Node53Step1Chunk6_3_checked, root8Node53Step1Chunk6_4_checked, root8Node53Step1Chunk6_5_checked, root8Node53Step1Chunk7_0_checked, root8Node53Step1Chunk7_1_checked, root8Node53Step1Chunk7_2_checked, root8Node53Step1Chunk7_3_checked, root8Node53Step1Chunk7_4_checked, root8Node53Step1Chunk7_5_checked, root8Node53Step1Chunk8_0_checked, root8Node53Step1Chunk8_1_checked, root8Node53Step1Chunk8_2_checked, root8Node53Step1Chunk8_3_checked, root8Node53Step1Chunk8_4_checked, root8Node53Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
