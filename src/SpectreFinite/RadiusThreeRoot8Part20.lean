module

public import SpectreFinite.RadiusThreeRoot8Part19
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable1
public import SpectreFinite.RadiusThreeTable10
public import SpectreFinite.RadiusThreeTable23

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node37Domains0 : Domains 37 State := restrict root8Node36Domains3 1 (7,3)
def root8Node37Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(7,0),(8,0)]
  | 1 => some [(7,3)]
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
theorem root8Node37Domains0_fast_eq : root8Node37Domains0 = expandDomains root8Node37Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node37Domains0 v = expandDomains root8Node37Domains0Fast v from by decide) v
def root8Node37Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2),(5,5),(8,2)]
  | 3 => [(7,0),(8,0)]
  | 4 => [(5,1)]
  | 5 => [(0,1)]
  | 6 => [(6,2)]
  | 7 => [(4,4),(8,4)]
  | 8 => [(1,4),(6,4)]
  | 9 => [(5,3),(8,3)]
  | 10 => [(8,5)]
  | 11 => [(1,0)]
  | 12 => [(7,1)]
  | 13 => [(7,5)]
  | 14 => [(0,3),(6,0)]
  | 15 => [(7,4)]
  | 16 => [(1,3)]
  | 17 => [(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2),(8,2)]
  | 21 => [(5,0),(5,3)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
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
def root8Node37Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2),(5,5),(8,2)]
  | 3 => some [(7,0),(8,0)]
  | 4 => some [(5,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(4,4),(8,4)]
  | 8 => some [(1,4),(6,4)]
  | 9 => some [(5,3),(8,3)]
  | 10 => some [(8,5)]
  | 11 => some [(1,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3),(6,0)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2),(8,2)]
  | 21 => some [(5,0),(5,3)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
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
theorem root8Node37Domains1_fast_eq : root8Node37Domains1 = expandDomains root8Node37Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node37Domains1 v = expandDomains root8Node37Domains1Fast v from by decide) v
theorem root8Node37Step1Chunk0_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_0⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk0_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_1⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk0_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_2⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk0_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_3⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk0_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_4⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk0_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_5⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk1_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_0⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk1_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_1⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk1_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_2⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk1_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_3⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk1_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_4⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk1_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_5⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk2_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_0⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk2_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_1⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk2_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_2⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk2_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_3⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk2_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_4⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk2_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_5⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk3_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_0⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk3_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_1⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk3_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_2⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk3_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_3⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk3_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_4⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk3_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_5⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk4_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_0⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk4_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_1⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk4_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_2⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk4_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_3⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk4_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_4⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk4_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_5⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk5_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_0⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk5_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_1⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk5_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_2⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk5_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_3⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk5_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_4⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk5_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_5⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk6_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_0⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk6_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_1⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk6_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_2⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk6_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_3⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk6_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_4⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk6_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_5⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk7_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_0⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk7_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_1⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk7_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_2⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk7_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_3⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk7_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_4⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk7_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_5⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk8_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_0⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk8_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_1⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk8_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_2⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk8_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_3⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk8_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_4⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1Chunk8_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_5⟩
      root8Node37Domains0 root8Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains0 root8Node37Domains1
    root8Node37Domains0Fast root8Node37Domains1Fast
    root8Node37Domains0_fast_eq root8Node37Domains1_fast_eq (by decide)
theorem root8Node37Step1_checked :
    checkReplacement table10 root8Node37Domains0 root8Node37Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node37Step1Chunk0_0_checked, root8Node37Step1Chunk0_1_checked, root8Node37Step1Chunk0_2_checked, root8Node37Step1Chunk0_3_checked, root8Node37Step1Chunk0_4_checked, root8Node37Step1Chunk0_5_checked, root8Node37Step1Chunk1_0_checked, root8Node37Step1Chunk1_1_checked, root8Node37Step1Chunk1_2_checked, root8Node37Step1Chunk1_3_checked, root8Node37Step1Chunk1_4_checked, root8Node37Step1Chunk1_5_checked, root8Node37Step1Chunk2_0_checked, root8Node37Step1Chunk2_1_checked, root8Node37Step1Chunk2_2_checked, root8Node37Step1Chunk2_3_checked, root8Node37Step1Chunk2_4_checked, root8Node37Step1Chunk2_5_checked, root8Node37Step1Chunk3_0_checked, root8Node37Step1Chunk3_1_checked, root8Node37Step1Chunk3_2_checked, root8Node37Step1Chunk3_3_checked, root8Node37Step1Chunk3_4_checked, root8Node37Step1Chunk3_5_checked, root8Node37Step1Chunk4_0_checked, root8Node37Step1Chunk4_1_checked, root8Node37Step1Chunk4_2_checked, root8Node37Step1Chunk4_3_checked, root8Node37Step1Chunk4_4_checked, root8Node37Step1Chunk4_5_checked, root8Node37Step1Chunk5_0_checked, root8Node37Step1Chunk5_1_checked, root8Node37Step1Chunk5_2_checked, root8Node37Step1Chunk5_3_checked, root8Node37Step1Chunk5_4_checked, root8Node37Step1Chunk5_5_checked, root8Node37Step1Chunk6_0_checked, root8Node37Step1Chunk6_1_checked, root8Node37Step1Chunk6_2_checked, root8Node37Step1Chunk6_3_checked, root8Node37Step1Chunk6_4_checked, root8Node37Step1Chunk6_5_checked, root8Node37Step1Chunk7_0_checked, root8Node37Step1Chunk7_1_checked, root8Node37Step1Chunk7_2_checked, root8Node37Step1Chunk7_3_checked, root8Node37Step1Chunk7_4_checked, root8Node37Step1Chunk7_5_checked, root8Node37Step1Chunk8_0_checked, root8Node37Step1Chunk8_1_checked, root8Node37Step1Chunk8_2_checked, root8Node37Step1Chunk8_3_checked, root8Node37Step1Chunk8_4_checked, root8Node37Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node37Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2),(5,5),(8,2)]
  | 3 => [(7,0),(8,0)]
  | 4 => [(5,1)]
  | 5 => [(0,1)]
  | 6 => [(6,2)]
  | 7 => [(4,4),(8,4)]
  | 8 => [(1,4),(6,4)]
  | 9 => [(5,3),(8,3)]
  | 10 => [(8,5)]
  | 11 => [(1,0)]
  | 12 => [(7,1)]
  | 13 => [(7,5)]
  | 14 => [(0,3),(6,0)]
  | 15 => [(7,4)]
  | 16 => [(1,3)]
  | 17 => [(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2),(8,2)]
  | 21 => [(5,0),(5,3)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(6,4)]
  | 26 => [(1,2)]
  | 27 => [(7,4),(8,4)]
  | 28 => [(7,0)]
  | 29 => [(4,3)]
  | 30 => [(3,5),(7,5)]
  | 31 => [(0,3)]
  | 32 => [(4,1),(8,1)]
  | 33 => [(1,4),(7,4)]
  | 34 => [(0,5),(1,3),(6,3)]
  | 35 => [(2,2),(2,4),(4,2)]
  | _ => [(1,3),(3,3),(5,3)]
def root8Node37Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2),(5,5),(8,2)]
  | 3 => some [(7,0),(8,0)]
  | 4 => some [(5,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(4,4),(8,4)]
  | 8 => some [(1,4),(6,4)]
  | 9 => some [(5,3),(8,3)]
  | 10 => some [(8,5)]
  | 11 => some [(1,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3),(6,0)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2),(8,2)]
  | 21 => some [(5,0),(5,3)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(6,4)]
  | 26 => some [(1,2)]
  | 27 => some [(7,4),(8,4)]
  | 28 => some [(7,0)]
  | 29 => some [(4,3)]
  | 30 => some [(3,5),(7,5)]
  | 31 => some [(0,3)]
  | 32 => some [(4,1),(8,1)]
  | 33 => some [(1,4),(7,4)]
  | 34 => some [(0,5),(1,3),(6,3)]
  | 35 => some [(2,2),(2,4),(4,2)]
  | _ => some [(1,3),(3,3),(5,3)]
theorem root8Node37Domains2_fast_eq : root8Node37Domains2 = expandDomains root8Node37Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node37Domains2 v = expandDomains root8Node37Domains2Fast v from by decide) v
theorem root8Node37Step2Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2_checked :
    checkReplacement table23 root8Node37Domains1 root8Node37Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node37Step2Chunk0_0_checked, root8Node37Step2Chunk0_1_checked, root8Node37Step2Chunk0_2_checked, root8Node37Step2Chunk0_3_checked, root8Node37Step2Chunk0_4_checked, root8Node37Step2Chunk0_5_checked, root8Node37Step2Chunk1_0_checked, root8Node37Step2Chunk1_1_checked, root8Node37Step2Chunk1_2_checked, root8Node37Step2Chunk1_3_checked, root8Node37Step2Chunk1_4_checked, root8Node37Step2Chunk1_5_checked, root8Node37Step2Chunk2_0_checked, root8Node37Step2Chunk2_1_checked, root8Node37Step2Chunk2_2_checked, root8Node37Step2Chunk2_3_checked, root8Node37Step2Chunk2_4_checked, root8Node37Step2Chunk2_5_checked, root8Node37Step2Chunk3_0_checked, root8Node37Step2Chunk3_1_checked, root8Node37Step2Chunk3_2_checked, root8Node37Step2Chunk3_3_checked, root8Node37Step2Chunk3_4_checked, root8Node37Step2Chunk3_5_checked, root8Node37Step2Chunk4_0_checked, root8Node37Step2Chunk4_1_checked, root8Node37Step2Chunk4_2_checked, root8Node37Step2Chunk4_3_checked, root8Node37Step2Chunk4_4_checked, root8Node37Step2Chunk4_5_checked, root8Node37Step2Chunk5_0_checked, root8Node37Step2Chunk5_1_checked, root8Node37Step2Chunk5_2_checked, root8Node37Step2Chunk5_3_checked, root8Node37Step2Chunk5_4_checked, root8Node37Step2Chunk5_5_checked, root8Node37Step2Chunk6_0_checked, root8Node37Step2Chunk6_1_checked, root8Node37Step2Chunk6_2_checked, root8Node37Step2Chunk6_3_checked, root8Node37Step2Chunk6_4_checked, root8Node37Step2Chunk6_5_checked, root8Node37Step2Chunk7_0_checked, root8Node37Step2Chunk7_1_checked, root8Node37Step2Chunk7_2_checked, root8Node37Step2Chunk7_3_checked, root8Node37Step2Chunk7_4_checked, root8Node37Step2Chunk7_5_checked, root8Node37Step2Chunk8_0_checked, root8Node37Step2Chunk8_1_checked, root8Node37Step2Chunk8_2_checked, root8Node37Step2Chunk8_3_checked, root8Node37Step2Chunk8_4_checked, root8Node37Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node37Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2),(8,2)]
  | 3 => [(8,0)]
  | 4 => [(5,1)]
  | 5 => [(0,1)]
  | 6 => [(6,2)]
  | 7 => [(8,4)]
  | 8 => [(1,4),(6,4)]
  | 9 => [(5,3),(8,3)]
  | 10 => [(8,5)]
  | 11 => [(1,0)]
  | 12 => [(7,1)]
  | 13 => [(7,5)]
  | 14 => [(0,3),(6,0)]
  | 15 => [(7,4)]
  | 16 => [(1,3)]
  | 17 => [(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2),(8,2)]
  | 21 => [(5,0),(5,3)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(6,4)]
  | 26 => [(1,2)]
  | 27 => [(7,4),(8,4)]
  | 28 => [(7,0)]
  | 29 => [(4,3)]
  | 30 => [(3,5),(7,5)]
  | 31 => [(0,3)]
  | 32 => [(4,1),(8,1)]
  | 33 => [(1,4),(7,4)]
  | 34 => [(0,5),(1,3),(6,3)]
  | 35 => [(2,2),(2,4),(4,2)]
  | _ => [(1,3),(3,3),(5,3)]
def root8Node37Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2),(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(5,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(8,4)]
  | 8 => some [(1,4),(6,4)]
  | 9 => some [(5,3),(8,3)]
  | 10 => some [(8,5)]
  | 11 => some [(1,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3),(6,0)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2),(8,2)]
  | 21 => some [(5,0),(5,3)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(6,4)]
  | 26 => some [(1,2)]
  | 27 => some [(7,4),(8,4)]
  | 28 => some [(7,0)]
  | 29 => some [(4,3)]
  | 30 => some [(3,5),(7,5)]
  | 31 => some [(0,3)]
  | 32 => some [(4,1),(8,1)]
  | 33 => some [(1,4),(7,4)]
  | 34 => some [(0,5),(1,3),(6,3)]
  | 35 => some [(2,2),(2,4),(4,2)]
  | _ => some [(1,3),(3,3),(5,3)]
theorem root8Node37Domains3_fast_eq : root8Node37Domains3 = expandDomains root8Node37Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node37Domains3 v = expandDomains root8Node37Domains3Fast v from by decide) v
theorem root8Node37Step3Chunk0_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_0⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk0_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_1⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk0_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_2⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk0_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_3⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk0_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_4⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk0_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_5⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk1_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_0⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk1_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_1⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk1_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_2⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk1_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_3⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk1_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_4⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk1_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_5⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk2_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_0⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk2_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_1⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk2_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_2⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk2_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_3⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk2_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_4⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk2_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_5⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk3_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_0⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk3_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_1⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk3_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_2⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk3_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_3⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk3_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_4⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk3_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_5⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk4_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_0⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk4_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_1⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk4_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_2⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk4_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_3⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk4_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_4⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk4_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_5⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk5_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_0⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk5_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_1⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk5_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_2⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk5_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_3⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk5_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_4⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk5_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_5⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk6_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_0⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk6_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_1⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk6_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_2⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk6_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_3⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk6_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_4⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk6_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_5⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk7_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_0⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk7_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_1⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk7_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_2⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk7_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_3⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk7_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_4⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk7_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_5⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk8_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_0⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk8_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_1⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk8_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_2⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk8_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_3⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk8_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_4⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk8_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_5⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3_checked :
    checkReplacement table1 root8Node37Domains2 root8Node37Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node37Step3Chunk0_0_checked, root8Node37Step3Chunk0_1_checked, root8Node37Step3Chunk0_2_checked, root8Node37Step3Chunk0_3_checked, root8Node37Step3Chunk0_4_checked, root8Node37Step3Chunk0_5_checked, root8Node37Step3Chunk1_0_checked, root8Node37Step3Chunk1_1_checked, root8Node37Step3Chunk1_2_checked, root8Node37Step3Chunk1_3_checked, root8Node37Step3Chunk1_4_checked, root8Node37Step3Chunk1_5_checked, root8Node37Step3Chunk2_0_checked, root8Node37Step3Chunk2_1_checked, root8Node37Step3Chunk2_2_checked, root8Node37Step3Chunk2_3_checked, root8Node37Step3Chunk2_4_checked, root8Node37Step3Chunk2_5_checked, root8Node37Step3Chunk3_0_checked, root8Node37Step3Chunk3_1_checked, root8Node37Step3Chunk3_2_checked, root8Node37Step3Chunk3_3_checked, root8Node37Step3Chunk3_4_checked, root8Node37Step3Chunk3_5_checked, root8Node37Step3Chunk4_0_checked, root8Node37Step3Chunk4_1_checked, root8Node37Step3Chunk4_2_checked, root8Node37Step3Chunk4_3_checked, root8Node37Step3Chunk4_4_checked, root8Node37Step3Chunk4_5_checked, root8Node37Step3Chunk5_0_checked, root8Node37Step3Chunk5_1_checked, root8Node37Step3Chunk5_2_checked, root8Node37Step3Chunk5_3_checked, root8Node37Step3Chunk5_4_checked, root8Node37Step3Chunk5_5_checked, root8Node37Step3Chunk6_0_checked, root8Node37Step3Chunk6_1_checked, root8Node37Step3Chunk6_2_checked, root8Node37Step3Chunk6_3_checked, root8Node37Step3Chunk6_4_checked, root8Node37Step3Chunk6_5_checked, root8Node37Step3Chunk7_0_checked, root8Node37Step3Chunk7_1_checked, root8Node37Step3Chunk7_2_checked, root8Node37Step3Chunk7_3_checked, root8Node37Step3Chunk7_4_checked, root8Node37Step3Chunk7_5_checked, root8Node37Step3Chunk8_0_checked, root8Node37Step3Chunk8_1_checked, root8Node37Step3Chunk8_2_checked, root8Node37Step3Chunk8_3_checked, root8Node37Step3Chunk8_4_checked, root8Node37Step3Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
