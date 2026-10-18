module

public import SpectreFinite.RadiusThreeRoot8Part18
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable12
public import SpectreFinite.RadiusThreeTable26
public import SpectreFinite.RadiusThreeTable4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node36Domains0 : Domains 37 State := restrict root8Node0Domains5 12 (7,1)
def root8Node36Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(4,2),(7,0),(8,0)]
  | 1 => some [(4,3),(5,3),(7,3),(8,3)]
  | 2 => some [(5,2),(5,5),(7,5),(8,2),(8,5)]
  | 3 => some [(1,0),(6,0),(7,0),(8,0)]
  | 4 => some [(1,2),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 5 => some [(0,1),(1,4),(7,4)]
  | 6 => some [(0,5),(6,2),(6,3)]
  | 7 => some [(4,4),(7,2),(8,4)]
  | 8 => some [(1,4),(4,0),(6,4),(7,4)]
  | 9 => some [(0,3),(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 10 => some [(4,1),(7,5),(8,5)]
  | 11 => some [(0,2),(1,0),(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(4,1),(5,1),(7,5),(8,1)]
  | 14 => some [(0,1),(0,2),(0,3),(6,0),(6,5)]
  | 15 => some [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 16 => some [(1,3),(3,3),(7,3)]
  | 17 => some [(5,2),(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(4,2),(5,2),(5,5),(8,2)]
  | 21 => some [(1,0),(3,0),(5,0),(5,3),(7,0)]
  | 22 => some [(0,1),(6,5)]
  | 23 => some [(0,4),(6,2)]
  | 24 => some [(5,4),(8,4)]
  | 25 => some [(1,4),(6,4)]
  | 26 => some [(0,5),(1,2)]
  | 27 => some [(4,4),(7,4),(8,4)]
  | 28 => some [(1,0),(7,0)]
  | 29 => some [(4,3),(7,1)]
  | 30 => some [(3,5),(7,5)]
  | 31 => some [(0,3),(6,0)]
  | 32 => some [(4,1),(7,1),(8,1)]
  | 33 => some [(1,4),(4,0),(7,4),(8,0)]
  | 34 => some [(0,5),(1,3),(6,3),(7,3)]
  | 35 => some [(2,2),(2,4),(4,2),(7,2),(8,2)]
  | _ => some [(1,3),(3,3),(4,0),(5,0),(5,3),(8,0)]
theorem root8Node36Domains0_fast_eq : root8Node36Domains0 = expandDomains root8Node36Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node36Domains0 v = expandDomains root8Node36Domains0Fast v from by decide) v
def root8Node36Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,0),(4,2),(7,0),(8,0)]
  | 1 => [(7,3),(8,3)]
  | 2 => [(5,2),(5,5),(8,2)]
  | 3 => [(7,0),(8,0)]
  | 4 => [(1,2),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 5 => [(0,1),(1,4)]
  | 6 => [(0,5),(6,2)]
  | 7 => [(4,4),(8,4)]
  | 8 => [(1,4),(6,4)]
  | 9 => [(0,3),(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 10 => [(7,5),(8,5)]
  | 11 => [(1,0),(6,0)]
  | 12 => [(7,1)]
  | 13 => [(7,5)]
  | 14 => [(0,3),(6,0)]
  | 15 => [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 16 => [(1,3),(3,3),(7,3)]
  | 17 => [(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2),(8,2)]
  | 21 => [(1,0),(3,0),(5,0),(5,3),(7,0)]
  | 22 => [(0,1),(6,5)]
  | 23 => [(0,4),(6,2)]
  | 24 => [(5,4),(8,4)]
  | 25 => [(6,4)]
  | 26 => [(1,2)]
  | 27 => [(4,4),(7,4),(8,4)]
  | 28 => [(1,0),(7,0)]
  | 29 => [(4,3),(7,1)]
  | 30 => [(3,5),(7,5)]
  | 31 => [(0,3),(6,0)]
  | 32 => [(4,1),(7,1),(8,1)]
  | 33 => [(1,4),(4,0),(7,4),(8,0)]
  | 34 => [(0,5),(1,3),(6,3),(7,3)]
  | 35 => [(2,2),(2,4),(4,2),(7,2),(8,2)]
  | _ => [(1,3),(3,3),(4,0),(5,0),(5,3),(8,0)]
def root8Node36Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(4,2),(7,0),(8,0)]
  | 1 => some [(7,3),(8,3)]
  | 2 => some [(5,2),(5,5),(8,2)]
  | 3 => some [(7,0),(8,0)]
  | 4 => some [(1,2),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 5 => some [(0,1),(1,4)]
  | 6 => some [(0,5),(6,2)]
  | 7 => some [(4,4),(8,4)]
  | 8 => some [(1,4),(6,4)]
  | 9 => some [(0,3),(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 10 => some [(7,5),(8,5)]
  | 11 => some [(1,0),(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3),(6,0)]
  | 15 => some [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 16 => some [(1,3),(3,3),(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2),(8,2)]
  | 21 => some [(1,0),(3,0),(5,0),(5,3),(7,0)]
  | 22 => some [(0,1),(6,5)]
  | 23 => some [(0,4),(6,2)]
  | 24 => some [(5,4),(8,4)]
  | 25 => some [(6,4)]
  | 26 => some [(1,2)]
  | 27 => some [(4,4),(7,4),(8,4)]
  | 28 => some [(1,0),(7,0)]
  | 29 => some [(4,3),(7,1)]
  | 30 => some [(3,5),(7,5)]
  | 31 => some [(0,3),(6,0)]
  | 32 => some [(4,1),(7,1),(8,1)]
  | 33 => some [(1,4),(4,0),(7,4),(8,0)]
  | 34 => some [(0,5),(1,3),(6,3),(7,3)]
  | 35 => some [(2,2),(2,4),(4,2),(7,2),(8,2)]
  | _ => some [(1,3),(3,3),(4,0),(5,0),(5,3),(8,0)]
theorem root8Node36Domains1_fast_eq : root8Node36Domains1 = expandDomains root8Node36Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node36Domains1 v = expandDomains root8Node36Domains1Fast v from by decide) v
theorem root8Node36Step1Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root8Node36Domains0 root8Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains0 root8Node36Domains1
    root8Node36Domains0Fast root8Node36Domains1Fast
    root8Node36Domains0_fast_eq root8Node36Domains1_fast_eq (by decide)
theorem root8Node36Step1_checked :
    checkReplacement table12 root8Node36Domains0 root8Node36Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node36Step1Chunk0_0_checked, root8Node36Step1Chunk0_1_checked, root8Node36Step1Chunk0_2_checked, root8Node36Step1Chunk0_3_checked, root8Node36Step1Chunk0_4_checked, root8Node36Step1Chunk0_5_checked, root8Node36Step1Chunk1_0_checked, root8Node36Step1Chunk1_1_checked, root8Node36Step1Chunk1_2_checked, root8Node36Step1Chunk1_3_checked, root8Node36Step1Chunk1_4_checked, root8Node36Step1Chunk1_5_checked, root8Node36Step1Chunk2_0_checked, root8Node36Step1Chunk2_1_checked, root8Node36Step1Chunk2_2_checked, root8Node36Step1Chunk2_3_checked, root8Node36Step1Chunk2_4_checked, root8Node36Step1Chunk2_5_checked, root8Node36Step1Chunk3_0_checked, root8Node36Step1Chunk3_1_checked, root8Node36Step1Chunk3_2_checked, root8Node36Step1Chunk3_3_checked, root8Node36Step1Chunk3_4_checked, root8Node36Step1Chunk3_5_checked, root8Node36Step1Chunk4_0_checked, root8Node36Step1Chunk4_1_checked, root8Node36Step1Chunk4_2_checked, root8Node36Step1Chunk4_3_checked, root8Node36Step1Chunk4_4_checked, root8Node36Step1Chunk4_5_checked, root8Node36Step1Chunk5_0_checked, root8Node36Step1Chunk5_1_checked, root8Node36Step1Chunk5_2_checked, root8Node36Step1Chunk5_3_checked, root8Node36Step1Chunk5_4_checked, root8Node36Step1Chunk5_5_checked, root8Node36Step1Chunk6_0_checked, root8Node36Step1Chunk6_1_checked, root8Node36Step1Chunk6_2_checked, root8Node36Step1Chunk6_3_checked, root8Node36Step1Chunk6_4_checked, root8Node36Step1Chunk6_5_checked, root8Node36Step1Chunk7_0_checked, root8Node36Step1Chunk7_1_checked, root8Node36Step1Chunk7_2_checked, root8Node36Step1Chunk7_3_checked, root8Node36Step1Chunk7_4_checked, root8Node36Step1Chunk7_5_checked, root8Node36Step1Chunk8_0_checked, root8Node36Step1Chunk8_1_checked, root8Node36Step1Chunk8_2_checked, root8Node36Step1Chunk8_3_checked, root8Node36Step1Chunk8_4_checked, root8Node36Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node36Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,0),(4,2),(7,0),(8,0)]
  | 1 => [(7,3),(8,3)]
  | 2 => [(5,2),(5,5),(8,2)]
  | 3 => [(7,0),(8,0)]
  | 4 => [(1,2),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 5 => [(0,1),(1,4)]
  | 6 => [(0,5),(6,2)]
  | 7 => [(4,4),(8,4)]
  | 8 => [(1,4),(6,4)]
  | 9 => [(0,3),(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 10 => [(7,5),(8,5)]
  | 11 => [(1,0),(6,0)]
  | 12 => [(7,1)]
  | 13 => [(7,5)]
  | 14 => [(0,3),(6,0)]
  | 15 => [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 16 => [(1,3),(3,3),(7,3)]
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
def root8Node36Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(4,2),(7,0),(8,0)]
  | 1 => some [(7,3),(8,3)]
  | 2 => some [(5,2),(5,5),(8,2)]
  | 3 => some [(7,0),(8,0)]
  | 4 => some [(1,2),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 5 => some [(0,1),(1,4)]
  | 6 => some [(0,5),(6,2)]
  | 7 => some [(4,4),(8,4)]
  | 8 => some [(1,4),(6,4)]
  | 9 => some [(0,3),(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 10 => some [(7,5),(8,5)]
  | 11 => some [(1,0),(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3),(6,0)]
  | 15 => some [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 16 => some [(1,3),(3,3),(7,3)]
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
theorem root8Node36Domains2_fast_eq : root8Node36Domains2 = expandDomains root8Node36Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node36Domains2 v = expandDomains root8Node36Domains2Fast v from by decide) v
theorem root8Node36Step2Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root8Node36Domains1 root8Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains1 root8Node36Domains2
    root8Node36Domains1Fast root8Node36Domains2Fast
    root8Node36Domains1_fast_eq root8Node36Domains2_fast_eq (by decide)
theorem root8Node36Step2_checked :
    checkReplacement table26 root8Node36Domains1 root8Node36Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node36Step2Chunk0_0_checked, root8Node36Step2Chunk0_1_checked, root8Node36Step2Chunk0_2_checked, root8Node36Step2Chunk0_3_checked, root8Node36Step2Chunk0_4_checked, root8Node36Step2Chunk0_5_checked, root8Node36Step2Chunk1_0_checked, root8Node36Step2Chunk1_1_checked, root8Node36Step2Chunk1_2_checked, root8Node36Step2Chunk1_3_checked, root8Node36Step2Chunk1_4_checked, root8Node36Step2Chunk1_5_checked, root8Node36Step2Chunk2_0_checked, root8Node36Step2Chunk2_1_checked, root8Node36Step2Chunk2_2_checked, root8Node36Step2Chunk2_3_checked, root8Node36Step2Chunk2_4_checked, root8Node36Step2Chunk2_5_checked, root8Node36Step2Chunk3_0_checked, root8Node36Step2Chunk3_1_checked, root8Node36Step2Chunk3_2_checked, root8Node36Step2Chunk3_3_checked, root8Node36Step2Chunk3_4_checked, root8Node36Step2Chunk3_5_checked, root8Node36Step2Chunk4_0_checked, root8Node36Step2Chunk4_1_checked, root8Node36Step2Chunk4_2_checked, root8Node36Step2Chunk4_3_checked, root8Node36Step2Chunk4_4_checked, root8Node36Step2Chunk4_5_checked, root8Node36Step2Chunk5_0_checked, root8Node36Step2Chunk5_1_checked, root8Node36Step2Chunk5_2_checked, root8Node36Step2Chunk5_3_checked, root8Node36Step2Chunk5_4_checked, root8Node36Step2Chunk5_5_checked, root8Node36Step2Chunk6_0_checked, root8Node36Step2Chunk6_1_checked, root8Node36Step2Chunk6_2_checked, root8Node36Step2Chunk6_3_checked, root8Node36Step2Chunk6_4_checked, root8Node36Step2Chunk6_5_checked, root8Node36Step2Chunk7_0_checked, root8Node36Step2Chunk7_1_checked, root8Node36Step2Chunk7_2_checked, root8Node36Step2Chunk7_3_checked, root8Node36Step2Chunk7_4_checked, root8Node36Step2Chunk7_5_checked, root8Node36Step2Chunk8_0_checked, root8Node36Step2Chunk8_1_checked, root8Node36Step2Chunk8_2_checked, root8Node36Step2Chunk8_3_checked, root8Node36Step2Chunk8_4_checked, root8Node36Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node36Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,0),(7,0),(8,0)]
  | 1 => [(7,3),(8,3)]
  | 2 => [(5,2),(5,5),(8,2)]
  | 3 => [(7,0),(8,0)]
  | 4 => [(4,4),(5,1),(5,4),(8,4)]
  | 5 => [(0,1),(1,4)]
  | 6 => [(0,5),(6,2)]
  | 7 => [(4,4),(8,4)]
  | 8 => [(1,4),(6,4)]
  | 9 => [(4,3),(5,3),(7,1),(8,3)]
  | 10 => [(7,5),(8,5)]
  | 11 => [(1,0),(6,0)]
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
def root8Node36Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(7,0),(8,0)]
  | 1 => some [(7,3),(8,3)]
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
theorem root8Node36Domains3_fast_eq : root8Node36Domains3 = expandDomains root8Node36Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node36Domains3 v = expandDomains root8Node36Domains3Fast v from by decide) v
theorem root8Node36Step3Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root8Node36Domains2 root8Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node36Domains2 root8Node36Domains3
    root8Node36Domains2Fast root8Node36Domains3Fast
    root8Node36Domains2_fast_eq root8Node36Domains3_fast_eq (by decide)
theorem root8Node36Step3_checked :
    checkReplacement table4 root8Node36Domains2 root8Node36Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node36Step3Chunk0_0_checked, root8Node36Step3Chunk0_1_checked, root8Node36Step3Chunk0_2_checked, root8Node36Step3Chunk0_3_checked, root8Node36Step3Chunk0_4_checked, root8Node36Step3Chunk0_5_checked, root8Node36Step3Chunk1_0_checked, root8Node36Step3Chunk1_1_checked, root8Node36Step3Chunk1_2_checked, root8Node36Step3Chunk1_3_checked, root8Node36Step3Chunk1_4_checked, root8Node36Step3Chunk1_5_checked, root8Node36Step3Chunk2_0_checked, root8Node36Step3Chunk2_1_checked, root8Node36Step3Chunk2_2_checked, root8Node36Step3Chunk2_3_checked, root8Node36Step3Chunk2_4_checked, root8Node36Step3Chunk2_5_checked, root8Node36Step3Chunk3_0_checked, root8Node36Step3Chunk3_1_checked, root8Node36Step3Chunk3_2_checked, root8Node36Step3Chunk3_3_checked, root8Node36Step3Chunk3_4_checked, root8Node36Step3Chunk3_5_checked, root8Node36Step3Chunk4_0_checked, root8Node36Step3Chunk4_1_checked, root8Node36Step3Chunk4_2_checked, root8Node36Step3Chunk4_3_checked, root8Node36Step3Chunk4_4_checked, root8Node36Step3Chunk4_5_checked, root8Node36Step3Chunk5_0_checked, root8Node36Step3Chunk5_1_checked, root8Node36Step3Chunk5_2_checked, root8Node36Step3Chunk5_3_checked, root8Node36Step3Chunk5_4_checked, root8Node36Step3Chunk5_5_checked, root8Node36Step3Chunk6_0_checked, root8Node36Step3Chunk6_1_checked, root8Node36Step3Chunk6_2_checked, root8Node36Step3Chunk6_3_checked, root8Node36Step3Chunk6_4_checked, root8Node36Step3Chunk6_5_checked, root8Node36Step3Chunk7_0_checked, root8Node36Step3Chunk7_1_checked, root8Node36Step3Chunk7_2_checked, root8Node36Step3Chunk7_3_checked, root8Node36Step3Chunk7_4_checked, root8Node36Step3Chunk7_5_checked, root8Node36Step3Chunk8_0_checked, root8Node36Step3Chunk8_1_checked, root8Node36Step3Chunk8_2_checked, root8Node36Step3Chunk8_3_checked, root8Node36Step3Chunk8_4_checked, root8Node36Step3Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
