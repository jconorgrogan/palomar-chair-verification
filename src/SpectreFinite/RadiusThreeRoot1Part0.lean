module

public import SpectreFinite.RadiusThreeRoot1Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable12
public import SpectreFinite.RadiusThreeTable23
public import SpectreFinite.RadiusThreeTable26

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node0Domains0 : Domains 37 State := domains (1,0)
def root1Node0Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => none
  | 1 => none
  | 2 => none
  | 3 => none
  | 4 => none
  | 5 => none
  | 6 => none
  | 7 => none
  | 8 => none
  | 9 => none
  | 10 => none
  | 11 => none
  | 12 => none
  | 13 => none
  | 14 => none
  | 15 => none
  | 16 => none
  | 17 => none
  | 18 => some [(1,0)]
  | 19 => none
  | 20 => none
  | 21 => none
  | 22 => none
  | 23 => none
  | 24 => none
  | 25 => none
  | 26 => none
  | 27 => none
  | 28 => none
  | 29 => none
  | 30 => none
  | 31 => none
  | 32 => none
  | 33 => none
  | 34 => none
  | 35 => none
  | _ => none
theorem root1Node0Domains0_fast_eq : root1Node0Domains0 = expandDomains root1Node0Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node0Domains0 v = expandDomains root1Node0Domains0Fast v from by decide) v
def root1Node0Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => [(0,3),(1,1),(6,1),(7,1)]
  | 2 => [(4,1),(7,5)]
  | 3 => [(0,2),(0,3),(6,0)]
  | 4 => stateChoices
  | 5 => [(2,0),(2,2),(4,0)]
  | 6 => [(3,3),(7,3)]
  | 7 => [(4,2),(5,2),(8,2)]
  | 8 => [(5,0),(5,3),(8,0)]
  | 9 => stateChoices
  | 10 => [(1,1),(3,1),(5,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(7,4),(8,4)]
  | 14 => [(0,0),(1,3),(1,4),(6,3),(6,4)]
  | 15 => stateChoices
  | 16 => stateChoices
  | 17 => [(4,5),(5,5),(8,5)]
  | 18 => [(1,0)]
  | 19 => [(2,1),(7,1)]
  | 20 => [(0,2),(1,5),(6,5),(7,5)]
  | 21 => stateChoices
  | 22 => stateChoices
  | 23 => stateChoices
  | 24 => [(4,4),(7,2),(8,2)]
  | 25 => [(0,0),(4,0),(5,0),(8,0)]
  | 26 => [(3,2),(4,5),(7,3)]
  | 27 => stateChoices
  | 28 => stateChoices
  | 29 => stateChoices
  | 30 => stateChoices
  | 31 => stateChoices
  | 32 => stateChoices
  | 33 => stateChoices
  | 34 => stateChoices
  | 35 => stateChoices
  | _ => stateChoices
def root1Node0Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => none
  | 1 => some [(0,3),(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(7,5)]
  | 3 => some [(0,2),(0,3),(6,0)]
  | 4 => none
  | 5 => some [(2,0),(2,2),(4,0)]
  | 6 => some [(3,3),(7,3)]
  | 7 => some [(4,2),(5,2),(8,2)]
  | 8 => some [(5,0),(5,3),(8,0)]
  | 9 => none
  | 10 => some [(1,1),(3,1),(5,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(7,4),(8,4)]
  | 14 => some [(0,0),(1,3),(1,4),(6,3),(6,4)]
  | 15 => none
  | 16 => none
  | 17 => some [(4,5),(5,5),(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(2,1),(7,1)]
  | 20 => some [(0,2),(1,5),(6,5),(7,5)]
  | 21 => none
  | 22 => none
  | 23 => none
  | 24 => some [(4,4),(7,2),(8,2)]
  | 25 => some [(0,0),(4,0),(5,0),(8,0)]
  | 26 => some [(3,2),(4,5),(7,3)]
  | 27 => none
  | 28 => none
  | 29 => none
  | 30 => none
  | 31 => none
  | 32 => none
  | 33 => none
  | 34 => none
  | 35 => none
  | _ => none
theorem root1Node0Domains1_fast_eq : root1Node0Domains1 = expandDomains root1Node0Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node0Domains1 v = expandDomains root1Node0Domains1Fast v from by decide) v
theorem root1Node0Step1Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root1Node0Domains0 root1Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains0 root1Node0Domains1
    root1Node0Domains0Fast root1Node0Domains1Fast
    root1Node0Domains0_fast_eq root1Node0Domains1_fast_eq (by decide)
theorem root1Node0Step1_checked :
    checkReplacement table12 root1Node0Domains0 root1Node0Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node0Step1Chunk0_0_checked, root1Node0Step1Chunk0_1_checked, root1Node0Step1Chunk0_2_checked, root1Node0Step1Chunk0_3_checked, root1Node0Step1Chunk0_4_checked, root1Node0Step1Chunk0_5_checked, root1Node0Step1Chunk1_0_checked, root1Node0Step1Chunk1_1_checked, root1Node0Step1Chunk1_2_checked, root1Node0Step1Chunk1_3_checked, root1Node0Step1Chunk1_4_checked, root1Node0Step1Chunk1_5_checked, root1Node0Step1Chunk2_0_checked, root1Node0Step1Chunk2_1_checked, root1Node0Step1Chunk2_2_checked, root1Node0Step1Chunk2_3_checked, root1Node0Step1Chunk2_4_checked, root1Node0Step1Chunk2_5_checked, root1Node0Step1Chunk3_0_checked, root1Node0Step1Chunk3_1_checked, root1Node0Step1Chunk3_2_checked, root1Node0Step1Chunk3_3_checked, root1Node0Step1Chunk3_4_checked, root1Node0Step1Chunk3_5_checked, root1Node0Step1Chunk4_0_checked, root1Node0Step1Chunk4_1_checked, root1Node0Step1Chunk4_2_checked, root1Node0Step1Chunk4_3_checked, root1Node0Step1Chunk4_4_checked, root1Node0Step1Chunk4_5_checked, root1Node0Step1Chunk5_0_checked, root1Node0Step1Chunk5_1_checked, root1Node0Step1Chunk5_2_checked, root1Node0Step1Chunk5_3_checked, root1Node0Step1Chunk5_4_checked, root1Node0Step1Chunk5_5_checked, root1Node0Step1Chunk6_0_checked, root1Node0Step1Chunk6_1_checked, root1Node0Step1Chunk6_2_checked, root1Node0Step1Chunk6_3_checked, root1Node0Step1Chunk6_4_checked, root1Node0Step1Chunk6_5_checked, root1Node0Step1Chunk7_0_checked, root1Node0Step1Chunk7_1_checked, root1Node0Step1Chunk7_2_checked, root1Node0Step1Chunk7_3_checked, root1Node0Step1Chunk7_4_checked, root1Node0Step1Chunk7_5_checked, root1Node0Step1Chunk8_0_checked, root1Node0Step1Chunk8_1_checked, root1Node0Step1Chunk8_2_checked, root1Node0Step1Chunk8_3_checked, root1Node0Step1Chunk8_4_checked, root1Node0Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node0Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => [(0,3),(1,1),(6,1),(7,1)]
  | 2 => [(4,1),(7,5)]
  | 3 => [(0,2),(0,3),(6,0)]
  | 4 => stateChoices
  | 5 => [(2,0),(2,2),(4,0)]
  | 6 => [(3,3),(7,3)]
  | 7 => [(4,2),(5,2),(8,2)]
  | 8 => [(5,0),(5,3),(8,0)]
  | 9 => [(0,2),(0,3),(1,1),(6,0),(6,1)]
  | 10 => [(1,1),(3,1),(5,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(7,4),(8,4)]
  | 14 => [(0,0),(1,3),(1,4),(6,3),(6,4)]
  | 15 => [(4,2),(5,2),(7,0),(8,0),(8,2)]
  | 16 => [(5,0),(5,3),(8,3)]
  | 17 => [(4,5),(5,5),(8,5)]
  | 18 => [(1,0)]
  | 19 => [(2,1),(7,1)]
  | 20 => [(0,2),(1,5),(6,5),(7,5)]
  | 21 => stateChoices
  | 22 => [(1,4),(7,4),(8,4)]
  | 23 => [(0,0),(0,5),(1,3),(6,3)]
  | 24 => [(4,4),(7,2),(8,2)]
  | 25 => [(0,0),(4,0),(5,0),(8,0)]
  | 26 => [(3,2),(4,5),(7,3)]
  | 27 => stateChoices
  | 28 => [(0,2),(1,5),(6,0),(6,5)]
  | 29 => [(0,4),(1,1),(6,1),(7,1)]
  | 30 => [(1,5),(5,1),(5,4)]
  | 31 => stateChoices
  | 32 => stateChoices
  | 33 => [(5,0),(7,0),(8,0)]
  | 34 => [(4,3),(4,5),(8,3)]
  | 35 => stateChoices
  | _ => stateChoices
def root1Node0Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => none
  | 1 => some [(0,3),(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(7,5)]
  | 3 => some [(0,2),(0,3),(6,0)]
  | 4 => none
  | 5 => some [(2,0),(2,2),(4,0)]
  | 6 => some [(3,3),(7,3)]
  | 7 => some [(4,2),(5,2),(8,2)]
  | 8 => some [(5,0),(5,3),(8,0)]
  | 9 => some [(0,2),(0,3),(1,1),(6,0),(6,1)]
  | 10 => some [(1,1),(3,1),(5,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(7,4),(8,4)]
  | 14 => some [(0,0),(1,3),(1,4),(6,3),(6,4)]
  | 15 => some [(4,2),(5,2),(7,0),(8,0),(8,2)]
  | 16 => some [(5,0),(5,3),(8,3)]
  | 17 => some [(4,5),(5,5),(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(2,1),(7,1)]
  | 20 => some [(0,2),(1,5),(6,5),(7,5)]
  | 21 => none
  | 22 => some [(1,4),(7,4),(8,4)]
  | 23 => some [(0,0),(0,5),(1,3),(6,3)]
  | 24 => some [(4,4),(7,2),(8,2)]
  | 25 => some [(0,0),(4,0),(5,0),(8,0)]
  | 26 => some [(3,2),(4,5),(7,3)]
  | 27 => none
  | 28 => some [(0,2),(1,5),(6,0),(6,5)]
  | 29 => some [(0,4),(1,1),(6,1),(7,1)]
  | 30 => some [(1,5),(5,1),(5,4)]
  | 31 => none
  | 32 => none
  | 33 => some [(5,0),(7,0),(8,0)]
  | 34 => some [(4,3),(4,5),(8,3)]
  | 35 => none
  | _ => none
theorem root1Node0Domains2_fast_eq : root1Node0Domains2 = expandDomains root1Node0Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node0Domains2 v = expandDomains root1Node0Domains2Fast v from by decide) v
theorem root1Node0Step2Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root1Node0Domains1 root1Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains1 root1Node0Domains2
    root1Node0Domains1Fast root1Node0Domains2Fast
    root1Node0Domains1_fast_eq root1Node0Domains2_fast_eq (by decide)
theorem root1Node0Step2_checked :
    checkReplacement table23 root1Node0Domains1 root1Node0Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node0Step2Chunk0_0_checked, root1Node0Step2Chunk0_1_checked, root1Node0Step2Chunk0_2_checked, root1Node0Step2Chunk0_3_checked, root1Node0Step2Chunk0_4_checked, root1Node0Step2Chunk0_5_checked, root1Node0Step2Chunk1_0_checked, root1Node0Step2Chunk1_1_checked, root1Node0Step2Chunk1_2_checked, root1Node0Step2Chunk1_3_checked, root1Node0Step2Chunk1_4_checked, root1Node0Step2Chunk1_5_checked, root1Node0Step2Chunk2_0_checked, root1Node0Step2Chunk2_1_checked, root1Node0Step2Chunk2_2_checked, root1Node0Step2Chunk2_3_checked, root1Node0Step2Chunk2_4_checked, root1Node0Step2Chunk2_5_checked, root1Node0Step2Chunk3_0_checked, root1Node0Step2Chunk3_1_checked, root1Node0Step2Chunk3_2_checked, root1Node0Step2Chunk3_3_checked, root1Node0Step2Chunk3_4_checked, root1Node0Step2Chunk3_5_checked, root1Node0Step2Chunk4_0_checked, root1Node0Step2Chunk4_1_checked, root1Node0Step2Chunk4_2_checked, root1Node0Step2Chunk4_3_checked, root1Node0Step2Chunk4_4_checked, root1Node0Step2Chunk4_5_checked, root1Node0Step2Chunk5_0_checked, root1Node0Step2Chunk5_1_checked, root1Node0Step2Chunk5_2_checked, root1Node0Step2Chunk5_3_checked, root1Node0Step2Chunk5_4_checked, root1Node0Step2Chunk5_5_checked, root1Node0Step2Chunk6_0_checked, root1Node0Step2Chunk6_1_checked, root1Node0Step2Chunk6_2_checked, root1Node0Step2Chunk6_3_checked, root1Node0Step2Chunk6_4_checked, root1Node0Step2Chunk6_5_checked, root1Node0Step2Chunk7_0_checked, root1Node0Step2Chunk7_1_checked, root1Node0Step2Chunk7_2_checked, root1Node0Step2Chunk7_3_checked, root1Node0Step2Chunk7_4_checked, root1Node0Step2Chunk7_5_checked, root1Node0Step2Chunk8_0_checked, root1Node0Step2Chunk8_1_checked, root1Node0Step2Chunk8_2_checked, root1Node0Step2Chunk8_3_checked, root1Node0Step2Chunk8_4_checked, root1Node0Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node0Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => [(0,3),(1,1),(6,1),(7,1)]
  | 2 => [(4,1),(7,5)]
  | 3 => [(0,2),(0,3),(6,0)]
  | 4 => stateChoices
  | 5 => [(2,0),(2,2),(4,0)]
  | 6 => [(3,3),(7,3)]
  | 7 => [(4,2),(5,2),(8,2)]
  | 8 => [(5,0),(5,3),(8,0)]
  | 9 => [(0,2),(0,3),(1,1),(6,0),(6,1)]
  | 10 => [(1,1),(3,1),(5,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(7,4),(8,4)]
  | 14 => [(0,0),(1,3),(1,4),(6,3),(6,4)]
  | 15 => [(4,2),(5,2),(7,0),(8,0),(8,2)]
  | 16 => [(5,0),(5,3),(8,3)]
  | 17 => [(4,5),(5,5),(8,5)]
  | 18 => [(1,0)]
  | 19 => [(2,1),(7,1)]
  | 20 => [(0,2),(1,5),(6,5),(7,5)]
  | 21 => [(0,3),(0,4),(1,1),(6,0),(6,1)]
  | 22 => [(1,4),(7,4),(8,4)]
  | 23 => [(0,0),(0,5),(1,3),(6,3)]
  | 24 => [(4,4),(7,2),(8,2)]
  | 25 => [(0,0),(4,0),(5,0),(8,0)]
  | 26 => [(3,2),(4,5),(7,3)]
  | 27 => [(4,0),(4,2),(7,0),(8,2)]
  | 28 => [(0,2),(1,5),(6,0),(6,5)]
  | 29 => [(0,4),(1,1),(6,1),(7,1)]
  | 30 => [(1,5),(5,1),(5,4)]
  | 31 => [(0,0),(0,1),(6,1),(6,4)]
  | 32 => [(1,2),(5,1),(6,2),(7,2)]
  | 33 => [(5,0),(7,0),(8,0)]
  | 34 => [(4,3),(4,5),(8,3)]
  | 35 => [(1,5),(3,5),(5,5),(7,0),(7,5),(8,5)]
  | _ => [(0,3),(1,0),(6,1),(8,3)]
def root1Node0Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => none
  | 1 => some [(0,3),(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(7,5)]
  | 3 => some [(0,2),(0,3),(6,0)]
  | 4 => none
  | 5 => some [(2,0),(2,2),(4,0)]
  | 6 => some [(3,3),(7,3)]
  | 7 => some [(4,2),(5,2),(8,2)]
  | 8 => some [(5,0),(5,3),(8,0)]
  | 9 => some [(0,2),(0,3),(1,1),(6,0),(6,1)]
  | 10 => some [(1,1),(3,1),(5,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(7,4),(8,4)]
  | 14 => some [(0,0),(1,3),(1,4),(6,3),(6,4)]
  | 15 => some [(4,2),(5,2),(7,0),(8,0),(8,2)]
  | 16 => some [(5,0),(5,3),(8,3)]
  | 17 => some [(4,5),(5,5),(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(2,1),(7,1)]
  | 20 => some [(0,2),(1,5),(6,5),(7,5)]
  | 21 => some [(0,3),(0,4),(1,1),(6,0),(6,1)]
  | 22 => some [(1,4),(7,4),(8,4)]
  | 23 => some [(0,0),(0,5),(1,3),(6,3)]
  | 24 => some [(4,4),(7,2),(8,2)]
  | 25 => some [(0,0),(4,0),(5,0),(8,0)]
  | 26 => some [(3,2),(4,5),(7,3)]
  | 27 => some [(4,0),(4,2),(7,0),(8,2)]
  | 28 => some [(0,2),(1,5),(6,0),(6,5)]
  | 29 => some [(0,4),(1,1),(6,1),(7,1)]
  | 30 => some [(1,5),(5,1),(5,4)]
  | 31 => some [(0,0),(0,1),(6,1),(6,4)]
  | 32 => some [(1,2),(5,1),(6,2),(7,2)]
  | 33 => some [(5,0),(7,0),(8,0)]
  | 34 => some [(4,3),(4,5),(8,3)]
  | 35 => some [(1,5),(3,5),(5,5),(7,0),(7,5),(8,5)]
  | _ => some [(0,3),(1,0),(6,1),(8,3)]
theorem root1Node0Domains3_fast_eq : root1Node0Domains3 = expandDomains root1Node0Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node0Domains3 v = expandDomains root1Node0Domains3Fast v from by decide) v
theorem root1Node0Step3Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root1Node0Domains2 root1Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node0Domains2 root1Node0Domains3
    root1Node0Domains2Fast root1Node0Domains3Fast
    root1Node0Domains2_fast_eq root1Node0Domains3_fast_eq (by decide)
theorem root1Node0Step3_checked :
    checkReplacement table26 root1Node0Domains2 root1Node0Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node0Step3Chunk0_0_checked, root1Node0Step3Chunk0_1_checked, root1Node0Step3Chunk0_2_checked, root1Node0Step3Chunk0_3_checked, root1Node0Step3Chunk0_4_checked, root1Node0Step3Chunk0_5_checked, root1Node0Step3Chunk1_0_checked, root1Node0Step3Chunk1_1_checked, root1Node0Step3Chunk1_2_checked, root1Node0Step3Chunk1_3_checked, root1Node0Step3Chunk1_4_checked, root1Node0Step3Chunk1_5_checked, root1Node0Step3Chunk2_0_checked, root1Node0Step3Chunk2_1_checked, root1Node0Step3Chunk2_2_checked, root1Node0Step3Chunk2_3_checked, root1Node0Step3Chunk2_4_checked, root1Node0Step3Chunk2_5_checked, root1Node0Step3Chunk3_0_checked, root1Node0Step3Chunk3_1_checked, root1Node0Step3Chunk3_2_checked, root1Node0Step3Chunk3_3_checked, root1Node0Step3Chunk3_4_checked, root1Node0Step3Chunk3_5_checked, root1Node0Step3Chunk4_0_checked, root1Node0Step3Chunk4_1_checked, root1Node0Step3Chunk4_2_checked, root1Node0Step3Chunk4_3_checked, root1Node0Step3Chunk4_4_checked, root1Node0Step3Chunk4_5_checked, root1Node0Step3Chunk5_0_checked, root1Node0Step3Chunk5_1_checked, root1Node0Step3Chunk5_2_checked, root1Node0Step3Chunk5_3_checked, root1Node0Step3Chunk5_4_checked, root1Node0Step3Chunk5_5_checked, root1Node0Step3Chunk6_0_checked, root1Node0Step3Chunk6_1_checked, root1Node0Step3Chunk6_2_checked, root1Node0Step3Chunk6_3_checked, root1Node0Step3Chunk6_4_checked, root1Node0Step3Chunk6_5_checked, root1Node0Step3Chunk7_0_checked, root1Node0Step3Chunk7_1_checked, root1Node0Step3Chunk7_2_checked, root1Node0Step3Chunk7_3_checked, root1Node0Step3Chunk7_4_checked, root1Node0Step3Chunk7_5_checked, root1Node0Step3Chunk8_0_checked, root1Node0Step3Chunk8_1_checked, root1Node0Step3Chunk8_2_checked, root1Node0Step3Chunk8_3_checked, root1Node0Step3Chunk8_4_checked, root1Node0Step3Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
