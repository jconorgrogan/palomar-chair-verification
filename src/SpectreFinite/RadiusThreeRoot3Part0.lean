module

public import SpectreFinite.RadiusThreeRoot3Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable12
public import SpectreFinite.RadiusThreeTable24
public import SpectreFinite.RadiusThreeTable26

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root3Node0Domains0 : Domains 37 State := domains (3,0)
def root3Node0Domains0Fast (v : Fin 37) : Option (List State) :=
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
  | 18 => some [(3,0)]
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
theorem root3Node0Domains0_fast_eq : root3Node0Domains0 = expandDomains root3Node0Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root3Node0Domains0 v = expandDomains root3Node0Domains0Fast v from by decide) v
def root3Node0Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => [(4,3)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => stateChoices
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(4,2)]
  | 8 => [(5,3)]
  | 9 => stateChoices
  | 10 => [(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => stateChoices
  | 16 => stateChoices
  | 17 => [(5,5)]
  | 18 => [(3,0)]
  | 19 => [(2,5)]
  | 20 => [(6,0)]
  | 21 => stateChoices
  | 22 => stateChoices
  | 23 => stateChoices
  | 24 => [(4,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
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
def root3Node0Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => none
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => none
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(4,2)]
  | 8 => some [(5,3)]
  | 9 => none
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => none
  | 16 => none
  | 17 => some [(5,5)]
  | 18 => some [(3,0)]
  | 19 => some [(2,5)]
  | 20 => some [(6,0)]
  | 21 => none
  | 22 => none
  | 23 => none
  | 24 => some [(4,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
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
theorem root3Node0Domains1_fast_eq : root3Node0Domains1 = expandDomains root3Node0Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root3Node0Domains1 v = expandDomains root3Node0Domains1Fast v from by decide) v
theorem root3Node0Step1Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1_checked :
    checkReplacement table12 root3Node0Domains0 root3Node0Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root3Node0Step1Chunk0_0_checked, root3Node0Step1Chunk0_1_checked, root3Node0Step1Chunk0_2_checked, root3Node0Step1Chunk0_3_checked, root3Node0Step1Chunk0_4_checked, root3Node0Step1Chunk0_5_checked, root3Node0Step1Chunk1_0_checked, root3Node0Step1Chunk1_1_checked, root3Node0Step1Chunk1_2_checked, root3Node0Step1Chunk1_3_checked, root3Node0Step1Chunk1_4_checked, root3Node0Step1Chunk1_5_checked, root3Node0Step1Chunk2_0_checked, root3Node0Step1Chunk2_1_checked, root3Node0Step1Chunk2_2_checked, root3Node0Step1Chunk2_3_checked, root3Node0Step1Chunk2_4_checked, root3Node0Step1Chunk2_5_checked, root3Node0Step1Chunk3_0_checked, root3Node0Step1Chunk3_1_checked, root3Node0Step1Chunk3_2_checked, root3Node0Step1Chunk3_3_checked, root3Node0Step1Chunk3_4_checked, root3Node0Step1Chunk3_5_checked, root3Node0Step1Chunk4_0_checked, root3Node0Step1Chunk4_1_checked, root3Node0Step1Chunk4_2_checked, root3Node0Step1Chunk4_3_checked, root3Node0Step1Chunk4_4_checked, root3Node0Step1Chunk4_5_checked, root3Node0Step1Chunk5_0_checked, root3Node0Step1Chunk5_1_checked, root3Node0Step1Chunk5_2_checked, root3Node0Step1Chunk5_3_checked, root3Node0Step1Chunk5_4_checked, root3Node0Step1Chunk5_5_checked, root3Node0Step1Chunk6_0_checked, root3Node0Step1Chunk6_1_checked, root3Node0Step1Chunk6_2_checked, root3Node0Step1Chunk6_3_checked, root3Node0Step1Chunk6_4_checked, root3Node0Step1Chunk6_5_checked, root3Node0Step1Chunk7_0_checked, root3Node0Step1Chunk7_1_checked, root3Node0Step1Chunk7_2_checked, root3Node0Step1Chunk7_3_checked, root3Node0Step1Chunk7_4_checked, root3Node0Step1Chunk7_5_checked, root3Node0Step1Chunk8_0_checked, root3Node0Step1Chunk8_1_checked, root3Node0Step1Chunk8_2_checked, root3Node0Step1Chunk8_3_checked, root3Node0Step1Chunk8_4_checked, root3Node0Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root3Node0Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => [(4,3)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => stateChoices
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(4,2)]
  | 8 => [(5,3)]
  | 9 => stateChoices
  | 10 => [(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => stateChoices
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(3,0)]
  | 19 => [(2,5)]
  | 20 => [(6,0)]
  | 21 => stateChoices
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(4,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => stateChoices
  | 28 => [(6,0)]
  | 29 => [(7,1)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => stateChoices
  | 33 => [(5,0)]
  | 34 => [(4,5)]
  | 35 => [(7,0)]
  | _ => stateChoices
def root3Node0Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => none
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => none
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(4,2)]
  | 8 => some [(5,3)]
  | 9 => none
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => none
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(3,0)]
  | 19 => some [(2,5)]
  | 20 => some [(6,0)]
  | 21 => none
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => none
  | 28 => some [(6,0)]
  | 29 => some [(7,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => none
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(7,0)]
  | _ => none
theorem root3Node0Domains2_fast_eq : root3Node0Domains2 = expandDomains root3Node0Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root3Node0Domains2 v = expandDomains root3Node0Domains2Fast v from by decide) v
theorem root3Node0Step2Chunk0_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk0_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk0_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk0_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk0_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk0_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk1_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk1_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk1_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk1_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk1_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk1_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk2_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk2_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk2_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk2_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk2_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk2_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk3_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk3_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk3_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk3_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk3_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk3_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk4_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk4_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk4_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk4_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk4_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk4_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk5_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk5_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk5_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk5_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk5_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk5_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk6_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk6_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk6_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk6_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk6_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk6_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk7_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk7_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk7_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk7_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk7_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk7_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk8_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk8_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk8_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk8_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk8_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk8_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2_checked :
    checkReplacement table24 root3Node0Domains1 root3Node0Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root3Node0Step2Chunk0_0_checked, root3Node0Step2Chunk0_1_checked, root3Node0Step2Chunk0_2_checked, root3Node0Step2Chunk0_3_checked, root3Node0Step2Chunk0_4_checked, root3Node0Step2Chunk0_5_checked, root3Node0Step2Chunk1_0_checked, root3Node0Step2Chunk1_1_checked, root3Node0Step2Chunk1_2_checked, root3Node0Step2Chunk1_3_checked, root3Node0Step2Chunk1_4_checked, root3Node0Step2Chunk1_5_checked, root3Node0Step2Chunk2_0_checked, root3Node0Step2Chunk2_1_checked, root3Node0Step2Chunk2_2_checked, root3Node0Step2Chunk2_3_checked, root3Node0Step2Chunk2_4_checked, root3Node0Step2Chunk2_5_checked, root3Node0Step2Chunk3_0_checked, root3Node0Step2Chunk3_1_checked, root3Node0Step2Chunk3_2_checked, root3Node0Step2Chunk3_3_checked, root3Node0Step2Chunk3_4_checked, root3Node0Step2Chunk3_5_checked, root3Node0Step2Chunk4_0_checked, root3Node0Step2Chunk4_1_checked, root3Node0Step2Chunk4_2_checked, root3Node0Step2Chunk4_3_checked, root3Node0Step2Chunk4_4_checked, root3Node0Step2Chunk4_5_checked, root3Node0Step2Chunk5_0_checked, root3Node0Step2Chunk5_1_checked, root3Node0Step2Chunk5_2_checked, root3Node0Step2Chunk5_3_checked, root3Node0Step2Chunk5_4_checked, root3Node0Step2Chunk5_5_checked, root3Node0Step2Chunk6_0_checked, root3Node0Step2Chunk6_1_checked, root3Node0Step2Chunk6_2_checked, root3Node0Step2Chunk6_3_checked, root3Node0Step2Chunk6_4_checked, root3Node0Step2Chunk6_5_checked, root3Node0Step2Chunk7_0_checked, root3Node0Step2Chunk7_1_checked, root3Node0Step2Chunk7_2_checked, root3Node0Step2Chunk7_3_checked, root3Node0Step2Chunk7_4_checked, root3Node0Step2Chunk7_5_checked, root3Node0Step2Chunk8_0_checked, root3Node0Step2Chunk8_1_checked, root3Node0Step2Chunk8_2_checked, root3Node0Step2Chunk8_3_checked, root3Node0Step2Chunk8_4_checked, root3Node0Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root3Node0Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => [(4,3)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => stateChoices
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(4,2)]
  | 8 => [(5,3)]
  | 9 => stateChoices
  | 10 => [(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => stateChoices
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(3,0)]
  | 19 => [(2,5)]
  | 20 => [(6,0)]
  | 21 => [(7,1)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(4,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(6,0)]
  | 29 => [(7,1)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(5,1)]
  | 33 => [(5,0)]
  | 34 => [(4,5)]
  | 35 => [(7,0)]
  | _ => [(8,3)]
def root3Node0Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => none
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => none
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(4,2)]
  | 8 => some [(5,3)]
  | 9 => none
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => none
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(3,0)]
  | 19 => some [(2,5)]
  | 20 => some [(6,0)]
  | 21 => some [(7,1)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(6,0)]
  | 29 => some [(7,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(5,1)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root3Node0Domains3_fast_eq : root3Node0Domains3 = expandDomains root3Node0Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root3Node0Domains3 v = expandDomains root3Node0Domains3Fast v from by decide) v
theorem root3Node0Step3Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3_checked :
    checkReplacement table26 root3Node0Domains2 root3Node0Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root3Node0Step3Chunk0_0_checked, root3Node0Step3Chunk0_1_checked, root3Node0Step3Chunk0_2_checked, root3Node0Step3Chunk0_3_checked, root3Node0Step3Chunk0_4_checked, root3Node0Step3Chunk0_5_checked, root3Node0Step3Chunk1_0_checked, root3Node0Step3Chunk1_1_checked, root3Node0Step3Chunk1_2_checked, root3Node0Step3Chunk1_3_checked, root3Node0Step3Chunk1_4_checked, root3Node0Step3Chunk1_5_checked, root3Node0Step3Chunk2_0_checked, root3Node0Step3Chunk2_1_checked, root3Node0Step3Chunk2_2_checked, root3Node0Step3Chunk2_3_checked, root3Node0Step3Chunk2_4_checked, root3Node0Step3Chunk2_5_checked, root3Node0Step3Chunk3_0_checked, root3Node0Step3Chunk3_1_checked, root3Node0Step3Chunk3_2_checked, root3Node0Step3Chunk3_3_checked, root3Node0Step3Chunk3_4_checked, root3Node0Step3Chunk3_5_checked, root3Node0Step3Chunk4_0_checked, root3Node0Step3Chunk4_1_checked, root3Node0Step3Chunk4_2_checked, root3Node0Step3Chunk4_3_checked, root3Node0Step3Chunk4_4_checked, root3Node0Step3Chunk4_5_checked, root3Node0Step3Chunk5_0_checked, root3Node0Step3Chunk5_1_checked, root3Node0Step3Chunk5_2_checked, root3Node0Step3Chunk5_3_checked, root3Node0Step3Chunk5_4_checked, root3Node0Step3Chunk5_5_checked, root3Node0Step3Chunk6_0_checked, root3Node0Step3Chunk6_1_checked, root3Node0Step3Chunk6_2_checked, root3Node0Step3Chunk6_3_checked, root3Node0Step3Chunk6_4_checked, root3Node0Step3Chunk6_5_checked, root3Node0Step3Chunk7_0_checked, root3Node0Step3Chunk7_1_checked, root3Node0Step3Chunk7_2_checked, root3Node0Step3Chunk7_3_checked, root3Node0Step3Chunk7_4_checked, root3Node0Step3Chunk7_5_checked, root3Node0Step3Chunk8_0_checked, root3Node0Step3Chunk8_1_checked, root3Node0Step3Chunk8_2_checked, root3Node0Step3Chunk8_3_checked, root3Node0Step3Chunk8_4_checked, root3Node0Step3Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
