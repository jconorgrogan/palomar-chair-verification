module

public import SpectreFinite.RadiusThreeRoot2Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable11
public import SpectreFinite.RadiusThreeTable13
public import SpectreFinite.RadiusThreeTable25

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root2Node0Domains0 : Domains 37 State := domains (2,0)
def root2Node0Domains0Fast (v : Fin 37) : Option (List State) :=
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
  | 18 => some [(2,0)]
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
theorem root2Node0Domains0_fast_eq : root2Node0Domains0 = expandDomains root2Node0Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root2Node0Domains0 v = expandDomains root2Node0Domains0Fast v from by decide) v
def root2Node0Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(5,0)]
  | 2 => [(4,5)]
  | 3 => stateChoices
  | 4 => [(0,4)]
  | 5 => [(5,4)]
  | 6 => [(0,0)]
  | 7 => [(7,2)]
  | 8 => stateChoices
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(1,5)]
  | 12 => [(6,1)]
  | 13 => [(4,1)]
  | 14 => stateChoices
  | 15 => stateChoices
  | 16 => [(1,4)]
  | 17 => [(0,5)]
  | 18 => [(2,0)]
  | 19 => [(7,3)]
  | 20 => stateChoices
  | 21 => stateChoices
  | 22 => stateChoices
  | 23 => [(6,0)]
  | 24 => [(3,1)]
  | 25 => [(0,1)]
  | 26 => stateChoices
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
def root2Node0Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => none
  | 4 => some [(0,4)]
  | 5 => some [(5,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => none
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(4,1)]
  | 14 => none
  | 15 => none
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(2,0)]
  | 19 => some [(7,3)]
  | 20 => none
  | 21 => none
  | 22 => none
  | 23 => some [(6,0)]
  | 24 => some [(3,1)]
  | 25 => some [(0,1)]
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
theorem root2Node0Domains1_fast_eq : root2Node0Domains1 = expandDomains root2Node0Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root2Node0Domains1 v = expandDomains root2Node0Domains1Fast v from by decide) v
theorem root2Node0Step1Chunk0_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk0_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk0_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk0_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk0_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk0_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk1_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk1_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk1_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk1_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk1_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk1_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk2_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk2_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk2_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk2_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk2_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk2_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk3_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk3_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk3_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk3_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk3_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk3_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk4_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk4_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk4_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk4_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk4_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk4_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk5_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk5_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk5_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk5_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk5_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk5_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk6_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk6_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk6_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk6_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk6_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk6_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk7_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk7_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk7_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk7_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk7_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk7_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk8_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk8_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk8_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk8_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk8_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk8_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1_checked :
    checkReplacement table11 root2Node0Domains0 root2Node0Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root2Node0Step1Chunk0_0_checked, root2Node0Step1Chunk0_1_checked, root2Node0Step1Chunk0_2_checked, root2Node0Step1Chunk0_3_checked, root2Node0Step1Chunk0_4_checked, root2Node0Step1Chunk0_5_checked, root2Node0Step1Chunk1_0_checked, root2Node0Step1Chunk1_1_checked, root2Node0Step1Chunk1_2_checked, root2Node0Step1Chunk1_3_checked, root2Node0Step1Chunk1_4_checked, root2Node0Step1Chunk1_5_checked, root2Node0Step1Chunk2_0_checked, root2Node0Step1Chunk2_1_checked, root2Node0Step1Chunk2_2_checked, root2Node0Step1Chunk2_3_checked, root2Node0Step1Chunk2_4_checked, root2Node0Step1Chunk2_5_checked, root2Node0Step1Chunk3_0_checked, root2Node0Step1Chunk3_1_checked, root2Node0Step1Chunk3_2_checked, root2Node0Step1Chunk3_3_checked, root2Node0Step1Chunk3_4_checked, root2Node0Step1Chunk3_5_checked, root2Node0Step1Chunk4_0_checked, root2Node0Step1Chunk4_1_checked, root2Node0Step1Chunk4_2_checked, root2Node0Step1Chunk4_3_checked, root2Node0Step1Chunk4_4_checked, root2Node0Step1Chunk4_5_checked, root2Node0Step1Chunk5_0_checked, root2Node0Step1Chunk5_1_checked, root2Node0Step1Chunk5_2_checked, root2Node0Step1Chunk5_3_checked, root2Node0Step1Chunk5_4_checked, root2Node0Step1Chunk5_5_checked, root2Node0Step1Chunk6_0_checked, root2Node0Step1Chunk6_1_checked, root2Node0Step1Chunk6_2_checked, root2Node0Step1Chunk6_3_checked, root2Node0Step1Chunk6_4_checked, root2Node0Step1Chunk6_5_checked, root2Node0Step1Chunk7_0_checked, root2Node0Step1Chunk7_1_checked, root2Node0Step1Chunk7_2_checked, root2Node0Step1Chunk7_3_checked, root2Node0Step1Chunk7_4_checked, root2Node0Step1Chunk7_5_checked, root2Node0Step1Chunk8_0_checked, root2Node0Step1Chunk8_1_checked, root2Node0Step1Chunk8_2_checked, root2Node0Step1Chunk8_3_checked, root2Node0Step1Chunk8_4_checked, root2Node0Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root2Node0Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(5,0)]
  | 2 => [(4,5)]
  | 3 => stateChoices
  | 4 => [(0,4)]
  | 5 => [(5,4)]
  | 6 => [(0,0)]
  | 7 => [(7,2)]
  | 8 => stateChoices
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(1,5)]
  | 12 => [(6,1)]
  | 13 => [(4,1)]
  | 14 => stateChoices
  | 15 => stateChoices
  | 16 => [(1,4)]
  | 17 => [(0,5)]
  | 18 => [(2,0)]
  | 19 => [(7,3)]
  | 20 => [(5,2)]
  | 21 => stateChoices
  | 22 => stateChoices
  | 23 => [(6,0)]
  | 24 => [(3,1)]
  | 25 => [(0,1)]
  | 26 => [(6,2)]
  | 27 => [(8,4)]
  | 28 => stateChoices
  | 29 => [(5,0)]
  | 30 => [(4,5)]
  | 31 => [(1,0)]
  | 32 => [(7,1)]
  | 33 => stateChoices
  | 34 => [(0,0)]
  | 35 => [(7,2)]
  | _ => [(4,0)]
def root2Node0Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => none
  | 4 => some [(0,4)]
  | 5 => some [(5,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => none
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(4,1)]
  | 14 => none
  | 15 => none
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(2,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => none
  | 22 => none
  | 23 => some [(6,0)]
  | 24 => some [(3,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(8,4)]
  | 28 => none
  | 29 => some [(5,0)]
  | 30 => some [(4,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => none
  | 34 => some [(0,0)]
  | 35 => some [(7,2)]
  | _ => some [(4,0)]
theorem root2Node0Domains2_fast_eq : root2Node0Domains2 = expandDomains root2Node0Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root2Node0Domains2 v = expandDomains root2Node0Domains2Fast v from by decide) v
theorem root2Node0Step2Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2_checked :
    checkReplacement table25 root2Node0Domains1 root2Node0Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root2Node0Step2Chunk0_0_checked, root2Node0Step2Chunk0_1_checked, root2Node0Step2Chunk0_2_checked, root2Node0Step2Chunk0_3_checked, root2Node0Step2Chunk0_4_checked, root2Node0Step2Chunk0_5_checked, root2Node0Step2Chunk1_0_checked, root2Node0Step2Chunk1_1_checked, root2Node0Step2Chunk1_2_checked, root2Node0Step2Chunk1_3_checked, root2Node0Step2Chunk1_4_checked, root2Node0Step2Chunk1_5_checked, root2Node0Step2Chunk2_0_checked, root2Node0Step2Chunk2_1_checked, root2Node0Step2Chunk2_2_checked, root2Node0Step2Chunk2_3_checked, root2Node0Step2Chunk2_4_checked, root2Node0Step2Chunk2_5_checked, root2Node0Step2Chunk3_0_checked, root2Node0Step2Chunk3_1_checked, root2Node0Step2Chunk3_2_checked, root2Node0Step2Chunk3_3_checked, root2Node0Step2Chunk3_4_checked, root2Node0Step2Chunk3_5_checked, root2Node0Step2Chunk4_0_checked, root2Node0Step2Chunk4_1_checked, root2Node0Step2Chunk4_2_checked, root2Node0Step2Chunk4_3_checked, root2Node0Step2Chunk4_4_checked, root2Node0Step2Chunk4_5_checked, root2Node0Step2Chunk5_0_checked, root2Node0Step2Chunk5_1_checked, root2Node0Step2Chunk5_2_checked, root2Node0Step2Chunk5_3_checked, root2Node0Step2Chunk5_4_checked, root2Node0Step2Chunk5_5_checked, root2Node0Step2Chunk6_0_checked, root2Node0Step2Chunk6_1_checked, root2Node0Step2Chunk6_2_checked, root2Node0Step2Chunk6_3_checked, root2Node0Step2Chunk6_4_checked, root2Node0Step2Chunk6_5_checked, root2Node0Step2Chunk7_0_checked, root2Node0Step2Chunk7_1_checked, root2Node0Step2Chunk7_2_checked, root2Node0Step2Chunk7_3_checked, root2Node0Step2Chunk7_4_checked, root2Node0Step2Chunk7_5_checked, root2Node0Step2Chunk8_0_checked, root2Node0Step2Chunk8_1_checked, root2Node0Step2Chunk8_2_checked, root2Node0Step2Chunk8_3_checked, root2Node0Step2Chunk8_4_checked, root2Node0Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root2Node0Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(5,0)]
  | 2 => [(4,5)]
  | 3 => [(7,0)]
  | 4 => [(0,4)]
  | 5 => [(5,4)]
  | 6 => [(0,0)]
  | 7 => [(7,2)]
  | 8 => [(7,4)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(1,5)]
  | 12 => [(6,1)]
  | 13 => [(4,1)]
  | 14 => [(0,2)]
  | 15 => stateChoices
  | 16 => [(1,4)]
  | 17 => [(0,5)]
  | 18 => [(2,0)]
  | 19 => [(7,3)]
  | 20 => [(5,2)]
  | 21 => [(8,0)]
  | 22 => stateChoices
  | 23 => [(6,0)]
  | 24 => [(3,1)]
  | 25 => [(0,1)]
  | 26 => [(6,2)]
  | 27 => [(8,4)]
  | 28 => stateChoices
  | 29 => [(5,0)]
  | 30 => [(4,5)]
  | 31 => [(1,0)]
  | 32 => [(7,1)]
  | 33 => stateChoices
  | 34 => [(0,0)]
  | 35 => [(7,2)]
  | _ => [(4,0)]
def root2Node0Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(0,4)]
  | 5 => some [(5,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(4,1)]
  | 14 => some [(0,2)]
  | 15 => none
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(2,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(8,0)]
  | 22 => none
  | 23 => some [(6,0)]
  | 24 => some [(3,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(8,4)]
  | 28 => none
  | 29 => some [(5,0)]
  | 30 => some [(4,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => none
  | 34 => some [(0,0)]
  | 35 => some [(7,2)]
  | _ => some [(4,0)]
theorem root2Node0Domains3_fast_eq : root2Node0Domains3 = expandDomains root2Node0Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root2Node0Domains3 v = expandDomains root2Node0Domains3Fast v from by decide) v
theorem root2Node0Step3Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3_checked :
    checkReplacement table13 root2Node0Domains2 root2Node0Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root2Node0Step3Chunk0_0_checked, root2Node0Step3Chunk0_1_checked, root2Node0Step3Chunk0_2_checked, root2Node0Step3Chunk0_3_checked, root2Node0Step3Chunk0_4_checked, root2Node0Step3Chunk0_5_checked, root2Node0Step3Chunk1_0_checked, root2Node0Step3Chunk1_1_checked, root2Node0Step3Chunk1_2_checked, root2Node0Step3Chunk1_3_checked, root2Node0Step3Chunk1_4_checked, root2Node0Step3Chunk1_5_checked, root2Node0Step3Chunk2_0_checked, root2Node0Step3Chunk2_1_checked, root2Node0Step3Chunk2_2_checked, root2Node0Step3Chunk2_3_checked, root2Node0Step3Chunk2_4_checked, root2Node0Step3Chunk2_5_checked, root2Node0Step3Chunk3_0_checked, root2Node0Step3Chunk3_1_checked, root2Node0Step3Chunk3_2_checked, root2Node0Step3Chunk3_3_checked, root2Node0Step3Chunk3_4_checked, root2Node0Step3Chunk3_5_checked, root2Node0Step3Chunk4_0_checked, root2Node0Step3Chunk4_1_checked, root2Node0Step3Chunk4_2_checked, root2Node0Step3Chunk4_3_checked, root2Node0Step3Chunk4_4_checked, root2Node0Step3Chunk4_5_checked, root2Node0Step3Chunk5_0_checked, root2Node0Step3Chunk5_1_checked, root2Node0Step3Chunk5_2_checked, root2Node0Step3Chunk5_3_checked, root2Node0Step3Chunk5_4_checked, root2Node0Step3Chunk5_5_checked, root2Node0Step3Chunk6_0_checked, root2Node0Step3Chunk6_1_checked, root2Node0Step3Chunk6_2_checked, root2Node0Step3Chunk6_3_checked, root2Node0Step3Chunk6_4_checked, root2Node0Step3Chunk6_5_checked, root2Node0Step3Chunk7_0_checked, root2Node0Step3Chunk7_1_checked, root2Node0Step3Chunk7_2_checked, root2Node0Step3Chunk7_3_checked, root2Node0Step3Chunk7_4_checked, root2Node0Step3Chunk7_5_checked, root2Node0Step3Chunk8_0_checked, root2Node0Step3Chunk8_1_checked, root2Node0Step3Chunk8_2_checked, root2Node0Step3Chunk8_3_checked, root2Node0Step3Chunk8_4_checked, root2Node0Step3Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
