module

public import SpectreFinite.RadiusThreeRoot0Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable10
public import SpectreFinite.RadiusThreeTable25
public import SpectreFinite.RadiusThreeTable8

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node0Domains0 : Domains 37 State := domains (0,0)
def root0Node0Domains0Fast (v : Fin 37) : Option (List State) :=
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
  | 18 => some [(0,0)]
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
theorem root0Node0Domains0_fast_eq : root0Node0Domains0 = expandDomains root0Node0Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node0Domains0 v = expandDomains root0Node0Domains0Fast v from by decide) v
def root0Node0Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => stateChoices
  | 2 => stateChoices
  | 3 => stateChoices
  | 4 => stateChoices
  | 5 => stateChoices
  | 6 => stateChoices
  | 7 => stateChoices
  | 8 => stateChoices
  | 9 => stateChoices
  | 10 => stateChoices
  | 11 => [(1,0),(3,0),(5,0)]
  | 12 => [(2,1),(2,5),(4,5)]
  | 13 => [(0,2),(1,0),(6,0),(7,0)]
  | 14 => stateChoices
  | 15 => stateChoices
  | 16 => stateChoices
  | 17 => [(4,4),(5,4),(8,4)]
  | 18 => [(0,0)]
  | 19 => [(3,2),(7,2)]
  | 20 => [(4,0),(7,4)]
  | 21 => stateChoices
  | 22 => stateChoices
  | 23 => [(4,3),(7,1),(8,1)]
  | 24 => [(1,5)]
  | 25 => [(6,1)]
  | 26 => [(4,1),(5,1),(8,1)]
  | 27 => [(0,1),(0,2),(6,5)]
  | 28 => stateChoices
  | 29 => [(0,5),(4,5),(5,5),(8,5)]
  | 30 => [(2,0),(7,0)]
  | 31 => [(7,3),(8,3)]
  | 32 => [(5,2),(5,5),(8,5)]
  | 33 => stateChoices
  | 34 => [(3,1),(4,4),(7,2)]
  | 35 => [(0,1),(1,4),(6,4),(7,4)]
  | _ => [(0,5),(1,2),(1,3),(6,2),(6,3)]
def root0Node0Domains1Fast (v : Fin 37) : Option (List State) :=
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
  | 11 => some [(1,0),(3,0),(5,0)]
  | 12 => some [(2,1),(2,5),(4,5)]
  | 13 => some [(0,2),(1,0),(6,0),(7,0)]
  | 14 => none
  | 15 => none
  | 16 => none
  | 17 => some [(4,4),(5,4),(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(3,2),(7,2)]
  | 20 => some [(4,0),(7,4)]
  | 21 => none
  | 22 => none
  | 23 => some [(4,3),(7,1),(8,1)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(4,1),(5,1),(8,1)]
  | 27 => some [(0,1),(0,2),(6,5)]
  | 28 => none
  | 29 => some [(0,5),(4,5),(5,5),(8,5)]
  | 30 => some [(2,0),(7,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5),(8,5)]
  | 33 => none
  | 34 => some [(3,1),(4,4),(7,2)]
  | 35 => some [(0,1),(1,4),(6,4),(7,4)]
  | _ => some [(0,5),(1,2),(1,3),(6,2),(6,3)]
theorem root0Node0Domains1_fast_eq : root0Node0Domains1 = expandDomains root0Node0Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node0Domains1 v = expandDomains root0Node0Domains1Fast v from by decide) v
theorem root0Node0Step1Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root0Node0Domains0 root0Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains0 root0Node0Domains1
    root0Node0Domains0Fast root0Node0Domains1Fast
    root0Node0Domains0_fast_eq root0Node0Domains1_fast_eq (by decide)
theorem root0Node0Step1_checked :
    checkReplacement table25 root0Node0Domains0 root0Node0Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node0Step1Chunk0_0_checked, root0Node0Step1Chunk0_1_checked, root0Node0Step1Chunk0_2_checked, root0Node0Step1Chunk0_3_checked, root0Node0Step1Chunk0_4_checked, root0Node0Step1Chunk0_5_checked, root0Node0Step1Chunk1_0_checked, root0Node0Step1Chunk1_1_checked, root0Node0Step1Chunk1_2_checked, root0Node0Step1Chunk1_3_checked, root0Node0Step1Chunk1_4_checked, root0Node0Step1Chunk1_5_checked, root0Node0Step1Chunk2_0_checked, root0Node0Step1Chunk2_1_checked, root0Node0Step1Chunk2_2_checked, root0Node0Step1Chunk2_3_checked, root0Node0Step1Chunk2_4_checked, root0Node0Step1Chunk2_5_checked, root0Node0Step1Chunk3_0_checked, root0Node0Step1Chunk3_1_checked, root0Node0Step1Chunk3_2_checked, root0Node0Step1Chunk3_3_checked, root0Node0Step1Chunk3_4_checked, root0Node0Step1Chunk3_5_checked, root0Node0Step1Chunk4_0_checked, root0Node0Step1Chunk4_1_checked, root0Node0Step1Chunk4_2_checked, root0Node0Step1Chunk4_3_checked, root0Node0Step1Chunk4_4_checked, root0Node0Step1Chunk4_5_checked, root0Node0Step1Chunk5_0_checked, root0Node0Step1Chunk5_1_checked, root0Node0Step1Chunk5_2_checked, root0Node0Step1Chunk5_3_checked, root0Node0Step1Chunk5_4_checked, root0Node0Step1Chunk5_5_checked, root0Node0Step1Chunk6_0_checked, root0Node0Step1Chunk6_1_checked, root0Node0Step1Chunk6_2_checked, root0Node0Step1Chunk6_3_checked, root0Node0Step1Chunk6_4_checked, root0Node0Step1Chunk6_5_checked, root0Node0Step1Chunk7_0_checked, root0Node0Step1Chunk7_1_checked, root0Node0Step1Chunk7_2_checked, root0Node0Step1Chunk7_3_checked, root0Node0Step1Chunk7_4_checked, root0Node0Step1Chunk7_5_checked, root0Node0Step1Chunk8_0_checked, root0Node0Step1Chunk8_1_checked, root0Node0Step1Chunk8_2_checked, root0Node0Step1Chunk8_3_checked, root0Node0Step1Chunk8_4_checked, root0Node0Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node0Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(4,0),(7,4)]
  | 1 => [(0,5),(1,3),(6,2),(6,3),(7,3)]
  | 2 => stateChoices
  | 3 => stateChoices
  | 4 => [(4,1),(5,1),(7,5),(8,1),(8,5)]
  | 5 => [(0,1),(0,2),(1,0),(6,0),(6,5)]
  | 6 => [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 7 => stateChoices
  | 8 => stateChoices
  | 9 => [(1,3),(7,3),(8,3)]
  | 10 => [(5,2),(5,5),(8,2)]
  | 11 => [(1,0),(3,0),(5,0)]
  | 12 => [(2,1),(2,5),(4,5)]
  | 13 => [(0,2),(1,0),(6,0),(7,0)]
  | 14 => stateChoices
  | 15 => [(0,1),(1,4),(6,4),(6,5)]
  | 16 => [(0,4),(0,5),(1,2),(6,2)]
  | 17 => [(4,4),(5,4),(8,4)]
  | 18 => [(0,0)]
  | 19 => [(3,2),(7,2)]
  | 20 => [(4,0),(7,4)]
  | 21 => stateChoices
  | 22 => [(0,3),(1,0),(6,0),(7,0)]
  | 23 => [(4,3),(7,1),(8,1)]
  | 24 => [(1,5)]
  | 25 => [(6,1)]
  | 26 => [(4,1),(5,1),(8,1)]
  | 27 => [(0,1),(0,2),(6,5)]
  | 28 => stateChoices
  | 29 => [(0,5),(4,5),(5,5),(8,5)]
  | 30 => [(2,0),(7,0)]
  | 31 => [(7,3),(8,3)]
  | 32 => [(5,2),(5,5),(8,5)]
  | 33 => stateChoices
  | 34 => [(3,1),(4,4),(7,2)]
  | 35 => [(0,1),(1,4),(6,4),(7,4)]
  | _ => [(0,5),(1,2),(1,3),(6,2),(6,3)]
def root0Node0Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(4,0),(7,4)]
  | 1 => some [(0,5),(1,3),(6,2),(6,3),(7,3)]
  | 2 => none
  | 3 => none
  | 4 => some [(4,1),(5,1),(7,5),(8,1),(8,5)]
  | 5 => some [(0,1),(0,2),(1,0),(6,0),(6,5)]
  | 6 => some [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 7 => none
  | 8 => none
  | 9 => some [(1,3),(7,3),(8,3)]
  | 10 => some [(5,2),(5,5),(8,2)]
  | 11 => some [(1,0),(3,0),(5,0)]
  | 12 => some [(2,1),(2,5),(4,5)]
  | 13 => some [(0,2),(1,0),(6,0),(7,0)]
  | 14 => none
  | 15 => some [(0,1),(1,4),(6,4),(6,5)]
  | 16 => some [(0,4),(0,5),(1,2),(6,2)]
  | 17 => some [(4,4),(5,4),(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(3,2),(7,2)]
  | 20 => some [(4,0),(7,4)]
  | 21 => none
  | 22 => some [(0,3),(1,0),(6,0),(7,0)]
  | 23 => some [(4,3),(7,1),(8,1)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(4,1),(5,1),(8,1)]
  | 27 => some [(0,1),(0,2),(6,5)]
  | 28 => none
  | 29 => some [(0,5),(4,5),(5,5),(8,5)]
  | 30 => some [(2,0),(7,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5),(8,5)]
  | 33 => none
  | 34 => some [(3,1),(4,4),(7,2)]
  | 35 => some [(0,1),(1,4),(6,4),(7,4)]
  | _ => some [(0,5),(1,2),(1,3),(6,2),(6,3)]
theorem root0Node0Domains2_fast_eq : root0Node0Domains2 = expandDomains root0Node0Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node0Domains2 v = expandDomains root0Node0Domains2Fast v from by decide) v
theorem root0Node0Step2Chunk0_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_0⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk0_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_1⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk0_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_2⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk0_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_3⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk0_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_4⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk0_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_5⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk1_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_0⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk1_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_1⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk1_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_2⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk1_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_3⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk1_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_4⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk1_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_5⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk2_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_0⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk2_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_1⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk2_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_2⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk2_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_3⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk2_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_4⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk2_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_5⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk3_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_0⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk3_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_1⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk3_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_2⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk3_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_3⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk3_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_4⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk3_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_5⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk4_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_0⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk4_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_1⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk4_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_2⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk4_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_3⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk4_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_4⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk4_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_5⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk5_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_0⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk5_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_1⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk5_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_2⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk5_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_3⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk5_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_4⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk5_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_5⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk6_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_0⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk6_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_1⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk6_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_2⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk6_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_3⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk6_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_4⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk6_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_5⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk7_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_0⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk7_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_1⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk7_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_2⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk7_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_3⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk7_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_4⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk7_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_5⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk8_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_0⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk8_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_1⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk8_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_2⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk8_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_3⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk8_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_4⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2Chunk8_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_5⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains1 root0Node0Domains2
    root0Node0Domains1Fast root0Node0Domains2Fast
    root0Node0Domains1_fast_eq root0Node0Domains2_fast_eq (by decide)
theorem root0Node0Step2_checked :
    checkReplacement table10 root0Node0Domains1 root0Node0Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node0Step2Chunk0_0_checked, root0Node0Step2Chunk0_1_checked, root0Node0Step2Chunk0_2_checked, root0Node0Step2Chunk0_3_checked, root0Node0Step2Chunk0_4_checked, root0Node0Step2Chunk0_5_checked, root0Node0Step2Chunk1_0_checked, root0Node0Step2Chunk1_1_checked, root0Node0Step2Chunk1_2_checked, root0Node0Step2Chunk1_3_checked, root0Node0Step2Chunk1_4_checked, root0Node0Step2Chunk1_5_checked, root0Node0Step2Chunk2_0_checked, root0Node0Step2Chunk2_1_checked, root0Node0Step2Chunk2_2_checked, root0Node0Step2Chunk2_3_checked, root0Node0Step2Chunk2_4_checked, root0Node0Step2Chunk2_5_checked, root0Node0Step2Chunk3_0_checked, root0Node0Step2Chunk3_1_checked, root0Node0Step2Chunk3_2_checked, root0Node0Step2Chunk3_3_checked, root0Node0Step2Chunk3_4_checked, root0Node0Step2Chunk3_5_checked, root0Node0Step2Chunk4_0_checked, root0Node0Step2Chunk4_1_checked, root0Node0Step2Chunk4_2_checked, root0Node0Step2Chunk4_3_checked, root0Node0Step2Chunk4_4_checked, root0Node0Step2Chunk4_5_checked, root0Node0Step2Chunk5_0_checked, root0Node0Step2Chunk5_1_checked, root0Node0Step2Chunk5_2_checked, root0Node0Step2Chunk5_3_checked, root0Node0Step2Chunk5_4_checked, root0Node0Step2Chunk5_5_checked, root0Node0Step2Chunk6_0_checked, root0Node0Step2Chunk6_1_checked, root0Node0Step2Chunk6_2_checked, root0Node0Step2Chunk6_3_checked, root0Node0Step2Chunk6_4_checked, root0Node0Step2Chunk6_5_checked, root0Node0Step2Chunk7_0_checked, root0Node0Step2Chunk7_1_checked, root0Node0Step2Chunk7_2_checked, root0Node0Step2Chunk7_3_checked, root0Node0Step2Chunk7_4_checked, root0Node0Step2Chunk7_5_checked, root0Node0Step2Chunk8_0_checked, root0Node0Step2Chunk8_1_checked, root0Node0Step2Chunk8_2_checked, root0Node0Step2Chunk8_3_checked, root0Node0Step2Chunk8_4_checked, root0Node0Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node0Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(4,0),(7,4)]
  | 1 => [(0,5),(1,3),(6,2),(6,3),(7,3)]
  | 2 => [(2,0),(2,2),(2,4),(4,2),(4,4),(7,4),(8,4)]
  | 3 => [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 4 => [(4,1),(5,1),(7,5),(8,1),(8,5)]
  | 5 => [(0,1),(0,2),(1,0),(6,0),(6,5)]
  | 6 => [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 7 => [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 8 => [(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 9 => [(1,3),(7,3),(8,3)]
  | 10 => [(5,2),(5,5),(8,2)]
  | 11 => [(1,0),(3,0),(5,0)]
  | 12 => [(2,1),(2,5),(4,5)]
  | 13 => [(0,2),(1,0),(6,0),(7,0)]
  | 14 => [(1,1),(4,3),(7,1),(8,3)]
  | 15 => [(0,1),(1,4),(6,4),(6,5)]
  | 16 => [(0,4),(0,5),(1,2),(6,2)]
  | 17 => [(4,4),(5,4),(8,4)]
  | 18 => [(0,0)]
  | 19 => [(3,2),(7,2)]
  | 20 => [(4,0),(7,4)]
  | 21 => [(1,3),(6,3),(7,3)]
  | 22 => [(0,3),(1,0),(6,0),(7,0)]
  | 23 => [(4,3),(7,1),(8,1)]
  | 24 => [(1,5)]
  | 25 => [(6,1)]
  | 26 => [(4,1),(5,1),(8,1)]
  | 27 => [(0,1),(0,2),(6,5)]
  | 28 => stateChoices
  | 29 => [(0,5),(4,5),(5,5),(8,5)]
  | 30 => [(2,0),(7,0)]
  | 31 => [(7,3),(8,3)]
  | 32 => [(5,2),(5,5),(8,5)]
  | 33 => stateChoices
  | 34 => [(3,1),(4,4),(7,2)]
  | 35 => [(0,1),(1,4),(6,4),(7,4)]
  | _ => [(0,5),(1,2),(1,3),(6,2),(6,3)]
def root0Node0Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(4,0),(7,4)]
  | 1 => some [(0,5),(1,3),(6,2),(6,3),(7,3)]
  | 2 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(7,4),(8,4)]
  | 3 => some [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 4 => some [(4,1),(5,1),(7,5),(8,1),(8,5)]
  | 5 => some [(0,1),(0,2),(1,0),(6,0),(6,5)]
  | 6 => some [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 7 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 8 => some [(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 9 => some [(1,3),(7,3),(8,3)]
  | 10 => some [(5,2),(5,5),(8,2)]
  | 11 => some [(1,0),(3,0),(5,0)]
  | 12 => some [(2,1),(2,5),(4,5)]
  | 13 => some [(0,2),(1,0),(6,0),(7,0)]
  | 14 => some [(1,1),(4,3),(7,1),(8,3)]
  | 15 => some [(0,1),(1,4),(6,4),(6,5)]
  | 16 => some [(0,4),(0,5),(1,2),(6,2)]
  | 17 => some [(4,4),(5,4),(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(3,2),(7,2)]
  | 20 => some [(4,0),(7,4)]
  | 21 => some [(1,3),(6,3),(7,3)]
  | 22 => some [(0,3),(1,0),(6,0),(7,0)]
  | 23 => some [(4,3),(7,1),(8,1)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(4,1),(5,1),(8,1)]
  | 27 => some [(0,1),(0,2),(6,5)]
  | 28 => none
  | 29 => some [(0,5),(4,5),(5,5),(8,5)]
  | 30 => some [(2,0),(7,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5),(8,5)]
  | 33 => none
  | 34 => some [(3,1),(4,4),(7,2)]
  | 35 => some [(0,1),(1,4),(6,4),(7,4)]
  | _ => some [(0,5),(1,2),(1,3),(6,2),(6,3)]
theorem root0Node0Domains3_fast_eq : root0Node0Domains3 = expandDomains root0Node0Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node0Domains3 v = expandDomains root0Node0Domains3Fast v from by decide) v
theorem root0Node0Step3Chunk0_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_0⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk0_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_1⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk0_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_2⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk0_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_3⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk0_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_4⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk0_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_5⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk1_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_0⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk1_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_1⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk1_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_2⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk1_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_3⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk1_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_4⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk1_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_5⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk2_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_0⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk2_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_1⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk2_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_2⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk2_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_3⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk2_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_4⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk2_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_5⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk3_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_0⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk3_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_1⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk3_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_2⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk3_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_3⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk3_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_4⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk3_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_5⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk4_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_0⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk4_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_1⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk4_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_2⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk4_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_3⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk4_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_4⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk4_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_5⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk5_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_0⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk5_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_1⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk5_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_2⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk5_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_3⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk5_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_4⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk5_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_5⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk6_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_0⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk6_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_1⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk6_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_2⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk6_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_3⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk6_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_4⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk6_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_5⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk7_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_0⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk7_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_1⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk7_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_2⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk7_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_3⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk7_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_4⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk7_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_5⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk8_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_0⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk8_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_1⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk8_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_2⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk8_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_3⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk8_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_4⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3Chunk8_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_5⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains2 root0Node0Domains3
    root0Node0Domains2Fast root0Node0Domains3Fast
    root0Node0Domains2_fast_eq root0Node0Domains3_fast_eq (by decide)
theorem root0Node0Step3_checked :
    checkReplacement table8 root0Node0Domains2 root0Node0Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node0Step3Chunk0_0_checked, root0Node0Step3Chunk0_1_checked, root0Node0Step3Chunk0_2_checked, root0Node0Step3Chunk0_3_checked, root0Node0Step3Chunk0_4_checked, root0Node0Step3Chunk0_5_checked, root0Node0Step3Chunk1_0_checked, root0Node0Step3Chunk1_1_checked, root0Node0Step3Chunk1_2_checked, root0Node0Step3Chunk1_3_checked, root0Node0Step3Chunk1_4_checked, root0Node0Step3Chunk1_5_checked, root0Node0Step3Chunk2_0_checked, root0Node0Step3Chunk2_1_checked, root0Node0Step3Chunk2_2_checked, root0Node0Step3Chunk2_3_checked, root0Node0Step3Chunk2_4_checked, root0Node0Step3Chunk2_5_checked, root0Node0Step3Chunk3_0_checked, root0Node0Step3Chunk3_1_checked, root0Node0Step3Chunk3_2_checked, root0Node0Step3Chunk3_3_checked, root0Node0Step3Chunk3_4_checked, root0Node0Step3Chunk3_5_checked, root0Node0Step3Chunk4_0_checked, root0Node0Step3Chunk4_1_checked, root0Node0Step3Chunk4_2_checked, root0Node0Step3Chunk4_3_checked, root0Node0Step3Chunk4_4_checked, root0Node0Step3Chunk4_5_checked, root0Node0Step3Chunk5_0_checked, root0Node0Step3Chunk5_1_checked, root0Node0Step3Chunk5_2_checked, root0Node0Step3Chunk5_3_checked, root0Node0Step3Chunk5_4_checked, root0Node0Step3Chunk5_5_checked, root0Node0Step3Chunk6_0_checked, root0Node0Step3Chunk6_1_checked, root0Node0Step3Chunk6_2_checked, root0Node0Step3Chunk6_3_checked, root0Node0Step3Chunk6_4_checked, root0Node0Step3Chunk6_5_checked, root0Node0Step3Chunk7_0_checked, root0Node0Step3Chunk7_1_checked, root0Node0Step3Chunk7_2_checked, root0Node0Step3Chunk7_3_checked, root0Node0Step3Chunk7_4_checked, root0Node0Step3Chunk7_5_checked, root0Node0Step3Chunk8_0_checked, root0Node0Step3Chunk8_1_checked, root0Node0Step3Chunk8_2_checked, root0Node0Step3Chunk8_3_checked, root0Node0Step3Chunk8_4_checked, root0Node0Step3Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
