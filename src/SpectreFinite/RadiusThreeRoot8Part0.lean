module

public import SpectreFinite.RadiusThreeRoot8Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable13
public import SpectreFinite.RadiusThreeTable18
public import SpectreFinite.RadiusThreeTable23

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node0Domains0 : Domains 37 State := domains (8,0)
def root8Node0Domains0Fast (v : Fin 37) : Option (List State) :=
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
  | 18 => some [(8,0)]
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
theorem root8Node0Domains0_fast_eq : root8Node0Domains0 = expandDomains root8Node0Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node0Domains0 v = expandDomains root8Node0Domains0Fast v from by decide) v
def root8Node0Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => stateChoices
  | 2 => stateChoices
  | 3 => stateChoices
  | 4 => stateChoices
  | 5 => [(0,1),(1,4),(7,4)]
  | 6 => [(0,5),(6,2),(6,3)]
  | 7 => [(4,4),(7,2),(8,4)]
  | 8 => stateChoices
  | 9 => stateChoices
  | 10 => [(4,1),(7,5),(8,5)]
  | 11 => [(0,2),(1,0),(6,0)]
  | 12 => [(1,1),(7,1)]
  | 13 => [(4,1),(5,1),(7,5),(8,1)]
  | 14 => stateChoices
  | 15 => stateChoices
  | 16 => [(1,3),(3,3),(7,3)]
  | 17 => [(5,2),(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(4,2),(5,2),(5,5),(8,2)]
  | 21 => stateChoices
  | 22 => stateChoices
  | 23 => [(0,4),(6,2)]
  | 24 => [(5,4),(8,4)]
  | 25 => [(1,4),(6,4)]
  | 26 => [(0,5),(1,2)]
  | 27 => stateChoices
  | 28 => stateChoices
  | 29 => [(4,3),(7,1)]
  | 30 => [(3,5),(7,5)]
  | 31 => [(0,3),(6,0)]
  | 32 => stateChoices
  | 33 => stateChoices
  | 34 => stateChoices
  | 35 => stateChoices
  | _ => stateChoices
def root8Node0Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => none
  | 1 => none
  | 2 => none
  | 3 => none
  | 4 => none
  | 5 => some [(0,1),(1,4),(7,4)]
  | 6 => some [(0,5),(6,2),(6,3)]
  | 7 => some [(4,4),(7,2),(8,4)]
  | 8 => none
  | 9 => none
  | 10 => some [(4,1),(7,5),(8,5)]
  | 11 => some [(0,2),(1,0),(6,0)]
  | 12 => some [(1,1),(7,1)]
  | 13 => some [(4,1),(5,1),(7,5),(8,1)]
  | 14 => none
  | 15 => none
  | 16 => some [(1,3),(3,3),(7,3)]
  | 17 => some [(5,2),(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(4,2),(5,2),(5,5),(8,2)]
  | 21 => none
  | 22 => none
  | 23 => some [(0,4),(6,2)]
  | 24 => some [(5,4),(8,4)]
  | 25 => some [(1,4),(6,4)]
  | 26 => some [(0,5),(1,2)]
  | 27 => none
  | 28 => none
  | 29 => some [(4,3),(7,1)]
  | 30 => some [(3,5),(7,5)]
  | 31 => some [(0,3),(6,0)]
  | 32 => none
  | 33 => none
  | 34 => none
  | 35 => none
  | _ => none
theorem root8Node0Domains1_fast_eq : root8Node0Domains1 = expandDomains root8Node0Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node0Domains1 v = expandDomains root8Node0Domains1Fast v from by decide) v
theorem root8Node0Step1Chunk0_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_0⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk0_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_1⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk0_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_2⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk0_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_3⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk0_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_4⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk0_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_5⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk1_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_0⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk1_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_1⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk1_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_2⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk1_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_3⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk1_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_4⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk1_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_5⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk2_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_0⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk2_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_1⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk2_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_2⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk2_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_3⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk2_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_4⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk2_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_5⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk3_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_0⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk3_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_1⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk3_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_2⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk3_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_3⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk3_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_4⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk3_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_5⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk4_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_0⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk4_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_1⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk4_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_2⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk4_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_3⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk4_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_4⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk4_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_5⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk5_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_0⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk5_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_1⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk5_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_2⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk5_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_3⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk5_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_4⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk5_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_5⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk6_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_0⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk6_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_1⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk6_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_2⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk6_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_3⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk6_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_4⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk6_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_5⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk7_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_0⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk7_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_1⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk7_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_2⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk7_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_3⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk7_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_4⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk7_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_5⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk8_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_0⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk8_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_1⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk8_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_2⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk8_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_3⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk8_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_4⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk8_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_5⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1_checked :
    checkReplacement table18 root8Node0Domains0 root8Node0Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node0Step1Chunk0_0_checked, root8Node0Step1Chunk0_1_checked, root8Node0Step1Chunk0_2_checked, root8Node0Step1Chunk0_3_checked, root8Node0Step1Chunk0_4_checked, root8Node0Step1Chunk0_5_checked, root8Node0Step1Chunk1_0_checked, root8Node0Step1Chunk1_1_checked, root8Node0Step1Chunk1_2_checked, root8Node0Step1Chunk1_3_checked, root8Node0Step1Chunk1_4_checked, root8Node0Step1Chunk1_5_checked, root8Node0Step1Chunk2_0_checked, root8Node0Step1Chunk2_1_checked, root8Node0Step1Chunk2_2_checked, root8Node0Step1Chunk2_3_checked, root8Node0Step1Chunk2_4_checked, root8Node0Step1Chunk2_5_checked, root8Node0Step1Chunk3_0_checked, root8Node0Step1Chunk3_1_checked, root8Node0Step1Chunk3_2_checked, root8Node0Step1Chunk3_3_checked, root8Node0Step1Chunk3_4_checked, root8Node0Step1Chunk3_5_checked, root8Node0Step1Chunk4_0_checked, root8Node0Step1Chunk4_1_checked, root8Node0Step1Chunk4_2_checked, root8Node0Step1Chunk4_3_checked, root8Node0Step1Chunk4_4_checked, root8Node0Step1Chunk4_5_checked, root8Node0Step1Chunk5_0_checked, root8Node0Step1Chunk5_1_checked, root8Node0Step1Chunk5_2_checked, root8Node0Step1Chunk5_3_checked, root8Node0Step1Chunk5_4_checked, root8Node0Step1Chunk5_5_checked, root8Node0Step1Chunk6_0_checked, root8Node0Step1Chunk6_1_checked, root8Node0Step1Chunk6_2_checked, root8Node0Step1Chunk6_3_checked, root8Node0Step1Chunk6_4_checked, root8Node0Step1Chunk6_5_checked, root8Node0Step1Chunk7_0_checked, root8Node0Step1Chunk7_1_checked, root8Node0Step1Chunk7_2_checked, root8Node0Step1Chunk7_3_checked, root8Node0Step1Chunk7_4_checked, root8Node0Step1Chunk7_5_checked, root8Node0Step1Chunk8_0_checked, root8Node0Step1Chunk8_1_checked, root8Node0Step1Chunk8_2_checked, root8Node0Step1Chunk8_3_checked, root8Node0Step1Chunk8_4_checked, root8Node0Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node0Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => stateChoices
  | 2 => stateChoices
  | 3 => stateChoices
  | 4 => stateChoices
  | 5 => [(0,1),(1,4),(7,4)]
  | 6 => [(0,5),(6,2),(6,3)]
  | 7 => [(4,4),(7,2),(8,4)]
  | 8 => stateChoices
  | 9 => [(0,3),(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 10 => [(4,1),(7,5),(8,5)]
  | 11 => [(0,2),(1,0),(6,0)]
  | 12 => [(1,1),(7,1)]
  | 13 => [(4,1),(5,1),(7,5),(8,1)]
  | 14 => stateChoices
  | 15 => [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 16 => [(1,3),(3,3),(7,3)]
  | 17 => [(5,2),(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(4,2),(5,2),(5,5),(8,2)]
  | 21 => stateChoices
  | 22 => [(0,1),(6,5)]
  | 23 => [(0,4),(6,2)]
  | 24 => [(5,4),(8,4)]
  | 25 => [(1,4),(6,4)]
  | 26 => [(0,5),(1,2)]
  | 27 => stateChoices
  | 28 => [(1,0),(7,0)]
  | 29 => [(4,3),(7,1)]
  | 30 => [(3,5),(7,5)]
  | 31 => [(0,3),(6,0)]
  | 32 => stateChoices
  | 33 => [(1,4),(4,0),(7,4),(8,0)]
  | 34 => [(0,5),(1,3),(6,3),(7,3)]
  | 35 => stateChoices
  | _ => stateChoices
def root8Node0Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => none
  | 1 => none
  | 2 => none
  | 3 => none
  | 4 => none
  | 5 => some [(0,1),(1,4),(7,4)]
  | 6 => some [(0,5),(6,2),(6,3)]
  | 7 => some [(4,4),(7,2),(8,4)]
  | 8 => none
  | 9 => some [(0,3),(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 10 => some [(4,1),(7,5),(8,5)]
  | 11 => some [(0,2),(1,0),(6,0)]
  | 12 => some [(1,1),(7,1)]
  | 13 => some [(4,1),(5,1),(7,5),(8,1)]
  | 14 => none
  | 15 => some [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 16 => some [(1,3),(3,3),(7,3)]
  | 17 => some [(5,2),(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(4,2),(5,2),(5,5),(8,2)]
  | 21 => none
  | 22 => some [(0,1),(6,5)]
  | 23 => some [(0,4),(6,2)]
  | 24 => some [(5,4),(8,4)]
  | 25 => some [(1,4),(6,4)]
  | 26 => some [(0,5),(1,2)]
  | 27 => none
  | 28 => some [(1,0),(7,0)]
  | 29 => some [(4,3),(7,1)]
  | 30 => some [(3,5),(7,5)]
  | 31 => some [(0,3),(6,0)]
  | 32 => none
  | 33 => some [(1,4),(4,0),(7,4),(8,0)]
  | 34 => some [(0,5),(1,3),(6,3),(7,3)]
  | 35 => none
  | _ => none
theorem root8Node0Domains2_fast_eq : root8Node0Domains2 = expandDomains root8Node0Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node0Domains2 v = expandDomains root8Node0Domains2Fast v from by decide) v
theorem root8Node0Step2Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root8Node0Domains1 root8Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains1 root8Node0Domains2
    root8Node0Domains1Fast root8Node0Domains2Fast
    root8Node0Domains1_fast_eq root8Node0Domains2_fast_eq (by decide)
theorem root8Node0Step2_checked :
    checkReplacement table23 root8Node0Domains1 root8Node0Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node0Step2Chunk0_0_checked, root8Node0Step2Chunk0_1_checked, root8Node0Step2Chunk0_2_checked, root8Node0Step2Chunk0_3_checked, root8Node0Step2Chunk0_4_checked, root8Node0Step2Chunk0_5_checked, root8Node0Step2Chunk1_0_checked, root8Node0Step2Chunk1_1_checked, root8Node0Step2Chunk1_2_checked, root8Node0Step2Chunk1_3_checked, root8Node0Step2Chunk1_4_checked, root8Node0Step2Chunk1_5_checked, root8Node0Step2Chunk2_0_checked, root8Node0Step2Chunk2_1_checked, root8Node0Step2Chunk2_2_checked, root8Node0Step2Chunk2_3_checked, root8Node0Step2Chunk2_4_checked, root8Node0Step2Chunk2_5_checked, root8Node0Step2Chunk3_0_checked, root8Node0Step2Chunk3_1_checked, root8Node0Step2Chunk3_2_checked, root8Node0Step2Chunk3_3_checked, root8Node0Step2Chunk3_4_checked, root8Node0Step2Chunk3_5_checked, root8Node0Step2Chunk4_0_checked, root8Node0Step2Chunk4_1_checked, root8Node0Step2Chunk4_2_checked, root8Node0Step2Chunk4_3_checked, root8Node0Step2Chunk4_4_checked, root8Node0Step2Chunk4_5_checked, root8Node0Step2Chunk5_0_checked, root8Node0Step2Chunk5_1_checked, root8Node0Step2Chunk5_2_checked, root8Node0Step2Chunk5_3_checked, root8Node0Step2Chunk5_4_checked, root8Node0Step2Chunk5_5_checked, root8Node0Step2Chunk6_0_checked, root8Node0Step2Chunk6_1_checked, root8Node0Step2Chunk6_2_checked, root8Node0Step2Chunk6_3_checked, root8Node0Step2Chunk6_4_checked, root8Node0Step2Chunk6_5_checked, root8Node0Step2Chunk7_0_checked, root8Node0Step2Chunk7_1_checked, root8Node0Step2Chunk7_2_checked, root8Node0Step2Chunk7_3_checked, root8Node0Step2Chunk7_4_checked, root8Node0Step2Chunk7_5_checked, root8Node0Step2Chunk8_0_checked, root8Node0Step2Chunk8_1_checked, root8Node0Step2Chunk8_2_checked, root8Node0Step2Chunk8_3_checked, root8Node0Step2Chunk8_4_checked, root8Node0Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node0Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => stateChoices
  | 2 => [(5,2),(5,5),(7,5),(8,2),(8,5)]
  | 3 => [(1,0),(6,0),(7,0),(8,0)]
  | 4 => stateChoices
  | 5 => [(0,1),(1,4),(7,4)]
  | 6 => [(0,5),(6,2),(6,3)]
  | 7 => [(4,4),(7,2),(8,4)]
  | 8 => [(1,4),(4,0),(6,4),(7,4)]
  | 9 => [(0,3),(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 10 => [(4,1),(7,5),(8,5)]
  | 11 => [(0,2),(1,0),(6,0)]
  | 12 => [(1,1),(7,1)]
  | 13 => [(4,1),(5,1),(7,5),(8,1)]
  | 14 => [(0,1),(0,2),(0,3),(6,0),(6,5)]
  | 15 => [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 16 => [(1,3),(3,3),(7,3)]
  | 17 => [(5,2),(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(4,2),(5,2),(5,5),(8,2)]
  | 21 => [(1,0),(3,0),(5,0),(5,3),(7,0)]
  | 22 => [(0,1),(6,5)]
  | 23 => [(0,4),(6,2)]
  | 24 => [(5,4),(8,4)]
  | 25 => [(1,4),(6,4)]
  | 26 => [(0,5),(1,2)]
  | 27 => [(4,4),(7,4),(8,4)]
  | 28 => [(1,0),(7,0)]
  | 29 => [(4,3),(7,1)]
  | 30 => [(3,5),(7,5)]
  | 31 => [(0,3),(6,0)]
  | 32 => stateChoices
  | 33 => [(1,4),(4,0),(7,4),(8,0)]
  | 34 => [(0,5),(1,3),(6,3),(7,3)]
  | 35 => stateChoices
  | _ => stateChoices
def root8Node0Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => none
  | 1 => none
  | 2 => some [(5,2),(5,5),(7,5),(8,2),(8,5)]
  | 3 => some [(1,0),(6,0),(7,0),(8,0)]
  | 4 => none
  | 5 => some [(0,1),(1,4),(7,4)]
  | 6 => some [(0,5),(6,2),(6,3)]
  | 7 => some [(4,4),(7,2),(8,4)]
  | 8 => some [(1,4),(4,0),(6,4),(7,4)]
  | 9 => some [(0,3),(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 10 => some [(4,1),(7,5),(8,5)]
  | 11 => some [(0,2),(1,0),(6,0)]
  | 12 => some [(1,1),(7,1)]
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
  | 32 => none
  | 33 => some [(1,4),(4,0),(7,4),(8,0)]
  | 34 => some [(0,5),(1,3),(6,3),(7,3)]
  | 35 => none
  | _ => none
theorem root8Node0Domains3_fast_eq : root8Node0Domains3 = expandDomains root8Node0Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node0Domains3 v = expandDomains root8Node0Domains3Fast v from by decide) v
theorem root8Node0Step3Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root8Node0Domains2 root8Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains2 root8Node0Domains3
    root8Node0Domains2Fast root8Node0Domains3Fast
    root8Node0Domains2_fast_eq root8Node0Domains3_fast_eq (by decide)
theorem root8Node0Step3_checked :
    checkReplacement table13 root8Node0Domains2 root8Node0Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node0Step3Chunk0_0_checked, root8Node0Step3Chunk0_1_checked, root8Node0Step3Chunk0_2_checked, root8Node0Step3Chunk0_3_checked, root8Node0Step3Chunk0_4_checked, root8Node0Step3Chunk0_5_checked, root8Node0Step3Chunk1_0_checked, root8Node0Step3Chunk1_1_checked, root8Node0Step3Chunk1_2_checked, root8Node0Step3Chunk1_3_checked, root8Node0Step3Chunk1_4_checked, root8Node0Step3Chunk1_5_checked, root8Node0Step3Chunk2_0_checked, root8Node0Step3Chunk2_1_checked, root8Node0Step3Chunk2_2_checked, root8Node0Step3Chunk2_3_checked, root8Node0Step3Chunk2_4_checked, root8Node0Step3Chunk2_5_checked, root8Node0Step3Chunk3_0_checked, root8Node0Step3Chunk3_1_checked, root8Node0Step3Chunk3_2_checked, root8Node0Step3Chunk3_3_checked, root8Node0Step3Chunk3_4_checked, root8Node0Step3Chunk3_5_checked, root8Node0Step3Chunk4_0_checked, root8Node0Step3Chunk4_1_checked, root8Node0Step3Chunk4_2_checked, root8Node0Step3Chunk4_3_checked, root8Node0Step3Chunk4_4_checked, root8Node0Step3Chunk4_5_checked, root8Node0Step3Chunk5_0_checked, root8Node0Step3Chunk5_1_checked, root8Node0Step3Chunk5_2_checked, root8Node0Step3Chunk5_3_checked, root8Node0Step3Chunk5_4_checked, root8Node0Step3Chunk5_5_checked, root8Node0Step3Chunk6_0_checked, root8Node0Step3Chunk6_1_checked, root8Node0Step3Chunk6_2_checked, root8Node0Step3Chunk6_3_checked, root8Node0Step3Chunk6_4_checked, root8Node0Step3Chunk6_5_checked, root8Node0Step3Chunk7_0_checked, root8Node0Step3Chunk7_1_checked, root8Node0Step3Chunk7_2_checked, root8Node0Step3Chunk7_3_checked, root8Node0Step3Chunk7_4_checked, root8Node0Step3Chunk7_5_checked, root8Node0Step3Chunk8_0_checked, root8Node0Step3Chunk8_1_checked, root8Node0Step3Chunk8_2_checked, root8Node0Step3Chunk8_3_checked, root8Node0Step3Chunk8_4_checked, root8Node0Step3Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
