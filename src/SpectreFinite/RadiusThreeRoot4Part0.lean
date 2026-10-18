module

public import SpectreFinite.RadiusThreeRoot4Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable19
public import SpectreFinite.RadiusThreeTable23
public import SpectreFinite.RadiusThreeTable6

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node0Domains0 : Domains 37 State := domains (4,0)
def root4Node0Domains0Fast (v : Fin 37) : Option (List State) :=
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
  | 18 => some [(4,0)]
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
theorem root4Node0Domains0_fast_eq : root4Node0Domains0 = expandDomains root4Node0Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node0Domains0 v = expandDomains root4Node0Domains0Fast v from by decide) v
def root4Node0Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => stateChoices
  | 2 => stateChoices
  | 3 => stateChoices
  | 4 => stateChoices
  | 5 => stateChoices
  | 6 => [(0,5),(6,2),(6,3)]
  | 7 => [(4,4),(7,2),(8,4)]
  | 8 => [(1,4),(6,4),(7,4)]
  | 9 => stateChoices
  | 10 => stateChoices
  | 11 => [(0,2),(1,0),(6,0)]
  | 12 => [(1,1),(7,1)]
  | 13 => [(4,1),(7,5)]
  | 14 => [(0,2),(0,3),(6,0)]
  | 15 => stateChoices
  | 16 => stateChoices
  | 17 => [(1,2),(3,2),(7,2)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2),(5,2),(8,2)]
  | 21 => [(5,0),(5,3),(8,0)]
  | 22 => stateChoices
  | 23 => stateChoices
  | 24 => [(5,1)]
  | 25 => [(0,1)]
  | 26 => [(6,2)]
  | 27 => [(7,4),(8,4)]
  | 28 => stateChoices
  | 29 => stateChoices
  | 30 => [(5,5),(8,5)]
  | 31 => [(1,0)]
  | 32 => [(2,1),(7,1)]
  | 33 => stateChoices
  | 34 => stateChoices
  | 35 => stateChoices
  | _ => stateChoices
def root4Node0Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => none
  | 1 => none
  | 2 => none
  | 3 => none
  | 4 => none
  | 5 => none
  | 6 => some [(0,5),(6,2),(6,3)]
  | 7 => some [(4,4),(7,2),(8,4)]
  | 8 => some [(1,4),(6,4),(7,4)]
  | 9 => none
  | 10 => none
  | 11 => some [(0,2),(1,0),(6,0)]
  | 12 => some [(1,1),(7,1)]
  | 13 => some [(4,1),(7,5)]
  | 14 => some [(0,2),(0,3),(6,0)]
  | 15 => none
  | 16 => none
  | 17 => some [(1,2),(3,2),(7,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2),(5,2),(8,2)]
  | 21 => some [(5,0),(5,3),(8,0)]
  | 22 => none
  | 23 => none
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(7,4),(8,4)]
  | 28 => none
  | 29 => none
  | 30 => some [(5,5),(8,5)]
  | 31 => some [(1,0)]
  | 32 => some [(2,1),(7,1)]
  | 33 => none
  | 34 => none
  | 35 => none
  | _ => none
theorem root4Node0Domains1_fast_eq : root4Node0Domains1 = expandDomains root4Node0Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node0Domains1 v = expandDomains root4Node0Domains1Fast v from by decide) v
theorem root4Node0Step1Chunk0_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_0⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk0_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_1⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk0_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_2⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk0_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_3⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk0_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_4⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk0_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_5⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk1_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_0⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk1_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_1⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk1_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_2⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk1_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_3⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk1_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_4⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk1_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_5⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk2_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_0⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk2_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_1⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk2_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_2⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk2_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_3⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk2_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_4⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk2_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_5⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk3_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_0⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk3_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_1⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk3_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_2⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk3_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_3⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk3_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_4⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk3_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_5⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk4_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_0⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk4_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_1⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk4_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_2⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk4_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_3⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk4_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_4⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk4_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_5⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk5_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_0⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk5_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_1⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk5_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_2⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk5_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_3⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk5_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_4⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk5_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_5⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk6_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_0⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk6_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_1⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk6_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_2⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk6_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_3⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk6_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_4⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk6_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_5⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk7_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_0⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk7_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_1⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk7_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_2⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk7_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_3⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk7_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_4⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk7_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_5⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk8_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_0⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk8_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_1⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk8_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_2⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk8_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_3⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk8_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_4⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk8_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_5⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1_checked :
    checkReplacement table19 root4Node0Domains0 root4Node0Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node0Step1Chunk0_0_checked, root4Node0Step1Chunk0_1_checked, root4Node0Step1Chunk0_2_checked, root4Node0Step1Chunk0_3_checked, root4Node0Step1Chunk0_4_checked, root4Node0Step1Chunk0_5_checked, root4Node0Step1Chunk1_0_checked, root4Node0Step1Chunk1_1_checked, root4Node0Step1Chunk1_2_checked, root4Node0Step1Chunk1_3_checked, root4Node0Step1Chunk1_4_checked, root4Node0Step1Chunk1_5_checked, root4Node0Step1Chunk2_0_checked, root4Node0Step1Chunk2_1_checked, root4Node0Step1Chunk2_2_checked, root4Node0Step1Chunk2_3_checked, root4Node0Step1Chunk2_4_checked, root4Node0Step1Chunk2_5_checked, root4Node0Step1Chunk3_0_checked, root4Node0Step1Chunk3_1_checked, root4Node0Step1Chunk3_2_checked, root4Node0Step1Chunk3_3_checked, root4Node0Step1Chunk3_4_checked, root4Node0Step1Chunk3_5_checked, root4Node0Step1Chunk4_0_checked, root4Node0Step1Chunk4_1_checked, root4Node0Step1Chunk4_2_checked, root4Node0Step1Chunk4_3_checked, root4Node0Step1Chunk4_4_checked, root4Node0Step1Chunk4_5_checked, root4Node0Step1Chunk5_0_checked, root4Node0Step1Chunk5_1_checked, root4Node0Step1Chunk5_2_checked, root4Node0Step1Chunk5_3_checked, root4Node0Step1Chunk5_4_checked, root4Node0Step1Chunk5_5_checked, root4Node0Step1Chunk6_0_checked, root4Node0Step1Chunk6_1_checked, root4Node0Step1Chunk6_2_checked, root4Node0Step1Chunk6_3_checked, root4Node0Step1Chunk6_4_checked, root4Node0Step1Chunk6_5_checked, root4Node0Step1Chunk7_0_checked, root4Node0Step1Chunk7_1_checked, root4Node0Step1Chunk7_2_checked, root4Node0Step1Chunk7_3_checked, root4Node0Step1Chunk7_4_checked, root4Node0Step1Chunk7_5_checked, root4Node0Step1Chunk8_0_checked, root4Node0Step1Chunk8_1_checked, root4Node0Step1Chunk8_2_checked, root4Node0Step1Chunk8_3_checked, root4Node0Step1Chunk8_4_checked, root4Node0Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node0Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => stateChoices
  | 2 => stateChoices
  | 3 => stateChoices
  | 4 => stateChoices
  | 5 => stateChoices
  | 6 => [(0,5),(6,2),(6,3)]
  | 7 => [(4,4),(7,2),(8,4)]
  | 8 => [(1,4),(6,4),(7,4)]
  | 9 => [(1,0),(3,0),(4,3),(5,0),(5,3),(7,0),(8,3)]
  | 10 => [(2,1),(2,3),(2,5),(4,5),(7,5),(8,5)]
  | 11 => [(0,2),(1,0),(6,0)]
  | 12 => [(1,1),(7,1)]
  | 13 => [(4,1),(7,5)]
  | 14 => [(0,2),(0,3),(6,0)]
  | 15 => [(4,4),(7,4),(8,4)]
  | 16 => [(0,0),(6,3),(6,4)]
  | 17 => [(1,2),(3,2),(7,2)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2),(5,2),(8,2)]
  | 21 => [(5,0),(5,3),(8,0)]
  | 22 => [(0,2),(1,5),(7,5)]
  | 23 => [(0,3),(1,1),(6,1)]
  | 24 => [(5,1)]
  | 25 => [(0,1)]
  | 26 => [(6,2)]
  | 27 => [(7,4),(8,4)]
  | 28 => [(4,2),(7,0),(8,0)]
  | 29 => [(5,3),(8,3)]
  | 30 => [(5,5),(8,5)]
  | 31 => [(1,0)]
  | 32 => [(2,1),(7,1)]
  | 33 => [(1,4),(7,4)]
  | 34 => [(0,5),(1,3),(6,3)]
  | 35 => stateChoices
  | _ => stateChoices
def root4Node0Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => none
  | 1 => none
  | 2 => none
  | 3 => none
  | 4 => none
  | 5 => none
  | 6 => some [(0,5),(6,2),(6,3)]
  | 7 => some [(4,4),(7,2),(8,4)]
  | 8 => some [(1,4),(6,4),(7,4)]
  | 9 => some [(1,0),(3,0),(4,3),(5,0),(5,3),(7,0),(8,3)]
  | 10 => some [(2,1),(2,3),(2,5),(4,5),(7,5),(8,5)]
  | 11 => some [(0,2),(1,0),(6,0)]
  | 12 => some [(1,1),(7,1)]
  | 13 => some [(4,1),(7,5)]
  | 14 => some [(0,2),(0,3),(6,0)]
  | 15 => some [(4,4),(7,4),(8,4)]
  | 16 => some [(0,0),(6,3),(6,4)]
  | 17 => some [(1,2),(3,2),(7,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2),(5,2),(8,2)]
  | 21 => some [(5,0),(5,3),(8,0)]
  | 22 => some [(0,2),(1,5),(7,5)]
  | 23 => some [(0,3),(1,1),(6,1)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(7,4),(8,4)]
  | 28 => some [(4,2),(7,0),(8,0)]
  | 29 => some [(5,3),(8,3)]
  | 30 => some [(5,5),(8,5)]
  | 31 => some [(1,0)]
  | 32 => some [(2,1),(7,1)]
  | 33 => some [(1,4),(7,4)]
  | 34 => some [(0,5),(1,3),(6,3)]
  | 35 => none
  | _ => none
theorem root4Node0Domains2_fast_eq : root4Node0Domains2 = expandDomains root4Node0Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node0Domains2 v = expandDomains root4Node0Domains2Fast v from by decide) v
theorem root4Node0Step2Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2_checked :
    checkReplacement table23 root4Node0Domains1 root4Node0Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node0Step2Chunk0_0_checked, root4Node0Step2Chunk0_1_checked, root4Node0Step2Chunk0_2_checked, root4Node0Step2Chunk0_3_checked, root4Node0Step2Chunk0_4_checked, root4Node0Step2Chunk0_5_checked, root4Node0Step2Chunk1_0_checked, root4Node0Step2Chunk1_1_checked, root4Node0Step2Chunk1_2_checked, root4Node0Step2Chunk1_3_checked, root4Node0Step2Chunk1_4_checked, root4Node0Step2Chunk1_5_checked, root4Node0Step2Chunk2_0_checked, root4Node0Step2Chunk2_1_checked, root4Node0Step2Chunk2_2_checked, root4Node0Step2Chunk2_3_checked, root4Node0Step2Chunk2_4_checked, root4Node0Step2Chunk2_5_checked, root4Node0Step2Chunk3_0_checked, root4Node0Step2Chunk3_1_checked, root4Node0Step2Chunk3_2_checked, root4Node0Step2Chunk3_3_checked, root4Node0Step2Chunk3_4_checked, root4Node0Step2Chunk3_5_checked, root4Node0Step2Chunk4_0_checked, root4Node0Step2Chunk4_1_checked, root4Node0Step2Chunk4_2_checked, root4Node0Step2Chunk4_3_checked, root4Node0Step2Chunk4_4_checked, root4Node0Step2Chunk4_5_checked, root4Node0Step2Chunk5_0_checked, root4Node0Step2Chunk5_1_checked, root4Node0Step2Chunk5_2_checked, root4Node0Step2Chunk5_3_checked, root4Node0Step2Chunk5_4_checked, root4Node0Step2Chunk5_5_checked, root4Node0Step2Chunk6_0_checked, root4Node0Step2Chunk6_1_checked, root4Node0Step2Chunk6_2_checked, root4Node0Step2Chunk6_3_checked, root4Node0Step2Chunk6_4_checked, root4Node0Step2Chunk6_5_checked, root4Node0Step2Chunk7_0_checked, root4Node0Step2Chunk7_1_checked, root4Node0Step2Chunk7_2_checked, root4Node0Step2Chunk7_3_checked, root4Node0Step2Chunk7_4_checked, root4Node0Step2Chunk7_5_checked, root4Node0Step2Chunk8_0_checked, root4Node0Step2Chunk8_1_checked, root4Node0Step2Chunk8_2_checked, root4Node0Step2Chunk8_3_checked, root4Node0Step2Chunk8_4_checked, root4Node0Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node0Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(2,0),(2,2),(4,0),(4,2),(8,0)]
  | 1 => [(3,3),(5,3),(7,3),(8,3)]
  | 2 => [(5,2),(5,5),(8,2),(8,5)]
  | 3 => [(7,0),(8,0)]
  | 4 => [(0,4),(1,1),(3,1),(5,1),(5,4),(6,2)]
  | 5 => [(0,1),(1,4),(3,4),(7,4)]
  | 6 => [(0,5),(6,2),(6,3)]
  | 7 => [(4,4),(7,2),(8,4)]
  | 8 => [(1,4),(6,4),(7,4)]
  | 9 => [(1,0),(3,0),(4,3),(5,0),(5,3),(7,0),(8,3)]
  | 10 => [(2,1),(2,3),(2,5),(4,5),(7,5),(8,5)]
  | 11 => [(0,2),(1,0),(6,0)]
  | 12 => [(1,1),(7,1)]
  | 13 => [(4,1),(7,5)]
  | 14 => [(0,2),(0,3),(6,0)]
  | 15 => [(4,4),(7,4),(8,4)]
  | 16 => [(0,0),(6,3),(6,4)]
  | 17 => [(1,2),(3,2),(7,2)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2),(5,2),(8,2)]
  | 21 => [(5,0),(5,3),(8,0)]
  | 22 => [(0,2),(1,5),(7,5)]
  | 23 => [(0,3),(1,1),(6,1)]
  | 24 => [(5,1)]
  | 25 => [(0,1)]
  | 26 => [(6,2)]
  | 27 => [(7,4),(8,4)]
  | 28 => [(4,2),(7,0),(8,0)]
  | 29 => [(5,3),(8,3)]
  | 30 => [(5,5),(8,5)]
  | 31 => [(1,0)]
  | 32 => [(2,1),(7,1)]
  | 33 => [(1,4),(7,4)]
  | 34 => [(0,5),(1,3),(6,3)]
  | 35 => stateChoices
  | _ => stateChoices
def root4Node0Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(2,0),(2,2),(4,0),(4,2),(8,0)]
  | 1 => some [(3,3),(5,3),(7,3),(8,3)]
  | 2 => some [(5,2),(5,5),(8,2),(8,5)]
  | 3 => some [(7,0),(8,0)]
  | 4 => some [(0,4),(1,1),(3,1),(5,1),(5,4),(6,2)]
  | 5 => some [(0,1),(1,4),(3,4),(7,4)]
  | 6 => some [(0,5),(6,2),(6,3)]
  | 7 => some [(4,4),(7,2),(8,4)]
  | 8 => some [(1,4),(6,4),(7,4)]
  | 9 => some [(1,0),(3,0),(4,3),(5,0),(5,3),(7,0),(8,3)]
  | 10 => some [(2,1),(2,3),(2,5),(4,5),(7,5),(8,5)]
  | 11 => some [(0,2),(1,0),(6,0)]
  | 12 => some [(1,1),(7,1)]
  | 13 => some [(4,1),(7,5)]
  | 14 => some [(0,2),(0,3),(6,0)]
  | 15 => some [(4,4),(7,4),(8,4)]
  | 16 => some [(0,0),(6,3),(6,4)]
  | 17 => some [(1,2),(3,2),(7,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2),(5,2),(8,2)]
  | 21 => some [(5,0),(5,3),(8,0)]
  | 22 => some [(0,2),(1,5),(7,5)]
  | 23 => some [(0,3),(1,1),(6,1)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(7,4),(8,4)]
  | 28 => some [(4,2),(7,0),(8,0)]
  | 29 => some [(5,3),(8,3)]
  | 30 => some [(5,5),(8,5)]
  | 31 => some [(1,0)]
  | 32 => some [(2,1),(7,1)]
  | 33 => some [(1,4),(7,4)]
  | 34 => some [(0,5),(1,3),(6,3)]
  | 35 => none
  | _ => none
theorem root4Node0Domains3_fast_eq : root4Node0Domains3 = expandDomains root4Node0Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node0Domains3 v = expandDomains root4Node0Domains3Fast v from by decide) v
theorem root4Node0Step3Chunk0_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_0⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk0_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_1⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk0_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_2⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk0_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_3⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk0_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_4⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk0_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_5⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk1_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_0⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk1_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_1⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk1_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_2⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk1_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_3⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk1_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_4⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk1_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_5⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk2_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_0⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk2_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_1⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk2_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_2⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk2_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_3⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk2_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_4⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk2_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_5⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk3_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_0⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk3_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_1⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk3_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_2⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk3_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_3⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk3_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_4⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk3_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_5⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk4_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_0⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk4_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_1⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk4_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_2⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk4_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_3⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk4_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_4⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk4_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_5⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk5_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_0⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk5_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_1⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk5_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_2⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk5_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_3⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk5_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_4⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk5_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_5⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk6_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_0⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk6_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_1⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk6_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_2⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk6_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_3⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk6_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_4⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk6_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_5⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk7_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_0⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk7_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_1⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk7_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_2⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk7_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_3⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk7_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_4⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk7_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_5⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk8_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_0⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk8_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_1⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk8_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_2⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk8_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_3⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk8_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_4⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk8_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_5⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3_checked :
    checkReplacement table6 root4Node0Domains2 root4Node0Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node0Step3Chunk0_0_checked, root4Node0Step3Chunk0_1_checked, root4Node0Step3Chunk0_2_checked, root4Node0Step3Chunk0_3_checked, root4Node0Step3Chunk0_4_checked, root4Node0Step3Chunk0_5_checked, root4Node0Step3Chunk1_0_checked, root4Node0Step3Chunk1_1_checked, root4Node0Step3Chunk1_2_checked, root4Node0Step3Chunk1_3_checked, root4Node0Step3Chunk1_4_checked, root4Node0Step3Chunk1_5_checked, root4Node0Step3Chunk2_0_checked, root4Node0Step3Chunk2_1_checked, root4Node0Step3Chunk2_2_checked, root4Node0Step3Chunk2_3_checked, root4Node0Step3Chunk2_4_checked, root4Node0Step3Chunk2_5_checked, root4Node0Step3Chunk3_0_checked, root4Node0Step3Chunk3_1_checked, root4Node0Step3Chunk3_2_checked, root4Node0Step3Chunk3_3_checked, root4Node0Step3Chunk3_4_checked, root4Node0Step3Chunk3_5_checked, root4Node0Step3Chunk4_0_checked, root4Node0Step3Chunk4_1_checked, root4Node0Step3Chunk4_2_checked, root4Node0Step3Chunk4_3_checked, root4Node0Step3Chunk4_4_checked, root4Node0Step3Chunk4_5_checked, root4Node0Step3Chunk5_0_checked, root4Node0Step3Chunk5_1_checked, root4Node0Step3Chunk5_2_checked, root4Node0Step3Chunk5_3_checked, root4Node0Step3Chunk5_4_checked, root4Node0Step3Chunk5_5_checked, root4Node0Step3Chunk6_0_checked, root4Node0Step3Chunk6_1_checked, root4Node0Step3Chunk6_2_checked, root4Node0Step3Chunk6_3_checked, root4Node0Step3Chunk6_4_checked, root4Node0Step3Chunk6_5_checked, root4Node0Step3Chunk7_0_checked, root4Node0Step3Chunk7_1_checked, root4Node0Step3Chunk7_2_checked, root4Node0Step3Chunk7_3_checked, root4Node0Step3Chunk7_4_checked, root4Node0Step3Chunk7_5_checked, root4Node0Step3Chunk8_0_checked, root4Node0Step3Chunk8_1_checked, root4Node0Step3Chunk8_2_checked, root4Node0Step3Chunk8_3_checked, root4Node0Step3Chunk8_4_checked, root4Node0Step3Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
