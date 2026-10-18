module

public import SpectreFinite.RadiusFourRoot3Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable20
public import SpectreFinite.RadiusFourTable31
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root3Node0Domains0 : Domains 61 State := domains (3,0)
def root3Node0Domains0Fast (v : Fin 61) : Option (List State) :=
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
  | 18 => none
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
  | 30 => some [(3,0)]
  | 31 => none
  | 32 => none
  | 33 => none
  | 34 => none
  | 35 => none
  | 36 => none
  | 37 => none
  | 38 => none
  | 39 => none
  | 40 => none
  | 41 => none
  | 42 => none
  | 43 => none
  | 44 => none
  | 45 => none
  | 46 => none
  | 47 => none
  | 48 => none
  | 49 => none
  | 50 => none
  | 51 => none
  | 52 => none
  | 53 => none
  | 54 => none
  | 55 => none
  | 56 => none
  | 57 => none
  | 58 => none
  | 59 => none
  | _ => none
theorem root3Node0Domains0_fast_eq : root3Node0Domains0 = expandDomains root3Node0Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root3Node0Domains0 v = expandDomains root3Node0Domains0Fast v from by decide) v
def root3Node0Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => stateChoices
  | 2 => stateChoices
  | 3 => stateChoices
  | 4 => stateChoices
  | 5 => stateChoices
  | 6 => stateChoices
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => stateChoices
  | 12 => stateChoices
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(5,5)]
  | 18 => stateChoices
  | 19 => stateChoices
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(1,4)]
  | 24 => [(0,5)]
  | 25 => [(4,4)]
  | 26 => stateChoices
  | 27 => stateChoices
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(3,0)]
  | 31 => [(2,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(7,5)]
  | 35 => stateChoices
  | 36 => stateChoices
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0)]
  | 42 => [(7,3)]
  | 43 => stateChoices
  | 44 => stateChoices
  | 45 => [(7,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(5,1)]
  | 49 => [(0,1)]
  | 50 => stateChoices
  | 51 => stateChoices
  | 52 => [(4,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(8,5)]
  | 56 => stateChoices
  | 57 => stateChoices
  | 58 => stateChoices
  | 59 => stateChoices
  | _ => stateChoices
def root3Node0Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => none
  | 1 => none
  | 2 => none
  | 3 => none
  | 4 => none
  | 5 => none
  | 6 => none
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => none
  | 12 => none
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5)]
  | 18 => none
  | 19 => none
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(1,4)]
  | 24 => some [(0,5)]
  | 25 => some [(4,4)]
  | 26 => none
  | 27 => none
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(3,0)]
  | 31 => some [(2,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(7,5)]
  | 35 => none
  | 36 => none
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => none
  | 44 => none
  | 45 => some [(7,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => none
  | 51 => none
  | 52 => some [(4,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => none
  | 57 => none
  | 58 => none
  | 59 => none
  | _ => none
theorem root3Node0Domains1_fast_eq : root3Node0Domains1 = expandDomains root3Node0Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root3Node0Domains1 v = expandDomains root3Node0Domains1Fast v from by decide) v
theorem root3Node0Step1Chunk0_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk0_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk0_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk0_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk0_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk0_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk1_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk1_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk1_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk1_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk1_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk1_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk2_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk2_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk2_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk2_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk2_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk2_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk3_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk3_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk3_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk3_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk3_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk3_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk4_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk4_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk4_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk4_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk4_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk4_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk5_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk5_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk5_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk5_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk5_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk5_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk6_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk6_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk6_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk6_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk6_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk6_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk7_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk7_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk7_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk7_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk7_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk7_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk8_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk8_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk8_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk8_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk8_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk8_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1_checked :
    checkReplacement table31 root3Node0Domains0 root3Node0Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root3Node0Step1Chunk0_0_checked, root3Node0Step1Chunk0_1_checked, root3Node0Step1Chunk0_2_checked, root3Node0Step1Chunk0_3_checked, root3Node0Step1Chunk0_4_checked, root3Node0Step1Chunk0_5_checked, root3Node0Step1Chunk1_0_checked, root3Node0Step1Chunk1_1_checked, root3Node0Step1Chunk1_2_checked, root3Node0Step1Chunk1_3_checked, root3Node0Step1Chunk1_4_checked, root3Node0Step1Chunk1_5_checked, root3Node0Step1Chunk2_0_checked, root3Node0Step1Chunk2_1_checked, root3Node0Step1Chunk2_2_checked, root3Node0Step1Chunk2_3_checked, root3Node0Step1Chunk2_4_checked, root3Node0Step1Chunk2_5_checked, root3Node0Step1Chunk3_0_checked, root3Node0Step1Chunk3_1_checked, root3Node0Step1Chunk3_2_checked, root3Node0Step1Chunk3_3_checked, root3Node0Step1Chunk3_4_checked, root3Node0Step1Chunk3_5_checked, root3Node0Step1Chunk4_0_checked, root3Node0Step1Chunk4_1_checked, root3Node0Step1Chunk4_2_checked, root3Node0Step1Chunk4_3_checked, root3Node0Step1Chunk4_4_checked, root3Node0Step1Chunk4_5_checked, root3Node0Step1Chunk5_0_checked, root3Node0Step1Chunk5_1_checked, root3Node0Step1Chunk5_2_checked, root3Node0Step1Chunk5_3_checked, root3Node0Step1Chunk5_4_checked, root3Node0Step1Chunk5_5_checked, root3Node0Step1Chunk6_0_checked, root3Node0Step1Chunk6_1_checked, root3Node0Step1Chunk6_2_checked, root3Node0Step1Chunk6_3_checked, root3Node0Step1Chunk6_4_checked, root3Node0Step1Chunk6_5_checked, root3Node0Step1Chunk7_0_checked, root3Node0Step1Chunk7_1_checked, root3Node0Step1Chunk7_2_checked, root3Node0Step1Chunk7_3_checked, root3Node0Step1Chunk7_4_checked, root3Node0Step1Chunk7_5_checked, root3Node0Step1Chunk8_0_checked, root3Node0Step1Chunk8_1_checked, root3Node0Step1Chunk8_2_checked, root3Node0Step1Chunk8_3_checked, root3Node0Step1Chunk8_4_checked, root3Node0Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root3Node0Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => stateChoices
  | 4 => stateChoices
  | 5 => [(4,5),(8,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => [(0,0),(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(5,5)]
  | 18 => [(0,2),(1,5)]
  | 19 => [(1,1),(6,1)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(1,4)]
  | 24 => [(0,5)]
  | 25 => [(4,4)]
  | 26 => [(5,2),(5,5)]
  | 27 => [(7,0),(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(3,0)]
  | 31 => [(2,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(7,5)]
  | 35 => [(4,4),(5,4),(8,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0)]
  | 42 => [(7,3)]
  | 43 => [(7,5)]
  | 44 => [(6,0)]
  | 45 => [(7,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(5,1)]
  | 49 => [(0,1)]
  | 50 => stateChoices
  | 51 => stateChoices
  | 52 => [(4,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(8,5)]
  | 56 => stateChoices
  | 57 => stateChoices
  | 58 => stateChoices
  | 59 => stateChoices
  | _ => stateChoices
def root3Node0Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => none
  | 4 => none
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(1,4)]
  | 24 => some [(0,5)]
  | 25 => some [(4,4)]
  | 26 => some [(5,2),(5,5)]
  | 27 => some [(7,0),(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(3,0)]
  | 31 => some [(2,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(4,4),(5,4),(8,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5)]
  | 44 => some [(6,0)]
  | 45 => some [(7,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => none
  | 51 => none
  | 52 => some [(4,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => none
  | 57 => none
  | 58 => none
  | 59 => none
  | _ => none
theorem root3Node0Domains2_fast_eq : root3Node0Domains2 = expandDomains root3Node0Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root3Node0Domains2 v = expandDomains root3Node0Domains2Fast v from by decide) v
theorem root3Node0Step2Chunk0_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk0_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk0_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk0_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk0_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk0_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk1_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk1_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk1_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk1_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk1_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk1_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk2_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk2_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk2_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk2_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk2_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk2_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk3_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk3_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk3_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk3_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk3_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk3_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk4_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk4_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk4_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk4_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk4_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk4_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk5_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk5_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk5_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk5_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk5_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk5_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk6_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk6_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk6_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk6_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk6_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk6_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk7_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk7_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk7_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk7_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk7_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk7_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk8_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk8_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk8_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk8_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk8_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk8_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2_checked :
    checkReplacement table20 root3Node0Domains1 root3Node0Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root3Node0Step2Chunk0_0_checked, root3Node0Step2Chunk0_1_checked, root3Node0Step2Chunk0_2_checked, root3Node0Step2Chunk0_3_checked, root3Node0Step2Chunk0_4_checked, root3Node0Step2Chunk0_5_checked, root3Node0Step2Chunk1_0_checked, root3Node0Step2Chunk1_1_checked, root3Node0Step2Chunk1_2_checked, root3Node0Step2Chunk1_3_checked, root3Node0Step2Chunk1_4_checked, root3Node0Step2Chunk1_5_checked, root3Node0Step2Chunk2_0_checked, root3Node0Step2Chunk2_1_checked, root3Node0Step2Chunk2_2_checked, root3Node0Step2Chunk2_3_checked, root3Node0Step2Chunk2_4_checked, root3Node0Step2Chunk2_5_checked, root3Node0Step2Chunk3_0_checked, root3Node0Step2Chunk3_1_checked, root3Node0Step2Chunk3_2_checked, root3Node0Step2Chunk3_3_checked, root3Node0Step2Chunk3_4_checked, root3Node0Step2Chunk3_5_checked, root3Node0Step2Chunk4_0_checked, root3Node0Step2Chunk4_1_checked, root3Node0Step2Chunk4_2_checked, root3Node0Step2Chunk4_3_checked, root3Node0Step2Chunk4_4_checked, root3Node0Step2Chunk4_5_checked, root3Node0Step2Chunk5_0_checked, root3Node0Step2Chunk5_1_checked, root3Node0Step2Chunk5_2_checked, root3Node0Step2Chunk5_3_checked, root3Node0Step2Chunk5_4_checked, root3Node0Step2Chunk5_5_checked, root3Node0Step2Chunk6_0_checked, root3Node0Step2Chunk6_1_checked, root3Node0Step2Chunk6_2_checked, root3Node0Step2Chunk6_3_checked, root3Node0Step2Chunk6_4_checked, root3Node0Step2Chunk6_5_checked, root3Node0Step2Chunk7_0_checked, root3Node0Step2Chunk7_1_checked, root3Node0Step2Chunk7_2_checked, root3Node0Step2Chunk7_3_checked, root3Node0Step2Chunk7_4_checked, root3Node0Step2Chunk7_5_checked, root3Node0Step2Chunk8_0_checked, root3Node0Step2Chunk8_1_checked, root3Node0Step2Chunk8_2_checked, root3Node0Step2Chunk8_3_checked, root3Node0Step2Chunk8_4_checked, root3Node0Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root3Node0Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => stateChoices
  | 4 => stateChoices
  | 5 => [(4,5),(8,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => [(0,0),(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(5,5)]
  | 18 => [(0,2),(1,5)]
  | 19 => [(1,1),(6,1)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(1,4)]
  | 24 => [(0,5)]
  | 25 => [(4,4)]
  | 26 => [(5,2),(5,5)]
  | 27 => [(7,0),(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(3,0)]
  | 31 => [(2,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(7,5)]
  | 35 => [(4,4),(5,4),(8,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0)]
  | 42 => [(7,3)]
  | 43 => [(7,5)]
  | 44 => [(6,0)]
  | 45 => [(7,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(5,1)]
  | 49 => [(0,1)]
  | 50 => [(8,2)]
  | 51 => [(5,0)]
  | 52 => [(4,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(8,5)]
  | 56 => [(5,4),(8,4)]
  | 57 => [(0,0)]
  | 58 => [(7,2)]
  | 59 => [(7,4)]
  | _ => [(1,3),(6,3)]
def root3Node0Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => none
  | 4 => none
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(1,4)]
  | 24 => some [(0,5)]
  | 25 => some [(4,4)]
  | 26 => some [(5,2),(5,5)]
  | 27 => some [(7,0),(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(3,0)]
  | 31 => some [(2,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(4,4),(5,4),(8,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5)]
  | 44 => some [(6,0)]
  | 45 => some [(7,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(8,2)]
  | 51 => some [(5,0)]
  | 52 => some [(4,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(0,0)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | _ => some [(1,3),(6,3)]
theorem root3Node0Domains3_fast_eq : root3Node0Domains3 = expandDomains root3Node0Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root3Node0Domains3 v = expandDomains root3Node0Domains3Fast v from by decide) v
theorem root3Node0Step3Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3_checked :
    checkReplacement table46 root3Node0Domains2 root3Node0Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root3Node0Step3Chunk0_0_checked, root3Node0Step3Chunk0_1_checked, root3Node0Step3Chunk0_2_checked, root3Node0Step3Chunk0_3_checked, root3Node0Step3Chunk0_4_checked, root3Node0Step3Chunk0_5_checked, root3Node0Step3Chunk1_0_checked, root3Node0Step3Chunk1_1_checked, root3Node0Step3Chunk1_2_checked, root3Node0Step3Chunk1_3_checked, root3Node0Step3Chunk1_4_checked, root3Node0Step3Chunk1_5_checked, root3Node0Step3Chunk2_0_checked, root3Node0Step3Chunk2_1_checked, root3Node0Step3Chunk2_2_checked, root3Node0Step3Chunk2_3_checked, root3Node0Step3Chunk2_4_checked, root3Node0Step3Chunk2_5_checked, root3Node0Step3Chunk3_0_checked, root3Node0Step3Chunk3_1_checked, root3Node0Step3Chunk3_2_checked, root3Node0Step3Chunk3_3_checked, root3Node0Step3Chunk3_4_checked, root3Node0Step3Chunk3_5_checked, root3Node0Step3Chunk4_0_checked, root3Node0Step3Chunk4_1_checked, root3Node0Step3Chunk4_2_checked, root3Node0Step3Chunk4_3_checked, root3Node0Step3Chunk4_4_checked, root3Node0Step3Chunk4_5_checked, root3Node0Step3Chunk5_0_checked, root3Node0Step3Chunk5_1_checked, root3Node0Step3Chunk5_2_checked, root3Node0Step3Chunk5_3_checked, root3Node0Step3Chunk5_4_checked, root3Node0Step3Chunk5_5_checked, root3Node0Step3Chunk6_0_checked, root3Node0Step3Chunk6_1_checked, root3Node0Step3Chunk6_2_checked, root3Node0Step3Chunk6_3_checked, root3Node0Step3Chunk6_4_checked, root3Node0Step3Chunk6_5_checked, root3Node0Step3Chunk7_0_checked, root3Node0Step3Chunk7_1_checked, root3Node0Step3Chunk7_2_checked, root3Node0Step3Chunk7_3_checked, root3Node0Step3Chunk7_4_checked, root3Node0Step3Chunk7_5_checked, root3Node0Step3Chunk8_0_checked, root3Node0Step3Chunk8_1_checked, root3Node0Step3Chunk8_2_checked, root3Node0Step3Chunk8_3_checked, root3Node0Step3Chunk8_4_checked, root3Node0Step3Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
