module

public import SpectreFinite.RadiusFiveRoot3Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable1
public import SpectreFinite.RadiusFiveTable33
public import SpectreFinite.RadiusFiveTable46
public import SpectreFinite.RadiusFiveTable65

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root3Node0Domains0 : Domains 91 State := domains (3,0)
def root3Node0Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 30 => none
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
  | 45 => some [(3,0)]
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
  | 60 => none
  | 61 => none
  | 62 => none
  | 63 => none
  | 64 => none
  | 65 => none
  | 66 => none
  | 67 => none
  | 68 => none
  | 69 => none
  | 70 => none
  | 71 => none
  | 72 => none
  | 73 => none
  | 74 => none
  | 75 => none
  | 76 => none
  | 77 => none
  | 78 => none
  | 79 => none
  | 80 => none
  | 81 => none
  | 82 => none
  | 83 => none
  | 84 => none
  | 85 => none
  | 86 => none
  | 87 => none
  | 88 => none
  | 89 => none
  | _ => none
theorem root3Node0Domains0_fast_eq : root3Node0Domains0 = expandDomains root3Node0Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root3Node0Domains0 v = expandDomains root3Node0Domains0Fast v from by decide) v
def root3Node0Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => stateChoices
  | 2 => stateChoices
  | 3 => stateChoices
  | 4 => stateChoices
  | 5 => stateChoices
  | 6 => stateChoices
  | 7 => stateChoices
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(6,4)]
  | 11 => [(1,2)]
  | 12 => [(7,4),(8,4)]
  | 13 => stateChoices
  | 14 => stateChoices
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(0,3)]
  | 19 => [(8,1)]
  | 20 => [(1,5),(6,5)]
  | 21 => stateChoices
  | 22 => stateChoices
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(4,2)]
  | 27 => [(5,3)]
  | 28 => [(5,5)]
  | 29 => [(7,0)]
  | 30 => stateChoices
  | 31 => stateChoices
  | 32 => [(1,1),(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(1,4)]
  | 40 => stateChoices
  | 41 => stateChoices
  | 42 => [(7,0),(8,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5)]
  | 45 => [(3,0)]
  | 46 => [(2,5)]
  | 47 => [(6,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(6,0)]
  | 51 => stateChoices
  | 52 => stateChoices
  | 53 => [(1,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(4,0)]
  | 59 => [(7,3)]
  | 60 => [(8,2)]
  | 61 => stateChoices
  | 62 => stateChoices
  | 63 => [(6,0)]
  | 64 => [(7,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(5,1)]
  | 68 => [(0,1)]
  | 69 => [(6,2)]
  | 70 => stateChoices
  | 71 => stateChoices
  | 72 => [(5,0)]
  | 73 => [(4,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(8,5)]
  | 77 => [(1,0)]
  | 78 => stateChoices
  | 79 => stateChoices
  | 80 => [(0,0)]
  | 81 => [(7,2)]
  | 82 => [(7,4)]
  | 83 => [(1,3),(6,3)]
  | 84 => [(7,2),(8,2)]
  | 85 => stateChoices
  | 86 => stateChoices
  | 87 => stateChoices
  | 88 => stateChoices
  | 89 => stateChoices
  | _ => stateChoices
def root3Node0Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => none
  | 1 => none
  | 2 => none
  | 3 => none
  | 4 => none
  | 5 => none
  | 6 => none
  | 7 => none
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(7,4),(8,4)]
  | 13 => none
  | 14 => none
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3)]
  | 19 => some [(8,1)]
  | 20 => some [(1,5),(6,5)]
  | 21 => none
  | 22 => none
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2)]
  | 27 => some [(5,3)]
  | 28 => some [(5,5)]
  | 29 => some [(7,0)]
  | 30 => none
  | 31 => none
  | 32 => some [(1,1),(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(1,4)]
  | 40 => none
  | 41 => none
  | 42 => some [(7,0),(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(3,0)]
  | 46 => some [(2,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(6,0)]
  | 51 => none
  | 52 => none
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(8,2)]
  | 61 => none
  | 62 => none
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => none
  | 71 => none
  | 72 => some [(5,0)]
  | 73 => some [(4,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(8,5)]
  | 77 => some [(1,0)]
  | 78 => none
  | 79 => none
  | 80 => some [(0,0)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(1,3),(6,3)]
  | 84 => some [(7,2),(8,2)]
  | 85 => none
  | 86 => none
  | 87 => none
  | 88 => none
  | 89 => none
  | _ => none
theorem root3Node0Domains1_fast_eq : root3Node0Domains1 = expandDomains root3Node0Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root3Node0Domains1 v = expandDomains root3Node0Domains1Fast v from by decide) v
theorem root3Node0Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq (by decide)
theorem root3Node0Step1Narrowing_checked :
    checkNarrowing table46 root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkNarrowing_flatten table46Scope [table46Rows0_0,table46Rows0_1,table46Rows0_2,table46Rows0_3,table46Rows0_4,table46Rows0_5,table46Rows1_0,table46Rows1_1,table46Rows1_2,table46Rows1_3,table46Rows1_4,table46Rows1_5,table46Rows2_0,table46Rows2_1,table46Rows2_2,table46Rows2_3,table46Rows2_4,table46Rows2_5,table46Rows3_0,table46Rows3_1,table46Rows3_2,table46Rows3_3,table46Rows3_4,table46Rows3_5,table46Rows4_0,table46Rows4_1,table46Rows4_2,table46Rows4_3,table46Rows4_4,table46Rows4_5,table46Rows5_0,table46Rows5_1,table46Rows5_2,table46Rows5_3,table46Rows5_4,table46Rows5_5,table46Rows6_0,table46Rows6_1,table46Rows6_2,table46Rows6_3,table46Rows6_4,table46Rows6_5,table46Rows7_0,table46Rows7_1,table46Rows7_2,table46Rows7_3,table46Rows7_4,table46Rows7_5,table46Rows8_0,table46Rows8_1,table46Rows8_2,table46Rows8_3,table46Rows8_4,table46Rows8_5]
    root3Node0Domains0 root3Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root3Node0Step1Chunk0_0_checked, root3Node0Step1Chunk0_1_checked, root3Node0Step1Chunk0_2_checked, root3Node0Step1Chunk0_3_checked, root3Node0Step1Chunk0_4_checked, root3Node0Step1Chunk0_5_checked, root3Node0Step1Chunk1_0_checked, root3Node0Step1Chunk1_1_checked, root3Node0Step1Chunk1_2_checked, root3Node0Step1Chunk1_3_checked, root3Node0Step1Chunk1_4_checked, root3Node0Step1Chunk1_5_checked, root3Node0Step1Chunk2_0_checked, root3Node0Step1Chunk2_1_checked, root3Node0Step1Chunk2_2_checked, root3Node0Step1Chunk2_3_checked, root3Node0Step1Chunk2_4_checked, root3Node0Step1Chunk2_5_checked, root3Node0Step1Chunk3_0_checked, root3Node0Step1Chunk3_1_checked, root3Node0Step1Chunk3_2_checked, root3Node0Step1Chunk3_3_checked, root3Node0Step1Chunk3_4_checked, root3Node0Step1Chunk3_5_checked, root3Node0Step1Chunk4_0_checked, root3Node0Step1Chunk4_1_checked, root3Node0Step1Chunk4_2_checked, root3Node0Step1Chunk4_3_checked, root3Node0Step1Chunk4_4_checked, root3Node0Step1Chunk4_5_checked, root3Node0Step1Chunk5_0_checked, root3Node0Step1Chunk5_1_checked, root3Node0Step1Chunk5_2_checked, root3Node0Step1Chunk5_3_checked, root3Node0Step1Chunk5_4_checked, root3Node0Step1Chunk5_5_checked, root3Node0Step1Chunk6_0_checked, root3Node0Step1Chunk6_1_checked, root3Node0Step1Chunk6_2_checked, root3Node0Step1Chunk6_3_checked, root3Node0Step1Chunk6_4_checked, root3Node0Step1Chunk6_5_checked, root3Node0Step1Chunk7_0_checked, root3Node0Step1Chunk7_1_checked, root3Node0Step1Chunk7_2_checked, root3Node0Step1Chunk7_3_checked, root3Node0Step1Chunk7_4_checked, root3Node0Step1Chunk7_5_checked, root3Node0Step1Chunk8_0_checked, root3Node0Step1Chunk8_1_checked, root3Node0Step1Chunk8_2_checked, root3Node0Step1Chunk8_3_checked, root3Node0Step1Chunk8_4_checked, root3Node0Step1Chunk8_5_checked, Bool.true_and])
theorem root3Node0Step1_checked :
    checkReplacement table46 root3Node0Domains0 root3Node0Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root3Node0Domains0 root3Node0Domains1
    root3Node0Domains0Fast root3Node0Domains1Fast
    root3Node0Domains0_fast_eq root3Node0Domains1_fast_eq
    root3Node0Step1Narrowing_checked (by decide)
def root3Node0Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,4),(7,4)]
  | 1 => [(1,3)]
  | 2 => [(5,2),(8,2)]
  | 3 => [(8,0)]
  | 4 => stateChoices
  | 5 => stateChoices
  | 6 => [(7,1),(8,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(6,4)]
  | 11 => [(1,2)]
  | 12 => [(7,4),(8,4)]
  | 13 => [(5,0),(5,3),(8,3)]
  | 14 => [(4,5),(8,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(0,3)]
  | 19 => [(8,1)]
  | 20 => [(1,5),(6,5)]
  | 21 => [(7,4),(8,4)]
  | 22 => [(0,0),(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(4,2)]
  | 27 => [(5,3)]
  | 28 => [(5,5)]
  | 29 => [(7,0)]
  | 30 => [(4,1),(8,1)]
  | 31 => [(0,2),(1,5)]
  | 32 => [(1,1),(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(1,4)]
  | 40 => [(1,3),(3,3),(5,3),(7,3)]
  | 41 => [(5,2),(5,5)]
  | 42 => [(7,0),(8,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5)]
  | 45 => [(3,0)]
  | 46 => [(2,5)]
  | 47 => [(6,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(6,0)]
  | 51 => [(0,4),(0,5),(6,2)]
  | 52 => [(4,4),(5,4),(8,4)]
  | 53 => [(1,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(4,0)]
  | 59 => [(7,3)]
  | 60 => [(8,2)]
  | 61 => [(4,3),(7,1)]
  | 62 => [(7,5)]
  | 63 => [(6,0)]
  | 64 => [(7,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(5,1)]
  | 68 => [(0,1)]
  | 69 => [(6,2)]
  | 70 => [(1,3),(7,3)]
  | 71 => [(8,2)]
  | 72 => [(5,0)]
  | 73 => [(4,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(8,5)]
  | 77 => [(1,0)]
  | 78 => stateChoices
  | 79 => stateChoices
  | 80 => [(0,0)]
  | 81 => [(7,2)]
  | 82 => [(7,4)]
  | 83 => [(1,3),(6,3)]
  | 84 => [(7,2),(8,2)]
  | 85 => stateChoices
  | 86 => stateChoices
  | 87 => stateChoices
  | 88 => stateChoices
  | 89 => stateChoices
  | _ => stateChoices
def root3Node0Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4),(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2),(8,2)]
  | 3 => some [(8,0)]
  | 4 => none
  | 5 => none
  | 6 => some [(7,1),(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(7,4),(8,4)]
  | 13 => some [(5,0),(5,3),(8,3)]
  | 14 => some [(4,5),(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3)]
  | 19 => some [(8,1)]
  | 20 => some [(1,5),(6,5)]
  | 21 => some [(7,4),(8,4)]
  | 22 => some [(0,0),(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2)]
  | 27 => some [(5,3)]
  | 28 => some [(5,5)]
  | 29 => some [(7,0)]
  | 30 => some [(4,1),(8,1)]
  | 31 => some [(0,2),(1,5)]
  | 32 => some [(1,1),(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(1,4)]
  | 40 => some [(1,3),(3,3),(5,3),(7,3)]
  | 41 => some [(5,2),(5,5)]
  | 42 => some [(7,0),(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(3,0)]
  | 46 => some [(2,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(6,0)]
  | 51 => some [(0,4),(0,5),(6,2)]
  | 52 => some [(4,4),(5,4),(8,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(8,2)]
  | 61 => some [(4,3),(7,1)]
  | 62 => some [(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(8,2)]
  | 72 => some [(5,0)]
  | 73 => some [(4,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(8,5)]
  | 77 => some [(1,0)]
  | 78 => none
  | 79 => none
  | 80 => some [(0,0)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(1,3),(6,3)]
  | 84 => some [(7,2),(8,2)]
  | 85 => none
  | 86 => none
  | 87 => none
  | 88 => none
  | 89 => none
  | _ => none
theorem root3Node0Domains2_fast_eq : root3Node0Domains2 = expandDomains root3Node0Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root3Node0Domains2 v = expandDomains root3Node0Domains2Fast v from by decide) v
theorem root3Node0Step2Chunk0_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk0_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk0_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk0_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk0_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk0_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk1_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk1_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk1_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk1_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk1_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk1_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk2_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk2_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk2_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk2_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk2_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk2_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk3_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk3_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk3_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk3_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk3_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk3_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk4_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk4_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk4_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk4_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk4_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk4_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk5_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk5_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk5_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk5_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk5_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk5_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk6_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk6_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk6_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk6_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk6_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk6_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk7_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk7_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk7_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk7_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk7_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk7_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk8_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_0⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk8_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_1⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk8_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_2⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk8_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_3⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk8_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_4⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Chunk8_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_5⟩
      root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq (by decide)
theorem root3Node0Step2Narrowing_checked :
    checkNarrowing table33 root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkNarrowing_flatten table33Scope [table33Rows0_0,table33Rows0_1,table33Rows0_2,table33Rows0_3,table33Rows0_4,table33Rows0_5,table33Rows1_0,table33Rows1_1,table33Rows1_2,table33Rows1_3,table33Rows1_4,table33Rows1_5,table33Rows2_0,table33Rows2_1,table33Rows2_2,table33Rows2_3,table33Rows2_4,table33Rows2_5,table33Rows3_0,table33Rows3_1,table33Rows3_2,table33Rows3_3,table33Rows3_4,table33Rows3_5,table33Rows4_0,table33Rows4_1,table33Rows4_2,table33Rows4_3,table33Rows4_4,table33Rows4_5,table33Rows5_0,table33Rows5_1,table33Rows5_2,table33Rows5_3,table33Rows5_4,table33Rows5_5,table33Rows6_0,table33Rows6_1,table33Rows6_2,table33Rows6_3,table33Rows6_4,table33Rows6_5,table33Rows7_0,table33Rows7_1,table33Rows7_2,table33Rows7_3,table33Rows7_4,table33Rows7_5,table33Rows8_0,table33Rows8_1,table33Rows8_2,table33Rows8_3,table33Rows8_4,table33Rows8_5]
    root3Node0Domains1 root3Node0Domains2 (by
      simp only [List.all_cons, List.all_nil, root3Node0Step2Chunk0_0_checked, root3Node0Step2Chunk0_1_checked, root3Node0Step2Chunk0_2_checked, root3Node0Step2Chunk0_3_checked, root3Node0Step2Chunk0_4_checked, root3Node0Step2Chunk0_5_checked, root3Node0Step2Chunk1_0_checked, root3Node0Step2Chunk1_1_checked, root3Node0Step2Chunk1_2_checked, root3Node0Step2Chunk1_3_checked, root3Node0Step2Chunk1_4_checked, root3Node0Step2Chunk1_5_checked, root3Node0Step2Chunk2_0_checked, root3Node0Step2Chunk2_1_checked, root3Node0Step2Chunk2_2_checked, root3Node0Step2Chunk2_3_checked, root3Node0Step2Chunk2_4_checked, root3Node0Step2Chunk2_5_checked, root3Node0Step2Chunk3_0_checked, root3Node0Step2Chunk3_1_checked, root3Node0Step2Chunk3_2_checked, root3Node0Step2Chunk3_3_checked, root3Node0Step2Chunk3_4_checked, root3Node0Step2Chunk3_5_checked, root3Node0Step2Chunk4_0_checked, root3Node0Step2Chunk4_1_checked, root3Node0Step2Chunk4_2_checked, root3Node0Step2Chunk4_3_checked, root3Node0Step2Chunk4_4_checked, root3Node0Step2Chunk4_5_checked, root3Node0Step2Chunk5_0_checked, root3Node0Step2Chunk5_1_checked, root3Node0Step2Chunk5_2_checked, root3Node0Step2Chunk5_3_checked, root3Node0Step2Chunk5_4_checked, root3Node0Step2Chunk5_5_checked, root3Node0Step2Chunk6_0_checked, root3Node0Step2Chunk6_1_checked, root3Node0Step2Chunk6_2_checked, root3Node0Step2Chunk6_3_checked, root3Node0Step2Chunk6_4_checked, root3Node0Step2Chunk6_5_checked, root3Node0Step2Chunk7_0_checked, root3Node0Step2Chunk7_1_checked, root3Node0Step2Chunk7_2_checked, root3Node0Step2Chunk7_3_checked, root3Node0Step2Chunk7_4_checked, root3Node0Step2Chunk7_5_checked, root3Node0Step2Chunk8_0_checked, root3Node0Step2Chunk8_1_checked, root3Node0Step2Chunk8_2_checked, root3Node0Step2Chunk8_3_checked, root3Node0Step2Chunk8_4_checked, root3Node0Step2Chunk8_5_checked, Bool.true_and])
theorem root3Node0Step2_checked :
    checkReplacement table33 root3Node0Domains1 root3Node0Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root3Node0Domains1 root3Node0Domains2
    root3Node0Domains1Fast root3Node0Domains2Fast
    root3Node0Domains1_fast_eq root3Node0Domains2_fast_eq
    root3Node0Step2Narrowing_checked (by decide)
def root3Node0Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,4),(7,4)]
  | 1 => [(1,3)]
  | 2 => [(5,2),(8,2)]
  | 3 => [(8,0)]
  | 4 => stateChoices
  | 5 => stateChoices
  | 6 => [(7,1),(8,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(6,4)]
  | 11 => [(1,2)]
  | 12 => [(7,4),(8,4)]
  | 13 => [(5,0),(5,3),(8,3)]
  | 14 => [(4,5),(8,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(0,3)]
  | 19 => [(8,1)]
  | 20 => [(1,5),(6,5)]
  | 21 => [(7,4),(8,4)]
  | 22 => [(0,0),(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(4,2)]
  | 27 => [(5,3)]
  | 28 => [(5,5)]
  | 29 => [(7,0)]
  | 30 => [(4,1),(8,1)]
  | 31 => [(0,2),(1,5)]
  | 32 => [(1,1),(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(1,4)]
  | 40 => [(1,3),(3,3),(5,3),(7,3)]
  | 41 => [(5,2),(5,5)]
  | 42 => [(7,0),(8,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5)]
  | 45 => [(3,0)]
  | 46 => [(2,5)]
  | 47 => [(6,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(6,0)]
  | 51 => [(0,4),(0,5),(6,2)]
  | 52 => [(4,4),(5,4),(8,4)]
  | 53 => [(1,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(4,0)]
  | 59 => [(7,3)]
  | 60 => [(8,2)]
  | 61 => [(4,3),(7,1)]
  | 62 => [(7,5)]
  | 63 => [(6,0)]
  | 64 => [(7,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(5,1)]
  | 68 => [(0,1)]
  | 69 => [(6,2)]
  | 70 => [(1,3),(7,3)]
  | 71 => [(8,2)]
  | 72 => [(5,0)]
  | 73 => [(4,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(8,5)]
  | 77 => [(1,0)]
  | 78 => [(0,4),(1,2),(6,2)]
  | 79 => [(5,4),(8,4)]
  | 80 => [(0,0)]
  | 81 => [(7,2)]
  | 82 => [(7,4)]
  | 83 => [(1,3),(6,3)]
  | 84 => [(7,2),(8,2)]
  | 85 => [(4,3),(7,1),(8,1)]
  | 86 => [(1,5)]
  | 87 => [(6,1)]
  | 88 => [(4,1),(8,1)]
  | 89 => [(0,2),(6,5)]
  | _ => [(0,4),(1,1)]
def root3Node0Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4),(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2),(8,2)]
  | 3 => some [(8,0)]
  | 4 => none
  | 5 => none
  | 6 => some [(7,1),(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(7,4),(8,4)]
  | 13 => some [(5,0),(5,3),(8,3)]
  | 14 => some [(4,5),(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3)]
  | 19 => some [(8,1)]
  | 20 => some [(1,5),(6,5)]
  | 21 => some [(7,4),(8,4)]
  | 22 => some [(0,0),(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2)]
  | 27 => some [(5,3)]
  | 28 => some [(5,5)]
  | 29 => some [(7,0)]
  | 30 => some [(4,1),(8,1)]
  | 31 => some [(0,2),(1,5)]
  | 32 => some [(1,1),(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(1,4)]
  | 40 => some [(1,3),(3,3),(5,3),(7,3)]
  | 41 => some [(5,2),(5,5)]
  | 42 => some [(7,0),(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(3,0)]
  | 46 => some [(2,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(6,0)]
  | 51 => some [(0,4),(0,5),(6,2)]
  | 52 => some [(4,4),(5,4),(8,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(8,2)]
  | 61 => some [(4,3),(7,1)]
  | 62 => some [(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(8,2)]
  | 72 => some [(5,0)]
  | 73 => some [(4,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(8,5)]
  | 77 => some [(1,0)]
  | 78 => some [(0,4),(1,2),(6,2)]
  | 79 => some [(5,4),(8,4)]
  | 80 => some [(0,0)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(1,3),(6,3)]
  | 84 => some [(7,2),(8,2)]
  | 85 => some [(4,3),(7,1),(8,1)]
  | 86 => some [(1,5)]
  | 87 => some [(6,1)]
  | 88 => some [(4,1),(8,1)]
  | 89 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root3Node0Domains3_fast_eq : root3Node0Domains3 = expandDomains root3Node0Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root3Node0Domains3 v = expandDomains root3Node0Domains3Fast v from by decide) v
theorem root3Node0Step3Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq (by decide)
theorem root3Node0Step3Narrowing_checked :
    checkNarrowing table65 root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root3Node0Domains2 root3Node0Domains3 (by
      simp only [List.all_cons, List.all_nil, root3Node0Step3Chunk0_0_checked, root3Node0Step3Chunk0_1_checked, root3Node0Step3Chunk0_2_checked, root3Node0Step3Chunk0_3_checked, root3Node0Step3Chunk0_4_checked, root3Node0Step3Chunk0_5_checked, root3Node0Step3Chunk1_0_checked, root3Node0Step3Chunk1_1_checked, root3Node0Step3Chunk1_2_checked, root3Node0Step3Chunk1_3_checked, root3Node0Step3Chunk1_4_checked, root3Node0Step3Chunk1_5_checked, root3Node0Step3Chunk2_0_checked, root3Node0Step3Chunk2_1_checked, root3Node0Step3Chunk2_2_checked, root3Node0Step3Chunk2_3_checked, root3Node0Step3Chunk2_4_checked, root3Node0Step3Chunk2_5_checked, root3Node0Step3Chunk3_0_checked, root3Node0Step3Chunk3_1_checked, root3Node0Step3Chunk3_2_checked, root3Node0Step3Chunk3_3_checked, root3Node0Step3Chunk3_4_checked, root3Node0Step3Chunk3_5_checked, root3Node0Step3Chunk4_0_checked, root3Node0Step3Chunk4_1_checked, root3Node0Step3Chunk4_2_checked, root3Node0Step3Chunk4_3_checked, root3Node0Step3Chunk4_4_checked, root3Node0Step3Chunk4_5_checked, root3Node0Step3Chunk5_0_checked, root3Node0Step3Chunk5_1_checked, root3Node0Step3Chunk5_2_checked, root3Node0Step3Chunk5_3_checked, root3Node0Step3Chunk5_4_checked, root3Node0Step3Chunk5_5_checked, root3Node0Step3Chunk6_0_checked, root3Node0Step3Chunk6_1_checked, root3Node0Step3Chunk6_2_checked, root3Node0Step3Chunk6_3_checked, root3Node0Step3Chunk6_4_checked, root3Node0Step3Chunk6_5_checked, root3Node0Step3Chunk7_0_checked, root3Node0Step3Chunk7_1_checked, root3Node0Step3Chunk7_2_checked, root3Node0Step3Chunk7_3_checked, root3Node0Step3Chunk7_4_checked, root3Node0Step3Chunk7_5_checked, root3Node0Step3Chunk8_0_checked, root3Node0Step3Chunk8_1_checked, root3Node0Step3Chunk8_2_checked, root3Node0Step3Chunk8_3_checked, root3Node0Step3Chunk8_4_checked, root3Node0Step3Chunk8_5_checked, Bool.true_and])
theorem root3Node0Step3_checked :
    checkReplacement table65 root3Node0Domains2 root3Node0Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root3Node0Domains2 root3Node0Domains3
    root3Node0Domains2Fast root3Node0Domains3Fast
    root3Node0Domains2_fast_eq root3Node0Domains3_fast_eq
    root3Node0Step3Narrowing_checked (by decide)
def root3Node0Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,4),(7,4)]
  | 1 => [(1,3)]
  | 2 => [(5,2),(8,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3)]
  | 5 => [(4,2),(5,2),(8,2)]
  | 6 => [(7,1),(8,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(6,4)]
  | 11 => [(1,2)]
  | 12 => [(7,4),(8,4)]
  | 13 => [(5,0),(5,3),(8,3)]
  | 14 => [(4,5),(8,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(0,3)]
  | 19 => [(8,1)]
  | 20 => [(1,5),(6,5)]
  | 21 => [(7,4),(8,4)]
  | 22 => [(0,0),(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(4,2)]
  | 27 => [(5,3)]
  | 28 => [(5,5)]
  | 29 => [(7,0)]
  | 30 => [(4,1),(8,1)]
  | 31 => [(0,2),(1,5)]
  | 32 => [(1,1),(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(1,4)]
  | 40 => [(1,3),(3,3),(5,3),(7,3)]
  | 41 => [(5,2),(5,5)]
  | 42 => [(7,0),(8,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5)]
  | 45 => [(3,0)]
  | 46 => [(2,5)]
  | 47 => [(6,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(6,0)]
  | 51 => [(0,4),(0,5),(6,2)]
  | 52 => [(4,4),(5,4),(8,4)]
  | 53 => [(1,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(4,0)]
  | 59 => [(7,3)]
  | 60 => [(8,2)]
  | 61 => [(4,3),(7,1)]
  | 62 => [(7,5)]
  | 63 => [(6,0)]
  | 64 => [(7,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(5,1)]
  | 68 => [(0,1)]
  | 69 => [(6,2)]
  | 70 => [(1,3),(7,3)]
  | 71 => [(8,2)]
  | 72 => [(5,0)]
  | 73 => [(4,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(8,5)]
  | 77 => [(1,0)]
  | 78 => [(0,4),(1,2),(6,2)]
  | 79 => [(5,4),(8,4)]
  | 80 => [(0,0)]
  | 81 => [(7,2)]
  | 82 => [(7,4)]
  | 83 => [(1,3),(6,3)]
  | 84 => [(7,2),(8,2)]
  | 85 => [(4,3),(7,1),(8,1)]
  | 86 => [(1,5)]
  | 87 => [(6,1)]
  | 88 => [(4,1),(8,1)]
  | 89 => [(0,2),(6,5)]
  | _ => [(0,4),(1,1)]
def root3Node0Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4),(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2),(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(4,2),(5,2),(8,2)]
  | 6 => some [(7,1),(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(7,4),(8,4)]
  | 13 => some [(5,0),(5,3),(8,3)]
  | 14 => some [(4,5),(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3)]
  | 19 => some [(8,1)]
  | 20 => some [(1,5),(6,5)]
  | 21 => some [(7,4),(8,4)]
  | 22 => some [(0,0),(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2)]
  | 27 => some [(5,3)]
  | 28 => some [(5,5)]
  | 29 => some [(7,0)]
  | 30 => some [(4,1),(8,1)]
  | 31 => some [(0,2),(1,5)]
  | 32 => some [(1,1),(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(1,4)]
  | 40 => some [(1,3),(3,3),(5,3),(7,3)]
  | 41 => some [(5,2),(5,5)]
  | 42 => some [(7,0),(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(3,0)]
  | 46 => some [(2,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(6,0)]
  | 51 => some [(0,4),(0,5),(6,2)]
  | 52 => some [(4,4),(5,4),(8,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(8,2)]
  | 61 => some [(4,3),(7,1)]
  | 62 => some [(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(8,2)]
  | 72 => some [(5,0)]
  | 73 => some [(4,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(8,5)]
  | 77 => some [(1,0)]
  | 78 => some [(0,4),(1,2),(6,2)]
  | 79 => some [(5,4),(8,4)]
  | 80 => some [(0,0)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(1,3),(6,3)]
  | 84 => some [(7,2),(8,2)]
  | 85 => some [(4,3),(7,1),(8,1)]
  | 86 => some [(1,5)]
  | 87 => some [(6,1)]
  | 88 => some [(4,1),(8,1)]
  | 89 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root3Node0Domains4_fast_eq : root3Node0Domains4 = expandDomains root3Node0Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root3Node0Domains4 v = expandDomains root3Node0Domains4Fast v from by decide) v
theorem root3Node0Step4Chunk0_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_0⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk0_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_1⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk0_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_2⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk0_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_3⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk0_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_4⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk0_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_5⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk1_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_0⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk1_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_1⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk1_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_2⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk1_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_3⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk1_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_4⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk1_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_5⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk2_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_0⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk2_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_1⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk2_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_2⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk2_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_3⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk2_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_4⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk2_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_5⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk3_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_0⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk3_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_1⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk3_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_2⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk3_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_3⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk3_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_4⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk3_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_5⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk4_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_0⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk4_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_1⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk4_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_2⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk4_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_3⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk4_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_4⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk4_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_5⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk5_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_0⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk5_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_1⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk5_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_2⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk5_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_3⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk5_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_4⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk5_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_5⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk6_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_0⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk6_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_1⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk6_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_2⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk6_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_3⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk6_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_4⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk6_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_5⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk7_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_0⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk7_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_1⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk7_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_2⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk7_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_3⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk7_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_4⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk7_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_5⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk8_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_0⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk8_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_1⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk8_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_2⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk8_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_3⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk8_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_4⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk8_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_5⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Narrowing_checked :
    checkNarrowing table1 root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_flatten table1Scope [table1Rows0_0,table1Rows0_1,table1Rows0_2,table1Rows0_3,table1Rows0_4,table1Rows0_5,table1Rows1_0,table1Rows1_1,table1Rows1_2,table1Rows1_3,table1Rows1_4,table1Rows1_5,table1Rows2_0,table1Rows2_1,table1Rows2_2,table1Rows2_3,table1Rows2_4,table1Rows2_5,table1Rows3_0,table1Rows3_1,table1Rows3_2,table1Rows3_3,table1Rows3_4,table1Rows3_5,table1Rows4_0,table1Rows4_1,table1Rows4_2,table1Rows4_3,table1Rows4_4,table1Rows4_5,table1Rows5_0,table1Rows5_1,table1Rows5_2,table1Rows5_3,table1Rows5_4,table1Rows5_5,table1Rows6_0,table1Rows6_1,table1Rows6_2,table1Rows6_3,table1Rows6_4,table1Rows6_5,table1Rows7_0,table1Rows7_1,table1Rows7_2,table1Rows7_3,table1Rows7_4,table1Rows7_5,table1Rows8_0,table1Rows8_1,table1Rows8_2,table1Rows8_3,table1Rows8_4,table1Rows8_5]
    root3Node0Domains3 root3Node0Domains4 (by
      simp only [List.all_cons, List.all_nil, root3Node0Step4Chunk0_0_checked, root3Node0Step4Chunk0_1_checked, root3Node0Step4Chunk0_2_checked, root3Node0Step4Chunk0_3_checked, root3Node0Step4Chunk0_4_checked, root3Node0Step4Chunk0_5_checked, root3Node0Step4Chunk1_0_checked, root3Node0Step4Chunk1_1_checked, root3Node0Step4Chunk1_2_checked, root3Node0Step4Chunk1_3_checked, root3Node0Step4Chunk1_4_checked, root3Node0Step4Chunk1_5_checked, root3Node0Step4Chunk2_0_checked, root3Node0Step4Chunk2_1_checked, root3Node0Step4Chunk2_2_checked, root3Node0Step4Chunk2_3_checked, root3Node0Step4Chunk2_4_checked, root3Node0Step4Chunk2_5_checked, root3Node0Step4Chunk3_0_checked, root3Node0Step4Chunk3_1_checked, root3Node0Step4Chunk3_2_checked, root3Node0Step4Chunk3_3_checked, root3Node0Step4Chunk3_4_checked, root3Node0Step4Chunk3_5_checked, root3Node0Step4Chunk4_0_checked, root3Node0Step4Chunk4_1_checked, root3Node0Step4Chunk4_2_checked, root3Node0Step4Chunk4_3_checked, root3Node0Step4Chunk4_4_checked, root3Node0Step4Chunk4_5_checked, root3Node0Step4Chunk5_0_checked, root3Node0Step4Chunk5_1_checked, root3Node0Step4Chunk5_2_checked, root3Node0Step4Chunk5_3_checked, root3Node0Step4Chunk5_4_checked, root3Node0Step4Chunk5_5_checked, root3Node0Step4Chunk6_0_checked, root3Node0Step4Chunk6_1_checked, root3Node0Step4Chunk6_2_checked, root3Node0Step4Chunk6_3_checked, root3Node0Step4Chunk6_4_checked, root3Node0Step4Chunk6_5_checked, root3Node0Step4Chunk7_0_checked, root3Node0Step4Chunk7_1_checked, root3Node0Step4Chunk7_2_checked, root3Node0Step4Chunk7_3_checked, root3Node0Step4Chunk7_4_checked, root3Node0Step4Chunk7_5_checked, root3Node0Step4Chunk8_0_checked, root3Node0Step4Chunk8_1_checked, root3Node0Step4Chunk8_2_checked, root3Node0Step4Chunk8_3_checked, root3Node0Step4Chunk8_4_checked, root3Node0Step4Chunk8_5_checked, Bool.true_and])
theorem root3Node0Step4_checked :
    checkReplacement table1 root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq
    root3Node0Step4Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
