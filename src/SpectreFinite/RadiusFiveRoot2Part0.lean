module

public import SpectreFinite.RadiusFiveRoot2Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable36
public import SpectreFinite.RadiusFiveTable45
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root2Node0Domains0 : Domains 91 State := domains (2,0)
def root2Node0Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 45 => some [(2,0)]
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
theorem root2Node0Domains0_fast_eq : root2Node0Domains0 = expandDomains root2Node0Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root2Node0Domains0 v = expandDomains root2Node0Domains0Fast v from by decide) v
def root2Node0Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => stateChoices
  | 2 => stateChoices
  | 3 => stateChoices
  | 4 => stateChoices
  | 5 => stateChoices
  | 6 => stateChoices
  | 7 => [(7,5),(8,5)]
  | 8 => [(1,0),(6,0)]
  | 9 => [(7,1)]
  | 10 => [(1,5)]
  | 11 => [(6,1)]
  | 12 => stateChoices
  | 13 => stateChoices
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => stateChoices
  | 21 => stateChoices
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => stateChoices
  | 30 => stateChoices
  | 31 => [(5,5)]
  | 32 => [(7,0)]
  | 33 => [(4,3)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => stateChoices
  | 40 => stateChoices
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(1,4)]
  | 44 => [(0,5)]
  | 45 => [(2,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(8,0)]
  | 49 => [(7,3),(8,3)]
  | 50 => stateChoices
  | 51 => stateChoices
  | 52 => [(7,1)]
  | 53 => [(7,5)]
  | 54 => [(6,0)]
  | 55 => [(3,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(1,4),(6,4)]
  | 60 => stateChoices
  | 61 => stateChoices
  | 62 => [(7,3)]
  | 63 => [(8,2)]
  | 64 => [(5,0)]
  | 65 => [(4,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => stateChoices
  | 70 => stateChoices
  | 71 => [(1,2),(6,2)]
  | 72 => [(8,4)]
  | 73 => [(0,0)]
  | 74 => [(7,2)]
  | 75 => [(4,0)]
  | 76 => [(7,3)]
  | 77 => stateChoices
  | 78 => stateChoices
  | 79 => [(7,1),(8,1)]
  | 80 => [(1,5)]
  | 81 => [(6,1)]
  | 82 => [(5,1)]
  | 83 => [(0,1)]
  | 84 => stateChoices
  | 85 => stateChoices
  | 86 => stateChoices
  | 87 => stateChoices
  | 88 => stateChoices
  | 89 => stateChoices
  | _ => stateChoices
def root2Node0Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => none
  | 1 => none
  | 2 => none
  | 3 => none
  | 4 => none
  | 5 => none
  | 6 => none
  | 7 => some [(7,5),(8,5)]
  | 8 => some [(1,0),(6,0)]
  | 9 => some [(7,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => none
  | 13 => none
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => none
  | 21 => none
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => none
  | 30 => none
  | 31 => some [(5,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => none
  | 40 => none
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(1,4)]
  | 44 => some [(0,5)]
  | 45 => some [(2,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3),(8,3)]
  | 50 => none
  | 51 => none
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(6,0)]
  | 55 => some [(3,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(1,4),(6,4)]
  | 60 => none
  | 61 => none
  | 62 => some [(7,3)]
  | 63 => some [(8,2)]
  | 64 => some [(5,0)]
  | 65 => some [(4,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => none
  | 70 => none
  | 71 => some [(1,2),(6,2)]
  | 72 => some [(8,4)]
  | 73 => some [(0,0)]
  | 74 => some [(7,2)]
  | 75 => some [(4,0)]
  | 76 => some [(7,3)]
  | 77 => none
  | 78 => none
  | 79 => some [(7,1),(8,1)]
  | 80 => some [(1,5)]
  | 81 => some [(6,1)]
  | 82 => some [(5,1)]
  | 83 => some [(0,1)]
  | 84 => none
  | 85 => none
  | 86 => none
  | 87 => none
  | 88 => none
  | 89 => none
  | _ => none
theorem root2Node0Domains1_fast_eq : root2Node0Domains1 = expandDomains root2Node0Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root2Node0Domains1 v = expandDomains root2Node0Domains1Fast v from by decide) v
theorem root2Node0Step1Chunk0_0_checked :
    checkNarrowing ⟨table45Scope, table45Rows0_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk0_1_checked :
    checkNarrowing ⟨table45Scope, table45Rows0_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk0_2_checked :
    checkNarrowing ⟨table45Scope, table45Rows0_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk0_3_checked :
    checkNarrowing ⟨table45Scope, table45Rows0_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk0_4_checked :
    checkNarrowing ⟨table45Scope, table45Rows0_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk0_5_checked :
    checkNarrowing ⟨table45Scope, table45Rows0_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk1_0_checked :
    checkNarrowing ⟨table45Scope, table45Rows1_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk1_1_checked :
    checkNarrowing ⟨table45Scope, table45Rows1_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk1_2_checked :
    checkNarrowing ⟨table45Scope, table45Rows1_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk1_3_checked :
    checkNarrowing ⟨table45Scope, table45Rows1_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk1_4_checked :
    checkNarrowing ⟨table45Scope, table45Rows1_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk1_5_checked :
    checkNarrowing ⟨table45Scope, table45Rows1_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk2_0_checked :
    checkNarrowing ⟨table45Scope, table45Rows2_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk2_1_checked :
    checkNarrowing ⟨table45Scope, table45Rows2_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk2_2_checked :
    checkNarrowing ⟨table45Scope, table45Rows2_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk2_3_checked :
    checkNarrowing ⟨table45Scope, table45Rows2_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk2_4_checked :
    checkNarrowing ⟨table45Scope, table45Rows2_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk2_5_checked :
    checkNarrowing ⟨table45Scope, table45Rows2_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk3_0_checked :
    checkNarrowing ⟨table45Scope, table45Rows3_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk3_1_checked :
    checkNarrowing ⟨table45Scope, table45Rows3_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk3_2_checked :
    checkNarrowing ⟨table45Scope, table45Rows3_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk3_3_checked :
    checkNarrowing ⟨table45Scope, table45Rows3_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk3_4_checked :
    checkNarrowing ⟨table45Scope, table45Rows3_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk3_5_checked :
    checkNarrowing ⟨table45Scope, table45Rows3_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk4_0_checked :
    checkNarrowing ⟨table45Scope, table45Rows4_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk4_1_checked :
    checkNarrowing ⟨table45Scope, table45Rows4_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk4_2_checked :
    checkNarrowing ⟨table45Scope, table45Rows4_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk4_3_checked :
    checkNarrowing ⟨table45Scope, table45Rows4_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk4_4_checked :
    checkNarrowing ⟨table45Scope, table45Rows4_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk4_5_checked :
    checkNarrowing ⟨table45Scope, table45Rows4_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk5_0_checked :
    checkNarrowing ⟨table45Scope, table45Rows5_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk5_1_checked :
    checkNarrowing ⟨table45Scope, table45Rows5_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk5_2_checked :
    checkNarrowing ⟨table45Scope, table45Rows5_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk5_3_checked :
    checkNarrowing ⟨table45Scope, table45Rows5_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk5_4_checked :
    checkNarrowing ⟨table45Scope, table45Rows5_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk5_5_checked :
    checkNarrowing ⟨table45Scope, table45Rows5_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk6_0_checked :
    checkNarrowing ⟨table45Scope, table45Rows6_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk6_1_checked :
    checkNarrowing ⟨table45Scope, table45Rows6_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk6_2_checked :
    checkNarrowing ⟨table45Scope, table45Rows6_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk6_3_checked :
    checkNarrowing ⟨table45Scope, table45Rows6_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk6_4_checked :
    checkNarrowing ⟨table45Scope, table45Rows6_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk6_5_checked :
    checkNarrowing ⟨table45Scope, table45Rows6_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk7_0_checked :
    checkNarrowing ⟨table45Scope, table45Rows7_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk7_1_checked :
    checkNarrowing ⟨table45Scope, table45Rows7_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk7_2_checked :
    checkNarrowing ⟨table45Scope, table45Rows7_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk7_3_checked :
    checkNarrowing ⟨table45Scope, table45Rows7_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk7_4_checked :
    checkNarrowing ⟨table45Scope, table45Rows7_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk7_5_checked :
    checkNarrowing ⟨table45Scope, table45Rows7_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk8_0_checked :
    checkNarrowing ⟨table45Scope, table45Rows8_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk8_1_checked :
    checkNarrowing ⟨table45Scope, table45Rows8_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk8_2_checked :
    checkNarrowing ⟨table45Scope, table45Rows8_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk8_3_checked :
    checkNarrowing ⟨table45Scope, table45Rows8_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk8_4_checked :
    checkNarrowing ⟨table45Scope, table45Rows8_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk8_5_checked :
    checkNarrowing ⟨table45Scope, table45Rows8_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Narrowing_checked :
    checkNarrowing table45 root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_flatten table45Scope [table45Rows0_0,table45Rows0_1,table45Rows0_2,table45Rows0_3,table45Rows0_4,table45Rows0_5,table45Rows1_0,table45Rows1_1,table45Rows1_2,table45Rows1_3,table45Rows1_4,table45Rows1_5,table45Rows2_0,table45Rows2_1,table45Rows2_2,table45Rows2_3,table45Rows2_4,table45Rows2_5,table45Rows3_0,table45Rows3_1,table45Rows3_2,table45Rows3_3,table45Rows3_4,table45Rows3_5,table45Rows4_0,table45Rows4_1,table45Rows4_2,table45Rows4_3,table45Rows4_4,table45Rows4_5,table45Rows5_0,table45Rows5_1,table45Rows5_2,table45Rows5_3,table45Rows5_4,table45Rows5_5,table45Rows6_0,table45Rows6_1,table45Rows6_2,table45Rows6_3,table45Rows6_4,table45Rows6_5,table45Rows7_0,table45Rows7_1,table45Rows7_2,table45Rows7_3,table45Rows7_4,table45Rows7_5,table45Rows8_0,table45Rows8_1,table45Rows8_2,table45Rows8_3,table45Rows8_4,table45Rows8_5]
    root2Node0Domains0 root2Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root2Node0Step1Chunk0_0_checked, root2Node0Step1Chunk0_1_checked, root2Node0Step1Chunk0_2_checked, root2Node0Step1Chunk0_3_checked, root2Node0Step1Chunk0_4_checked, root2Node0Step1Chunk0_5_checked, root2Node0Step1Chunk1_0_checked, root2Node0Step1Chunk1_1_checked, root2Node0Step1Chunk1_2_checked, root2Node0Step1Chunk1_3_checked, root2Node0Step1Chunk1_4_checked, root2Node0Step1Chunk1_5_checked, root2Node0Step1Chunk2_0_checked, root2Node0Step1Chunk2_1_checked, root2Node0Step1Chunk2_2_checked, root2Node0Step1Chunk2_3_checked, root2Node0Step1Chunk2_4_checked, root2Node0Step1Chunk2_5_checked, root2Node0Step1Chunk3_0_checked, root2Node0Step1Chunk3_1_checked, root2Node0Step1Chunk3_2_checked, root2Node0Step1Chunk3_3_checked, root2Node0Step1Chunk3_4_checked, root2Node0Step1Chunk3_5_checked, root2Node0Step1Chunk4_0_checked, root2Node0Step1Chunk4_1_checked, root2Node0Step1Chunk4_2_checked, root2Node0Step1Chunk4_3_checked, root2Node0Step1Chunk4_4_checked, root2Node0Step1Chunk4_5_checked, root2Node0Step1Chunk5_0_checked, root2Node0Step1Chunk5_1_checked, root2Node0Step1Chunk5_2_checked, root2Node0Step1Chunk5_3_checked, root2Node0Step1Chunk5_4_checked, root2Node0Step1Chunk5_5_checked, root2Node0Step1Chunk6_0_checked, root2Node0Step1Chunk6_1_checked, root2Node0Step1Chunk6_2_checked, root2Node0Step1Chunk6_3_checked, root2Node0Step1Chunk6_4_checked, root2Node0Step1Chunk6_5_checked, root2Node0Step1Chunk7_0_checked, root2Node0Step1Chunk7_1_checked, root2Node0Step1Chunk7_2_checked, root2Node0Step1Chunk7_3_checked, root2Node0Step1Chunk7_4_checked, root2Node0Step1Chunk7_5_checked, root2Node0Step1Chunk8_0_checked, root2Node0Step1Chunk8_1_checked, root2Node0Step1Chunk8_2_checked, root2Node0Step1Chunk8_3_checked, root2Node0Step1Chunk8_4_checked, root2Node0Step1Chunk8_5_checked, Bool.true_and])
theorem root2Node0Step1_checked :
    checkReplacement table45 root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq
    root2Node0Step1Narrowing_checked (by decide)
def root2Node0Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => stateChoices
  | 2 => stateChoices
  | 3 => stateChoices
  | 4 => stateChoices
  | 5 => stateChoices
  | 6 => stateChoices
  | 7 => [(7,5),(8,5)]
  | 8 => [(1,0),(6,0)]
  | 9 => [(7,1)]
  | 10 => [(1,5)]
  | 11 => [(6,1)]
  | 12 => stateChoices
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => stateChoices
  | 21 => [(8,1)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => stateChoices
  | 30 => [(5,3),(8,3)]
  | 31 => [(5,5)]
  | 32 => [(7,0)]
  | 33 => [(4,3)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => stateChoices
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(1,4)]
  | 44 => [(0,5)]
  | 45 => [(2,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(8,0)]
  | 49 => [(7,3),(8,3)]
  | 50 => stateChoices
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(7,5)]
  | 54 => [(6,0)]
  | 55 => [(3,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(1,4),(6,4)]
  | 60 => stateChoices
  | 61 => [(4,0),(8,0)]
  | 62 => [(7,3)]
  | 63 => [(8,2)]
  | 64 => [(5,0)]
  | 65 => [(4,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => stateChoices
  | 70 => [(0,1),(6,4)]
  | 71 => [(1,2),(6,2)]
  | 72 => [(8,4)]
  | 73 => [(0,0)]
  | 74 => [(7,2)]
  | 75 => [(4,0)]
  | 76 => [(7,3)]
  | 77 => stateChoices
  | 78 => [(0,3),(1,0)]
  | 79 => [(7,1),(8,1)]
  | 80 => [(1,5)]
  | 81 => [(6,1)]
  | 82 => [(5,1)]
  | 83 => [(0,1)]
  | 84 => stateChoices
  | 85 => [(5,0),(5,3)]
  | 86 => [(4,5),(5,5),(8,5)]
  | 87 => [(7,0)]
  | 88 => [(8,3)]
  | 89 => stateChoices
  | _ => stateChoices
def root2Node0Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => none
  | 1 => none
  | 2 => none
  | 3 => none
  | 4 => none
  | 5 => none
  | 6 => none
  | 7 => some [(7,5),(8,5)]
  | 8 => some [(1,0),(6,0)]
  | 9 => some [(7,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => none
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => none
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => none
  | 30 => some [(5,3),(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => none
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(1,4)]
  | 44 => some [(0,5)]
  | 45 => some [(2,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3),(8,3)]
  | 50 => none
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(6,0)]
  | 55 => some [(3,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(1,4),(6,4)]
  | 60 => none
  | 61 => some [(4,0),(8,0)]
  | 62 => some [(7,3)]
  | 63 => some [(8,2)]
  | 64 => some [(5,0)]
  | 65 => some [(4,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => none
  | 70 => some [(0,1),(6,4)]
  | 71 => some [(1,2),(6,2)]
  | 72 => some [(8,4)]
  | 73 => some [(0,0)]
  | 74 => some [(7,2)]
  | 75 => some [(4,0)]
  | 76 => some [(7,3)]
  | 77 => none
  | 78 => some [(0,3),(1,0)]
  | 79 => some [(7,1),(8,1)]
  | 80 => some [(1,5)]
  | 81 => some [(6,1)]
  | 82 => some [(5,1)]
  | 83 => some [(0,1)]
  | 84 => none
  | 85 => some [(5,0),(5,3)]
  | 86 => some [(4,5),(5,5),(8,5)]
  | 87 => some [(7,0)]
  | 88 => some [(8,3)]
  | 89 => none
  | _ => none
theorem root2Node0Domains2_fast_eq : root2Node0Domains2 = expandDomains root2Node0Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root2Node0Domains2 v = expandDomains root2Node0Domains2Fast v from by decide) v
theorem root2Node0Step2Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Narrowing_checked :
    checkNarrowing table54 root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root2Node0Domains1 root2Node0Domains2 (by
      simp only [List.all_cons, List.all_nil, root2Node0Step2Chunk0_0_checked, root2Node0Step2Chunk0_1_checked, root2Node0Step2Chunk0_2_checked, root2Node0Step2Chunk0_3_checked, root2Node0Step2Chunk0_4_checked, root2Node0Step2Chunk0_5_checked, root2Node0Step2Chunk1_0_checked, root2Node0Step2Chunk1_1_checked, root2Node0Step2Chunk1_2_checked, root2Node0Step2Chunk1_3_checked, root2Node0Step2Chunk1_4_checked, root2Node0Step2Chunk1_5_checked, root2Node0Step2Chunk2_0_checked, root2Node0Step2Chunk2_1_checked, root2Node0Step2Chunk2_2_checked, root2Node0Step2Chunk2_3_checked, root2Node0Step2Chunk2_4_checked, root2Node0Step2Chunk2_5_checked, root2Node0Step2Chunk3_0_checked, root2Node0Step2Chunk3_1_checked, root2Node0Step2Chunk3_2_checked, root2Node0Step2Chunk3_3_checked, root2Node0Step2Chunk3_4_checked, root2Node0Step2Chunk3_5_checked, root2Node0Step2Chunk4_0_checked, root2Node0Step2Chunk4_1_checked, root2Node0Step2Chunk4_2_checked, root2Node0Step2Chunk4_3_checked, root2Node0Step2Chunk4_4_checked, root2Node0Step2Chunk4_5_checked, root2Node0Step2Chunk5_0_checked, root2Node0Step2Chunk5_1_checked, root2Node0Step2Chunk5_2_checked, root2Node0Step2Chunk5_3_checked, root2Node0Step2Chunk5_4_checked, root2Node0Step2Chunk5_5_checked, root2Node0Step2Chunk6_0_checked, root2Node0Step2Chunk6_1_checked, root2Node0Step2Chunk6_2_checked, root2Node0Step2Chunk6_3_checked, root2Node0Step2Chunk6_4_checked, root2Node0Step2Chunk6_5_checked, root2Node0Step2Chunk7_0_checked, root2Node0Step2Chunk7_1_checked, root2Node0Step2Chunk7_2_checked, root2Node0Step2Chunk7_3_checked, root2Node0Step2Chunk7_4_checked, root2Node0Step2Chunk7_5_checked, root2Node0Step2Chunk8_0_checked, root2Node0Step2Chunk8_1_checked, root2Node0Step2Chunk8_2_checked, root2Node0Step2Chunk8_3_checked, root2Node0Step2Chunk8_4_checked, root2Node0Step2Chunk8_5_checked, Bool.true_and])
theorem root2Node0Step2_checked :
    checkReplacement table54 root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq
    root2Node0Step2Narrowing_checked (by decide)
def root2Node0Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => stateChoices
  | 2 => [(0,5),(6,2)]
  | 3 => [(4,4),(8,4)]
  | 4 => [(0,0)]
  | 5 => [(3,2),(7,2)]
  | 6 => stateChoices
  | 7 => [(7,5),(8,5)]
  | 8 => [(1,0),(6,0)]
  | 9 => [(7,1)]
  | 10 => [(1,5)]
  | 11 => [(6,1)]
  | 12 => [(5,1),(8,1)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(8,1)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => [(7,2)]
  | 30 => [(5,3),(8,3)]
  | 31 => [(5,5)]
  | 32 => [(7,0)]
  | 33 => [(4,3)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => [(4,1),(5,1),(8,1)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(1,4)]
  | 44 => [(0,5)]
  | 45 => [(2,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(8,0)]
  | 49 => [(7,3),(8,3)]
  | 50 => [(5,2),(5,5)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(7,5)]
  | 54 => [(6,0)]
  | 55 => [(3,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(1,4),(6,4)]
  | 60 => [(0,5),(1,2)]
  | 61 => [(4,0),(8,0)]
  | 62 => [(7,3)]
  | 63 => [(8,2)]
  | 64 => [(5,0)]
  | 65 => [(4,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(0,3),(6,0)]
  | 70 => [(0,1),(6,4)]
  | 71 => [(1,2),(6,2)]
  | 72 => [(8,4)]
  | 73 => [(0,0)]
  | 74 => [(7,2)]
  | 75 => [(4,0)]
  | 76 => [(7,3)]
  | 77 => [(4,2),(8,2)]
  | 78 => [(0,3),(1,0)]
  | 79 => [(7,1),(8,1)]
  | 80 => [(1,5)]
  | 81 => [(6,1)]
  | 82 => [(5,1)]
  | 83 => [(0,1)]
  | 84 => stateChoices
  | 85 => [(5,0),(5,3)]
  | 86 => [(4,5),(5,5),(8,5)]
  | 87 => [(7,0)]
  | 88 => [(8,3)]
  | 89 => stateChoices
  | _ => stateChoices
def root2Node0Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => none
  | 1 => none
  | 2 => some [(0,5),(6,2)]
  | 3 => some [(4,4),(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(3,2),(7,2)]
  | 6 => none
  | 7 => some [(7,5),(8,5)]
  | 8 => some [(1,0),(6,0)]
  | 9 => some [(7,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1),(8,1)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(5,3),(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(4,1),(5,1),(8,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(1,4)]
  | 44 => some [(0,5)]
  | 45 => some [(2,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3),(8,3)]
  | 50 => some [(5,2),(5,5)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(6,0)]
  | 55 => some [(3,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(1,4),(6,4)]
  | 60 => some [(0,5),(1,2)]
  | 61 => some [(4,0),(8,0)]
  | 62 => some [(7,3)]
  | 63 => some [(8,2)]
  | 64 => some [(5,0)]
  | 65 => some [(4,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3),(6,0)]
  | 70 => some [(0,1),(6,4)]
  | 71 => some [(1,2),(6,2)]
  | 72 => some [(8,4)]
  | 73 => some [(0,0)]
  | 74 => some [(7,2)]
  | 75 => some [(4,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2),(8,2)]
  | 78 => some [(0,3),(1,0)]
  | 79 => some [(7,1),(8,1)]
  | 80 => some [(1,5)]
  | 81 => some [(6,1)]
  | 82 => some [(5,1)]
  | 83 => some [(0,1)]
  | 84 => none
  | 85 => some [(5,0),(5,3)]
  | 86 => some [(4,5),(5,5),(8,5)]
  | 87 => some [(7,0)]
  | 88 => some [(8,3)]
  | 89 => none
  | _ => none
theorem root2Node0Domains3_fast_eq : root2Node0Domains3 = expandDomains root2Node0Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root2Node0Domains3 v = expandDomains root2Node0Domains3Fast v from by decide) v
theorem root2Node0Step3Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Narrowing_checked :
    checkNarrowing table36 root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root2Node0Domains2 root2Node0Domains3 (by
      simp only [List.all_cons, List.all_nil, root2Node0Step3Chunk0_0_checked, root2Node0Step3Chunk0_1_checked, root2Node0Step3Chunk0_2_checked, root2Node0Step3Chunk0_3_checked, root2Node0Step3Chunk0_4_checked, root2Node0Step3Chunk0_5_checked, root2Node0Step3Chunk1_0_checked, root2Node0Step3Chunk1_1_checked, root2Node0Step3Chunk1_2_checked, root2Node0Step3Chunk1_3_checked, root2Node0Step3Chunk1_4_checked, root2Node0Step3Chunk1_5_checked, root2Node0Step3Chunk2_0_checked, root2Node0Step3Chunk2_1_checked, root2Node0Step3Chunk2_2_checked, root2Node0Step3Chunk2_3_checked, root2Node0Step3Chunk2_4_checked, root2Node0Step3Chunk2_5_checked, root2Node0Step3Chunk3_0_checked, root2Node0Step3Chunk3_1_checked, root2Node0Step3Chunk3_2_checked, root2Node0Step3Chunk3_3_checked, root2Node0Step3Chunk3_4_checked, root2Node0Step3Chunk3_5_checked, root2Node0Step3Chunk4_0_checked, root2Node0Step3Chunk4_1_checked, root2Node0Step3Chunk4_2_checked, root2Node0Step3Chunk4_3_checked, root2Node0Step3Chunk4_4_checked, root2Node0Step3Chunk4_5_checked, root2Node0Step3Chunk5_0_checked, root2Node0Step3Chunk5_1_checked, root2Node0Step3Chunk5_2_checked, root2Node0Step3Chunk5_3_checked, root2Node0Step3Chunk5_4_checked, root2Node0Step3Chunk5_5_checked, root2Node0Step3Chunk6_0_checked, root2Node0Step3Chunk6_1_checked, root2Node0Step3Chunk6_2_checked, root2Node0Step3Chunk6_3_checked, root2Node0Step3Chunk6_4_checked, root2Node0Step3Chunk6_5_checked, root2Node0Step3Chunk7_0_checked, root2Node0Step3Chunk7_1_checked, root2Node0Step3Chunk7_2_checked, root2Node0Step3Chunk7_3_checked, root2Node0Step3Chunk7_4_checked, root2Node0Step3Chunk7_5_checked, root2Node0Step3Chunk8_0_checked, root2Node0Step3Chunk8_1_checked, root2Node0Step3Chunk8_2_checked, root2Node0Step3Chunk8_3_checked, root2Node0Step3Chunk8_4_checked, root2Node0Step3Chunk8_5_checked, Bool.true_and])
theorem root2Node0Step3_checked :
    checkReplacement table36 root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq
    root2Node0Step3Narrowing_checked (by decide)
def root2Node0Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => stateChoices
  | 2 => [(0,5),(6,2)]
  | 3 => [(4,4),(8,4)]
  | 4 => [(0,0)]
  | 5 => [(3,2),(7,2)]
  | 6 => stateChoices
  | 7 => [(7,5),(8,5)]
  | 8 => [(1,0),(6,0)]
  | 9 => [(7,1)]
  | 10 => [(1,5)]
  | 11 => [(6,1)]
  | 12 => [(5,1),(8,1)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(8,1)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => [(7,2)]
  | 30 => [(5,3),(8,3)]
  | 31 => [(5,5)]
  | 32 => [(7,0)]
  | 33 => [(4,3)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => [(4,1),(5,1),(8,1)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(1,4)]
  | 44 => [(0,5)]
  | 45 => [(2,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(8,0)]
  | 49 => [(7,3),(8,3)]
  | 50 => [(5,2),(5,5)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(7,5)]
  | 54 => [(6,0)]
  | 55 => [(3,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(1,4),(6,4)]
  | 60 => [(0,5),(1,2)]
  | 61 => [(4,0),(8,0)]
  | 62 => [(7,3)]
  | 63 => [(8,2)]
  | 64 => [(5,0)]
  | 65 => [(4,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(0,3),(6,0)]
  | 70 => [(0,1),(6,4)]
  | 71 => [(1,2),(6,2)]
  | 72 => [(8,4)]
  | 73 => [(0,0)]
  | 74 => [(7,2)]
  | 75 => [(4,0)]
  | 76 => [(7,3)]
  | 77 => [(4,2),(8,2)]
  | 78 => [(0,3),(1,0)]
  | 79 => [(7,1),(8,1)]
  | 80 => [(1,5)]
  | 81 => [(6,1)]
  | 82 => [(5,1)]
  | 83 => [(0,1)]
  | 84 => [(6,2)]
  | 85 => [(5,0),(5,3)]
  | 86 => [(4,5),(5,5),(8,5)]
  | 87 => [(7,0)]
  | 88 => [(8,3)]
  | 89 => [(5,5),(8,5)]
  | _ => [(1,0)]
def root2Node0Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => none
  | 1 => none
  | 2 => some [(0,5),(6,2)]
  | 3 => some [(4,4),(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(3,2),(7,2)]
  | 6 => none
  | 7 => some [(7,5),(8,5)]
  | 8 => some [(1,0),(6,0)]
  | 9 => some [(7,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1),(8,1)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(5,3),(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(4,1),(5,1),(8,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(1,4)]
  | 44 => some [(0,5)]
  | 45 => some [(2,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3),(8,3)]
  | 50 => some [(5,2),(5,5)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(6,0)]
  | 55 => some [(3,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(1,4),(6,4)]
  | 60 => some [(0,5),(1,2)]
  | 61 => some [(4,0),(8,0)]
  | 62 => some [(7,3)]
  | 63 => some [(8,2)]
  | 64 => some [(5,0)]
  | 65 => some [(4,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3),(6,0)]
  | 70 => some [(0,1),(6,4)]
  | 71 => some [(1,2),(6,2)]
  | 72 => some [(8,4)]
  | 73 => some [(0,0)]
  | 74 => some [(7,2)]
  | 75 => some [(4,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2),(8,2)]
  | 78 => some [(0,3),(1,0)]
  | 79 => some [(7,1),(8,1)]
  | 80 => some [(1,5)]
  | 81 => some [(6,1)]
  | 82 => some [(5,1)]
  | 83 => some [(0,1)]
  | 84 => some [(6,2)]
  | 85 => some [(5,0),(5,3)]
  | 86 => some [(4,5),(5,5),(8,5)]
  | 87 => some [(7,0)]
  | 88 => some [(8,3)]
  | 89 => some [(5,5),(8,5)]
  | _ => some [(1,0)]
theorem root2Node0Domains4_fast_eq : root2Node0Domains4 = expandDomains root2Node0Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root2Node0Domains4 v = expandDomains root2Node0Domains4Fast v from by decide) v
theorem root2Node0Step4Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Narrowing_checked :
    checkNarrowing table56 root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root2Node0Domains3 root2Node0Domains4 (by
      simp only [List.all_cons, List.all_nil, root2Node0Step4Chunk0_0_checked, root2Node0Step4Chunk0_1_checked, root2Node0Step4Chunk0_2_checked, root2Node0Step4Chunk0_3_checked, root2Node0Step4Chunk0_4_checked, root2Node0Step4Chunk0_5_checked, root2Node0Step4Chunk1_0_checked, root2Node0Step4Chunk1_1_checked, root2Node0Step4Chunk1_2_checked, root2Node0Step4Chunk1_3_checked, root2Node0Step4Chunk1_4_checked, root2Node0Step4Chunk1_5_checked, root2Node0Step4Chunk2_0_checked, root2Node0Step4Chunk2_1_checked, root2Node0Step4Chunk2_2_checked, root2Node0Step4Chunk2_3_checked, root2Node0Step4Chunk2_4_checked, root2Node0Step4Chunk2_5_checked, root2Node0Step4Chunk3_0_checked, root2Node0Step4Chunk3_1_checked, root2Node0Step4Chunk3_2_checked, root2Node0Step4Chunk3_3_checked, root2Node0Step4Chunk3_4_checked, root2Node0Step4Chunk3_5_checked, root2Node0Step4Chunk4_0_checked, root2Node0Step4Chunk4_1_checked, root2Node0Step4Chunk4_2_checked, root2Node0Step4Chunk4_3_checked, root2Node0Step4Chunk4_4_checked, root2Node0Step4Chunk4_5_checked, root2Node0Step4Chunk5_0_checked, root2Node0Step4Chunk5_1_checked, root2Node0Step4Chunk5_2_checked, root2Node0Step4Chunk5_3_checked, root2Node0Step4Chunk5_4_checked, root2Node0Step4Chunk5_5_checked, root2Node0Step4Chunk6_0_checked, root2Node0Step4Chunk6_1_checked, root2Node0Step4Chunk6_2_checked, root2Node0Step4Chunk6_3_checked, root2Node0Step4Chunk6_4_checked, root2Node0Step4Chunk6_5_checked, root2Node0Step4Chunk7_0_checked, root2Node0Step4Chunk7_1_checked, root2Node0Step4Chunk7_2_checked, root2Node0Step4Chunk7_3_checked, root2Node0Step4Chunk7_4_checked, root2Node0Step4Chunk7_5_checked, root2Node0Step4Chunk8_0_checked, root2Node0Step4Chunk8_1_checked, root2Node0Step4Chunk8_2_checked, root2Node0Step4Chunk8_3_checked, root2Node0Step4Chunk8_4_checked, root2Node0Step4Chunk8_5_checked, Bool.true_and])
theorem root2Node0Step4_checked :
    checkReplacement table56 root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq
    root2Node0Step4Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
