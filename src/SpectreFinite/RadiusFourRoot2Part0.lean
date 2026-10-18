module

public import SpectreFinite.RadiusFourRoot2Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable11
public import SpectreFinite.RadiusFourTable14
public import SpectreFinite.RadiusFourTable16
public import SpectreFinite.RadiusFourTable30
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root2Node0Domains0 : Domains 61 State := domains (2,0)
def root2Node0Domains0Fast (v : Fin 61) : Option (List State) :=
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
  | 30 => some [(2,0)]
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
theorem root2Node0Domains0_fast_eq : root2Node0Domains0 = expandDomains root2Node0Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root2Node0Domains0 v = expandDomains root2Node0Domains0Fast v from by decide) v
def root2Node0Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => stateChoices
  | 2 => stateChoices
  | 3 => stateChoices
  | 4 => stateChoices
  | 5 => stateChoices
  | 6 => [(8,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => stateChoices
  | 11 => stateChoices
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => stateChoices
  | 18 => stateChoices
  | 19 => [(7,0)]
  | 20 => [(4,3)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => stateChoices
  | 26 => stateChoices
  | 27 => [(4,4)]
  | 28 => [(1,4)]
  | 29 => [(0,5)]
  | 30 => [(2,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(8,0)]
  | 34 => stateChoices
  | 35 => stateChoices
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(3,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => stateChoices
  | 43 => stateChoices
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => stateChoices
  | 50 => stateChoices
  | 51 => [(8,4)]
  | 52 => [(0,0)]
  | 53 => [(7,2)]
  | 54 => [(4,0)]
  | 55 => stateChoices
  | 56 => stateChoices
  | 57 => stateChoices
  | 58 => stateChoices
  | 59 => stateChoices
  | _ => stateChoices
def root2Node0Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => none
  | 1 => none
  | 2 => none
  | 3 => none
  | 4 => none
  | 5 => none
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => none
  | 11 => none
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => none
  | 18 => none
  | 19 => some [(7,0)]
  | 20 => some [(4,3)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => none
  | 26 => none
  | 27 => some [(4,4)]
  | 28 => some [(1,4)]
  | 29 => some [(0,5)]
  | 30 => some [(2,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => none
  | 35 => none
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => none
  | 43 => none
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => none
  | 50 => none
  | 51 => some [(8,4)]
  | 52 => some [(0,0)]
  | 53 => some [(7,2)]
  | 54 => some [(4,0)]
  | 55 => none
  | 56 => none
  | 57 => none
  | 58 => none
  | 59 => none
  | _ => none
theorem root2Node0Domains1_fast_eq : root2Node0Domains1 = expandDomains root2Node0Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root2Node0Domains1 v = expandDomains root2Node0Domains1Fast v from by decide) v
theorem root2Node0Step1Chunk0_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk0_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk0_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk0_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk0_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk0_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk1_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk1_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk1_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk1_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk1_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk1_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk2_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk2_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk2_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk2_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk2_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk2_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk3_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk3_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk3_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk3_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk3_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk3_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk4_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk4_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk4_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk4_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk4_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk4_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk5_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk5_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk5_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk5_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk5_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk5_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk6_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk6_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk6_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk6_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk6_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk6_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk7_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk7_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk7_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk7_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk7_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk7_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk8_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_0⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk8_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_1⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk8_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_2⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk8_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_3⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk8_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_4⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1Chunk8_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_5⟩
      root2Node0Domains0 root2Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains0 root2Node0Domains1
    root2Node0Domains0Fast root2Node0Domains1Fast
    root2Node0Domains0_fast_eq root2Node0Domains1_fast_eq (by decide)
theorem root2Node0Step1_checked :
    checkReplacement table30 root2Node0Domains0 root2Node0Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root2Node0Step1Chunk0_0_checked, root2Node0Step1Chunk0_1_checked, root2Node0Step1Chunk0_2_checked, root2Node0Step1Chunk0_3_checked, root2Node0Step1Chunk0_4_checked, root2Node0Step1Chunk0_5_checked, root2Node0Step1Chunk1_0_checked, root2Node0Step1Chunk1_1_checked, root2Node0Step1Chunk1_2_checked, root2Node0Step1Chunk1_3_checked, root2Node0Step1Chunk1_4_checked, root2Node0Step1Chunk1_5_checked, root2Node0Step1Chunk2_0_checked, root2Node0Step1Chunk2_1_checked, root2Node0Step1Chunk2_2_checked, root2Node0Step1Chunk2_3_checked, root2Node0Step1Chunk2_4_checked, root2Node0Step1Chunk2_5_checked, root2Node0Step1Chunk3_0_checked, root2Node0Step1Chunk3_1_checked, root2Node0Step1Chunk3_2_checked, root2Node0Step1Chunk3_3_checked, root2Node0Step1Chunk3_4_checked, root2Node0Step1Chunk3_5_checked, root2Node0Step1Chunk4_0_checked, root2Node0Step1Chunk4_1_checked, root2Node0Step1Chunk4_2_checked, root2Node0Step1Chunk4_3_checked, root2Node0Step1Chunk4_4_checked, root2Node0Step1Chunk4_5_checked, root2Node0Step1Chunk5_0_checked, root2Node0Step1Chunk5_1_checked, root2Node0Step1Chunk5_2_checked, root2Node0Step1Chunk5_3_checked, root2Node0Step1Chunk5_4_checked, root2Node0Step1Chunk5_5_checked, root2Node0Step1Chunk6_0_checked, root2Node0Step1Chunk6_1_checked, root2Node0Step1Chunk6_2_checked, root2Node0Step1Chunk6_3_checked, root2Node0Step1Chunk6_4_checked, root2Node0Step1Chunk6_5_checked, root2Node0Step1Chunk7_0_checked, root2Node0Step1Chunk7_1_checked, root2Node0Step1Chunk7_2_checked, root2Node0Step1Chunk7_3_checked, root2Node0Step1Chunk7_4_checked, root2Node0Step1Chunk7_5_checked, root2Node0Step1Chunk8_0_checked, root2Node0Step1Chunk8_1_checked, root2Node0Step1Chunk8_2_checked, root2Node0Step1Chunk8_3_checked, root2Node0Step1Chunk8_4_checked, root2Node0Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root2Node0Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5),(8,5)]
  | 1 => [(1,0),(6,0)]
  | 2 => [(7,1)]
  | 3 => [(1,5)]
  | 4 => [(6,1)]
  | 5 => [(1,3)]
  | 6 => [(8,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => stateChoices
  | 19 => [(7,0)]
  | 20 => [(4,3)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => stateChoices
  | 26 => stateChoices
  | 27 => [(4,4)]
  | 28 => [(1,4)]
  | 29 => [(0,5)]
  | 30 => [(2,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(8,0)]
  | 34 => stateChoices
  | 35 => stateChoices
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(3,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => stateChoices
  | 43 => stateChoices
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => stateChoices
  | 50 => stateChoices
  | 51 => [(8,4)]
  | 52 => [(0,0)]
  | 53 => [(7,2)]
  | 54 => [(4,0)]
  | 55 => stateChoices
  | 56 => stateChoices
  | 57 => stateChoices
  | 58 => stateChoices
  | 59 => stateChoices
  | _ => stateChoices
def root2Node0Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5),(8,5)]
  | 1 => some [(1,0),(6,0)]
  | 2 => some [(7,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(1,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => none
  | 19 => some [(7,0)]
  | 20 => some [(4,3)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => none
  | 26 => none
  | 27 => some [(4,4)]
  | 28 => some [(1,4)]
  | 29 => some [(0,5)]
  | 30 => some [(2,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => none
  | 35 => none
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => none
  | 43 => none
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => none
  | 50 => none
  | 51 => some [(8,4)]
  | 52 => some [(0,0)]
  | 53 => some [(7,2)]
  | 54 => some [(4,0)]
  | 55 => none
  | 56 => none
  | 57 => none
  | 58 => none
  | 59 => none
  | _ => none
theorem root2Node0Domains2_fast_eq : root2Node0Domains2 = expandDomains root2Node0Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root2Node0Domains2 v = expandDomains root2Node0Domains2Fast v from by decide) v
theorem root2Node0Step2Chunk0_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk0_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk0_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk0_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk0_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk0_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk1_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk1_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk1_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk1_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk1_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk1_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk2_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk2_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk2_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk2_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk2_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk2_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk3_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk3_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk3_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk3_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk3_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk3_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk4_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk4_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk4_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk4_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk4_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk4_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk5_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk5_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk5_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk5_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk5_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk5_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk6_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk6_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk6_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk6_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk6_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk6_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk7_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk7_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk7_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk7_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk7_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk7_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk8_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_0⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk8_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_1⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk8_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_2⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk8_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_3⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk8_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_4⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2Chunk8_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_5⟩
      root2Node0Domains1 root2Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains1 root2Node0Domains2
    root2Node0Domains1Fast root2Node0Domains2Fast
    root2Node0Domains1_fast_eq root2Node0Domains2_fast_eq (by decide)
theorem root2Node0Step2_checked :
    checkReplacement table14 root2Node0Domains1 root2Node0Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root2Node0Step2Chunk0_0_checked, root2Node0Step2Chunk0_1_checked, root2Node0Step2Chunk0_2_checked, root2Node0Step2Chunk0_3_checked, root2Node0Step2Chunk0_4_checked, root2Node0Step2Chunk0_5_checked, root2Node0Step2Chunk1_0_checked, root2Node0Step2Chunk1_1_checked, root2Node0Step2Chunk1_2_checked, root2Node0Step2Chunk1_3_checked, root2Node0Step2Chunk1_4_checked, root2Node0Step2Chunk1_5_checked, root2Node0Step2Chunk2_0_checked, root2Node0Step2Chunk2_1_checked, root2Node0Step2Chunk2_2_checked, root2Node0Step2Chunk2_3_checked, root2Node0Step2Chunk2_4_checked, root2Node0Step2Chunk2_5_checked, root2Node0Step2Chunk3_0_checked, root2Node0Step2Chunk3_1_checked, root2Node0Step2Chunk3_2_checked, root2Node0Step2Chunk3_3_checked, root2Node0Step2Chunk3_4_checked, root2Node0Step2Chunk3_5_checked, root2Node0Step2Chunk4_0_checked, root2Node0Step2Chunk4_1_checked, root2Node0Step2Chunk4_2_checked, root2Node0Step2Chunk4_3_checked, root2Node0Step2Chunk4_4_checked, root2Node0Step2Chunk4_5_checked, root2Node0Step2Chunk5_0_checked, root2Node0Step2Chunk5_1_checked, root2Node0Step2Chunk5_2_checked, root2Node0Step2Chunk5_3_checked, root2Node0Step2Chunk5_4_checked, root2Node0Step2Chunk5_5_checked, root2Node0Step2Chunk6_0_checked, root2Node0Step2Chunk6_1_checked, root2Node0Step2Chunk6_2_checked, root2Node0Step2Chunk6_3_checked, root2Node0Step2Chunk6_4_checked, root2Node0Step2Chunk6_5_checked, root2Node0Step2Chunk7_0_checked, root2Node0Step2Chunk7_1_checked, root2Node0Step2Chunk7_2_checked, root2Node0Step2Chunk7_3_checked, root2Node0Step2Chunk7_4_checked, root2Node0Step2Chunk7_5_checked, root2Node0Step2Chunk8_0_checked, root2Node0Step2Chunk8_1_checked, root2Node0Step2Chunk8_2_checked, root2Node0Step2Chunk8_3_checked, root2Node0Step2Chunk8_4_checked, root2Node0Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root2Node0Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5),(8,5)]
  | 1 => [(1,0),(6,0)]
  | 2 => [(7,1)]
  | 3 => [(1,5)]
  | 4 => [(6,1)]
  | 5 => [(1,3)]
  | 6 => [(8,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => stateChoices
  | 19 => [(7,0)]
  | 20 => [(4,3)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => stateChoices
  | 26 => stateChoices
  | 27 => [(4,4)]
  | 28 => [(1,4)]
  | 29 => [(0,5)]
  | 30 => [(2,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(8,0)]
  | 34 => stateChoices
  | 35 => stateChoices
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(3,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => stateChoices
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(1,2),(6,2)]
  | 51 => [(8,4)]
  | 52 => [(0,0)]
  | 53 => [(7,2)]
  | 54 => [(4,0)]
  | 55 => [(7,3)]
  | 56 => [(7,1),(8,1)]
  | 57 => [(1,5)]
  | 58 => [(6,1)]
  | 59 => [(5,1)]
  | _ => [(0,1)]
def root2Node0Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5),(8,5)]
  | 1 => some [(1,0),(6,0)]
  | 2 => some [(7,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(1,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => none
  | 19 => some [(7,0)]
  | 20 => some [(4,3)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => none
  | 26 => none
  | 27 => some [(4,4)]
  | 28 => some [(1,4)]
  | 29 => some [(0,5)]
  | 30 => some [(2,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => none
  | 35 => none
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => none
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(1,2),(6,2)]
  | 51 => some [(8,4)]
  | 52 => some [(0,0)]
  | 53 => some [(7,2)]
  | 54 => some [(4,0)]
  | 55 => some [(7,3)]
  | 56 => some [(7,1),(8,1)]
  | 57 => some [(1,5)]
  | 58 => some [(6,1)]
  | 59 => some [(5,1)]
  | _ => some [(0,1)]
theorem root2Node0Domains3_fast_eq : root2Node0Domains3 = expandDomains root2Node0Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root2Node0Domains3 v = expandDomains root2Node0Domains3Fast v from by decide) v
theorem root2Node0Step3Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root2Node0Domains2 root2Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains2 root2Node0Domains3
    root2Node0Domains2Fast root2Node0Domains3Fast
    root2Node0Domains2_fast_eq root2Node0Domains3_fast_eq (by decide)
theorem root2Node0Step3_checked :
    checkReplacement table46 root2Node0Domains2 root2Node0Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root2Node0Step3Chunk0_0_checked, root2Node0Step3Chunk0_1_checked, root2Node0Step3Chunk0_2_checked, root2Node0Step3Chunk0_3_checked, root2Node0Step3Chunk0_4_checked, root2Node0Step3Chunk0_5_checked, root2Node0Step3Chunk1_0_checked, root2Node0Step3Chunk1_1_checked, root2Node0Step3Chunk1_2_checked, root2Node0Step3Chunk1_3_checked, root2Node0Step3Chunk1_4_checked, root2Node0Step3Chunk1_5_checked, root2Node0Step3Chunk2_0_checked, root2Node0Step3Chunk2_1_checked, root2Node0Step3Chunk2_2_checked, root2Node0Step3Chunk2_3_checked, root2Node0Step3Chunk2_4_checked, root2Node0Step3Chunk2_5_checked, root2Node0Step3Chunk3_0_checked, root2Node0Step3Chunk3_1_checked, root2Node0Step3Chunk3_2_checked, root2Node0Step3Chunk3_3_checked, root2Node0Step3Chunk3_4_checked, root2Node0Step3Chunk3_5_checked, root2Node0Step3Chunk4_0_checked, root2Node0Step3Chunk4_1_checked, root2Node0Step3Chunk4_2_checked, root2Node0Step3Chunk4_3_checked, root2Node0Step3Chunk4_4_checked, root2Node0Step3Chunk4_5_checked, root2Node0Step3Chunk5_0_checked, root2Node0Step3Chunk5_1_checked, root2Node0Step3Chunk5_2_checked, root2Node0Step3Chunk5_3_checked, root2Node0Step3Chunk5_4_checked, root2Node0Step3Chunk5_5_checked, root2Node0Step3Chunk6_0_checked, root2Node0Step3Chunk6_1_checked, root2Node0Step3Chunk6_2_checked, root2Node0Step3Chunk6_3_checked, root2Node0Step3Chunk6_4_checked, root2Node0Step3Chunk6_5_checked, root2Node0Step3Chunk7_0_checked, root2Node0Step3Chunk7_1_checked, root2Node0Step3Chunk7_2_checked, root2Node0Step3Chunk7_3_checked, root2Node0Step3Chunk7_4_checked, root2Node0Step3Chunk7_5_checked, root2Node0Step3Chunk8_0_checked, root2Node0Step3Chunk8_1_checked, root2Node0Step3Chunk8_2_checked, root2Node0Step3Chunk8_3_checked, root2Node0Step3Chunk8_4_checked, root2Node0Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root2Node0Domains4 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5),(8,5)]
  | 1 => [(1,0),(6,0)]
  | 2 => [(7,1)]
  | 3 => [(1,5)]
  | 4 => [(6,1)]
  | 5 => [(1,3)]
  | 6 => [(8,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => [(5,5)]
  | 19 => [(7,0)]
  | 20 => [(4,3)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => stateChoices
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(1,4)]
  | 29 => [(0,5)]
  | 30 => [(2,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(8,0)]
  | 34 => stateChoices
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(3,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => stateChoices
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(1,2),(6,2)]
  | 51 => [(8,4)]
  | 52 => [(0,0)]
  | 53 => [(7,2)]
  | 54 => [(4,0)]
  | 55 => [(7,3)]
  | 56 => [(7,1),(8,1)]
  | 57 => [(1,5)]
  | 58 => [(6,1)]
  | 59 => [(5,1)]
  | _ => [(0,1)]
def root2Node0Domains4Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5),(8,5)]
  | 1 => some [(1,0),(6,0)]
  | 2 => some [(7,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(1,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(7,0)]
  | 20 => some [(4,3)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => none
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(1,4)]
  | 29 => some [(0,5)]
  | 30 => some [(2,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => none
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => none
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(1,2),(6,2)]
  | 51 => some [(8,4)]
  | 52 => some [(0,0)]
  | 53 => some [(7,2)]
  | 54 => some [(4,0)]
  | 55 => some [(7,3)]
  | 56 => some [(7,1),(8,1)]
  | 57 => some [(1,5)]
  | 58 => some [(6,1)]
  | 59 => some [(5,1)]
  | _ => some [(0,1)]
theorem root2Node0Domains4_fast_eq : root2Node0Domains4 = expandDomains root2Node0Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 61, root2Node0Domains4 v = expandDomains root2Node0Domains4Fast v from by decide) v
theorem root2Node0Step4Chunk0_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk0_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk0_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk0_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk0_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk0_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk1_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk1_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk1_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk1_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk1_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk1_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk2_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk2_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk2_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk2_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk2_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk2_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk3_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk3_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk3_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk3_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk3_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk3_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk4_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk4_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk4_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk4_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk4_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk4_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk5_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk5_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk5_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk5_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk5_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk5_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk6_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk6_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk6_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk6_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk6_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk6_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk7_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk7_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk7_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk7_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk7_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk7_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk8_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk8_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk8_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk8_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk8_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk8_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4_checked :
    checkReplacement table11 root2Node0Domains3 root2Node0Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root2Node0Step4Chunk0_0_checked, root2Node0Step4Chunk0_1_checked, root2Node0Step4Chunk0_2_checked, root2Node0Step4Chunk0_3_checked, root2Node0Step4Chunk0_4_checked, root2Node0Step4Chunk0_5_checked, root2Node0Step4Chunk1_0_checked, root2Node0Step4Chunk1_1_checked, root2Node0Step4Chunk1_2_checked, root2Node0Step4Chunk1_3_checked, root2Node0Step4Chunk1_4_checked, root2Node0Step4Chunk1_5_checked, root2Node0Step4Chunk2_0_checked, root2Node0Step4Chunk2_1_checked, root2Node0Step4Chunk2_2_checked, root2Node0Step4Chunk2_3_checked, root2Node0Step4Chunk2_4_checked, root2Node0Step4Chunk2_5_checked, root2Node0Step4Chunk3_0_checked, root2Node0Step4Chunk3_1_checked, root2Node0Step4Chunk3_2_checked, root2Node0Step4Chunk3_3_checked, root2Node0Step4Chunk3_4_checked, root2Node0Step4Chunk3_5_checked, root2Node0Step4Chunk4_0_checked, root2Node0Step4Chunk4_1_checked, root2Node0Step4Chunk4_2_checked, root2Node0Step4Chunk4_3_checked, root2Node0Step4Chunk4_4_checked, root2Node0Step4Chunk4_5_checked, root2Node0Step4Chunk5_0_checked, root2Node0Step4Chunk5_1_checked, root2Node0Step4Chunk5_2_checked, root2Node0Step4Chunk5_3_checked, root2Node0Step4Chunk5_4_checked, root2Node0Step4Chunk5_5_checked, root2Node0Step4Chunk6_0_checked, root2Node0Step4Chunk6_1_checked, root2Node0Step4Chunk6_2_checked, root2Node0Step4Chunk6_3_checked, root2Node0Step4Chunk6_4_checked, root2Node0Step4Chunk6_5_checked, root2Node0Step4Chunk7_0_checked, root2Node0Step4Chunk7_1_checked, root2Node0Step4Chunk7_2_checked, root2Node0Step4Chunk7_3_checked, root2Node0Step4Chunk7_4_checked, root2Node0Step4Chunk7_5_checked, root2Node0Step4Chunk8_0_checked, root2Node0Step4Chunk8_1_checked, root2Node0Step4Chunk8_2_checked, root2Node0Step4Chunk8_3_checked, root2Node0Step4Chunk8_4_checked, root2Node0Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root2Node0Domains5 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5),(8,5)]
  | 1 => [(1,0),(6,0)]
  | 2 => [(7,1)]
  | 3 => [(1,5)]
  | 4 => [(6,1)]
  | 5 => [(1,3)]
  | 6 => [(8,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => [(5,5)]
  | 19 => [(7,0)]
  | 20 => [(4,3)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(1,4)]
  | 29 => [(0,5)]
  | 30 => [(2,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(3,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(1,4),(6,4)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(1,2),(6,2)]
  | 51 => [(8,4)]
  | 52 => [(0,0)]
  | 53 => [(7,2)]
  | 54 => [(4,0)]
  | 55 => [(7,3)]
  | 56 => [(7,1),(8,1)]
  | 57 => [(1,5)]
  | 58 => [(6,1)]
  | 59 => [(5,1)]
  | _ => [(0,1)]
def root2Node0Domains5Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5),(8,5)]
  | 1 => some [(1,0),(6,0)]
  | 2 => some [(7,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(1,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(7,0)]
  | 20 => some [(4,3)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(1,4)]
  | 29 => some [(0,5)]
  | 30 => some [(2,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(1,4),(6,4)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(1,2),(6,2)]
  | 51 => some [(8,4)]
  | 52 => some [(0,0)]
  | 53 => some [(7,2)]
  | 54 => some [(4,0)]
  | 55 => some [(7,3)]
  | 56 => some [(7,1),(8,1)]
  | 57 => some [(1,5)]
  | 58 => some [(6,1)]
  | 59 => some [(5,1)]
  | _ => some [(0,1)]
theorem root2Node0Domains5_fast_eq : root2Node0Domains5 = expandDomains root2Node0Domains5Fast := by
  funext v
  exact (show ∀ v : Fin 61, root2Node0Domains5 v = expandDomains root2Node0Domains5Fast v from by decide) v
theorem root2Node0Step5Chunk0_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_0⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk0_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_1⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk0_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_2⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk0_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_3⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk0_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_4⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk0_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_5⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk1_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_0⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk1_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_1⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk1_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_2⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk1_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_3⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk1_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_4⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk1_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_5⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk2_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_0⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk2_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_1⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk2_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_2⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk2_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_3⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk2_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_4⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk2_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_5⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk3_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_0⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk3_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_1⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk3_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_2⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk3_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_3⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk3_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_4⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk3_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_5⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk4_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_0⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk4_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_1⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk4_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_2⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk4_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_3⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk4_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_4⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk4_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_5⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk5_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_0⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk5_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_1⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk5_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_2⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk5_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_3⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk5_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_4⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk5_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_5⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk6_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_0⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk6_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_1⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk6_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_2⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk6_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_3⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk6_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_4⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk6_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_5⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk7_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_0⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk7_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_1⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk7_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_2⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk7_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_3⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk7_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_4⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk7_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_5⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk8_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_0⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk8_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_1⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk8_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_2⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk8_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_3⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk8_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_4⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5Chunk8_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_5⟩
      root2Node0Domains4 root2Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains4 root2Node0Domains5
    root2Node0Domains4Fast root2Node0Domains5Fast
    root2Node0Domains4_fast_eq root2Node0Domains5_fast_eq (by decide)
theorem root2Node0Step5_checked :
    checkReplacement table16 root2Node0Domains4 root2Node0Domains5 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root2Node0Step5Chunk0_0_checked, root2Node0Step5Chunk0_1_checked, root2Node0Step5Chunk0_2_checked, root2Node0Step5Chunk0_3_checked, root2Node0Step5Chunk0_4_checked, root2Node0Step5Chunk0_5_checked, root2Node0Step5Chunk1_0_checked, root2Node0Step5Chunk1_1_checked, root2Node0Step5Chunk1_2_checked, root2Node0Step5Chunk1_3_checked, root2Node0Step5Chunk1_4_checked, root2Node0Step5Chunk1_5_checked, root2Node0Step5Chunk2_0_checked, root2Node0Step5Chunk2_1_checked, root2Node0Step5Chunk2_2_checked, root2Node0Step5Chunk2_3_checked, root2Node0Step5Chunk2_4_checked, root2Node0Step5Chunk2_5_checked, root2Node0Step5Chunk3_0_checked, root2Node0Step5Chunk3_1_checked, root2Node0Step5Chunk3_2_checked, root2Node0Step5Chunk3_3_checked, root2Node0Step5Chunk3_4_checked, root2Node0Step5Chunk3_5_checked, root2Node0Step5Chunk4_0_checked, root2Node0Step5Chunk4_1_checked, root2Node0Step5Chunk4_2_checked, root2Node0Step5Chunk4_3_checked, root2Node0Step5Chunk4_4_checked, root2Node0Step5Chunk4_5_checked, root2Node0Step5Chunk5_0_checked, root2Node0Step5Chunk5_1_checked, root2Node0Step5Chunk5_2_checked, root2Node0Step5Chunk5_3_checked, root2Node0Step5Chunk5_4_checked, root2Node0Step5Chunk5_5_checked, root2Node0Step5Chunk6_0_checked, root2Node0Step5Chunk6_1_checked, root2Node0Step5Chunk6_2_checked, root2Node0Step5Chunk6_3_checked, root2Node0Step5Chunk6_4_checked, root2Node0Step5Chunk6_5_checked, root2Node0Step5Chunk7_0_checked, root2Node0Step5Chunk7_1_checked, root2Node0Step5Chunk7_2_checked, root2Node0Step5Chunk7_3_checked, root2Node0Step5Chunk7_4_checked, root2Node0Step5Chunk7_5_checked, root2Node0Step5Chunk8_0_checked, root2Node0Step5Chunk8_1_checked, root2Node0Step5Chunk8_2_checked, root2Node0Step5Chunk8_3_checked, root2Node0Step5Chunk8_4_checked, root2Node0Step5Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
