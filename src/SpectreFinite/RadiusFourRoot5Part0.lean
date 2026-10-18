module

public import SpectreFinite.RadiusFourRoot5Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable10
public import SpectreFinite.RadiusFourTable20
public import SpectreFinite.RadiusFourTable29
public import SpectreFinite.RadiusFourTable35
public import SpectreFinite.RadiusFourTable39

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node0Domains0 : Domains 61 State := domains (5,0)
def root5Node0Domains0Fast (v : Fin 61) : Option (List State) :=
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
  | 30 => some [(5,0)]
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
theorem root5Node0Domains0_fast_eq : root5Node0Domains0 = expandDomains root5Node0Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node0Domains0 v = expandDomains root5Node0Domains0Fast v from by decide) v
def root5Node0Domains1 (v : Fin 61) : List State :=
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
  | 11 => stateChoices
  | 12 => stateChoices
  | 13 => [(0,1),(1,4),(7,4)]
  | 14 => [(0,5),(6,2),(6,3)]
  | 15 => [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 16 => [(0,0),(1,3),(3,3),(7,3)]
  | 17 => stateChoices
  | 18 => stateChoices
  | 19 => stateChoices
  | 20 => [(4,1),(7,5),(8,5)]
  | 21 => [(0,2),(1,0),(6,0)]
  | 22 => [(1,1),(3,1),(7,1)]
  | 23 => [(0,1),(1,5),(6,5)]
  | 24 => [(0,4),(6,1),(6,2)]
  | 25 => stateChoices
  | 26 => stateChoices
  | 27 => stateChoices
  | 28 => [(1,3),(7,3)]
  | 29 => [(5,2),(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(1,0),(7,0)]
  | 33 => [(4,3),(7,1),(8,3)]
  | 34 => stateChoices
  | 35 => stateChoices
  | 36 => [(0,1),(6,4),(6,5)]
  | 37 => [(0,4),(1,2),(6,2)]
  | 38 => [(5,4),(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0),(7,4)]
  | 42 => [(1,3),(6,3),(7,3)]
  | 43 => stateChoices
  | 44 => [(0,3),(1,0),(7,0)]
  | 45 => [(4,3),(7,1),(8,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(4,1),(5,1),(8,1)]
  | 49 => [(0,1),(0,2),(6,5)]
  | 50 => stateChoices
  | 51 => [(1,4),(5,0),(5,3)]
  | 52 => [(0,5),(4,5),(5,5),(8,5)]
  | 53 => [(2,0),(7,0)]
  | 54 => [(7,3),(8,3)]
  | 55 => [(5,2),(5,5),(8,5)]
  | 56 => stateChoices
  | 57 => [(0,0),(0,5),(6,0),(6,3)]
  | 58 => [(3,1),(4,4),(7,2)]
  | 59 => [(0,1),(1,4),(7,4)]
  | _ => [(0,5),(1,3),(6,2),(6,3)]
def root5Node0Domains1Fast (v : Fin 61) : Option (List State) :=
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
  | 13 => some [(0,1),(1,4),(7,4)]
  | 14 => some [(0,5),(6,2),(6,3)]
  | 15 => some [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 16 => some [(0,0),(1,3),(3,3),(7,3)]
  | 17 => none
  | 18 => none
  | 19 => none
  | 20 => some [(4,1),(7,5),(8,5)]
  | 21 => some [(0,2),(1,0),(6,0)]
  | 22 => some [(1,1),(3,1),(7,1)]
  | 23 => some [(0,1),(1,5),(6,5)]
  | 24 => some [(0,4),(6,1),(6,2)]
  | 25 => none
  | 26 => none
  | 27 => none
  | 28 => some [(1,3),(7,3)]
  | 29 => some [(5,2),(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0),(7,0)]
  | 33 => some [(4,3),(7,1),(8,3)]
  | 34 => none
  | 35 => none
  | 36 => some [(0,1),(6,4),(6,5)]
  | 37 => some [(0,4),(1,2),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0),(7,4)]
  | 42 => some [(1,3),(6,3),(7,3)]
  | 43 => none
  | 44 => some [(0,3),(1,0),(7,0)]
  | 45 => some [(4,3),(7,1),(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1),(5,1),(8,1)]
  | 49 => some [(0,1),(0,2),(6,5)]
  | 50 => none
  | 51 => some [(1,4),(5,0),(5,3)]
  | 52 => some [(0,5),(4,5),(5,5),(8,5)]
  | 53 => some [(2,0),(7,0)]
  | 54 => some [(7,3),(8,3)]
  | 55 => some [(5,2),(5,5),(8,5)]
  | 56 => none
  | 57 => some [(0,0),(0,5),(6,0),(6,3)]
  | 58 => some [(3,1),(4,4),(7,2)]
  | 59 => some [(0,1),(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,2),(6,3)]
theorem root5Node0Domains1_fast_eq : root5Node0Domains1 = expandDomains root5Node0Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node0Domains1 v = expandDomains root5Node0Domains1Fast v from by decide) v
theorem root5Node0Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root5Node0Domains0 root5Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains0 root5Node0Domains1
    root5Node0Domains0Fast root5Node0Domains1Fast
    root5Node0Domains0_fast_eq root5Node0Domains1_fast_eq (by decide)
theorem root5Node0Step1_checked :
    checkReplacement table39 root5Node0Domains0 root5Node0Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node0Step1Chunk0_0_checked, root5Node0Step1Chunk0_1_checked, root5Node0Step1Chunk0_2_checked, root5Node0Step1Chunk0_3_checked, root5Node0Step1Chunk0_4_checked, root5Node0Step1Chunk0_5_checked, root5Node0Step1Chunk1_0_checked, root5Node0Step1Chunk1_1_checked, root5Node0Step1Chunk1_2_checked, root5Node0Step1Chunk1_3_checked, root5Node0Step1Chunk1_4_checked, root5Node0Step1Chunk1_5_checked, root5Node0Step1Chunk2_0_checked, root5Node0Step1Chunk2_1_checked, root5Node0Step1Chunk2_2_checked, root5Node0Step1Chunk2_3_checked, root5Node0Step1Chunk2_4_checked, root5Node0Step1Chunk2_5_checked, root5Node0Step1Chunk3_0_checked, root5Node0Step1Chunk3_1_checked, root5Node0Step1Chunk3_2_checked, root5Node0Step1Chunk3_3_checked, root5Node0Step1Chunk3_4_checked, root5Node0Step1Chunk3_5_checked, root5Node0Step1Chunk4_0_checked, root5Node0Step1Chunk4_1_checked, root5Node0Step1Chunk4_2_checked, root5Node0Step1Chunk4_3_checked, root5Node0Step1Chunk4_4_checked, root5Node0Step1Chunk4_5_checked, root5Node0Step1Chunk5_0_checked, root5Node0Step1Chunk5_1_checked, root5Node0Step1Chunk5_2_checked, root5Node0Step1Chunk5_3_checked, root5Node0Step1Chunk5_4_checked, root5Node0Step1Chunk5_5_checked, root5Node0Step1Chunk6_0_checked, root5Node0Step1Chunk6_1_checked, root5Node0Step1Chunk6_2_checked, root5Node0Step1Chunk6_3_checked, root5Node0Step1Chunk6_4_checked, root5Node0Step1Chunk6_5_checked, root5Node0Step1Chunk7_0_checked, root5Node0Step1Chunk7_1_checked, root5Node0Step1Chunk7_2_checked, root5Node0Step1Chunk7_3_checked, root5Node0Step1Chunk7_4_checked, root5Node0Step1Chunk7_5_checked, root5Node0Step1Chunk8_0_checked, root5Node0Step1Chunk8_1_checked, root5Node0Step1Chunk8_2_checked, root5Node0Step1Chunk8_3_checked, root5Node0Step1Chunk8_4_checked, root5Node0Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node0Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(1,5),(6,0),(6,5)]
  | 1 => [(0,4),(1,1),(6,1),(7,1)]
  | 2 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 3 => stateChoices
  | 4 => stateChoices
  | 5 => [(1,2),(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 6 => [(4,0),(7,0),(8,0)]
  | 7 => [(4,3),(7,3),(8,3)]
  | 8 => [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 9 => stateChoices
  | 10 => stateChoices
  | 11 => [(0,3),(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 12 => [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 13 => [(0,1),(1,4),(7,4)]
  | 14 => [(0,5),(6,2),(6,3)]
  | 15 => [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 16 => [(0,0),(1,3),(3,3),(7,3)]
  | 17 => stateChoices
  | 18 => [(0,2),(1,0),(4,2),(6,0),(7,0)]
  | 19 => [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 20 => [(4,1),(7,5),(8,5)]
  | 21 => [(0,2),(1,0),(6,0)]
  | 22 => [(1,1),(3,1),(7,1)]
  | 23 => [(0,1),(1,5),(6,5)]
  | 24 => [(0,4),(6,1),(6,2)]
  | 25 => stateChoices
  | 26 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => [(4,0),(7,4),(8,0)]
  | 28 => [(1,3),(7,3)]
  | 29 => [(5,2),(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(1,0),(7,0)]
  | 33 => [(4,3),(7,1),(8,3)]
  | 34 => stateChoices
  | 35 => [(5,1),(5,4),(8,1),(8,4)]
  | 36 => [(0,1),(6,4),(6,5)]
  | 37 => [(0,4),(1,2),(6,2)]
  | 38 => [(5,4),(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0),(7,4)]
  | 42 => [(1,3),(6,3),(7,3)]
  | 43 => [(5,5),(7,5),(8,5)]
  | 44 => [(0,3),(1,0),(7,0)]
  | 45 => [(4,3),(7,1),(8,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(4,1),(5,1),(8,1)]
  | 49 => [(0,1),(0,2),(6,5)]
  | 50 => stateChoices
  | 51 => [(1,4),(5,0),(5,3)]
  | 52 => [(0,5),(4,5),(5,5),(8,5)]
  | 53 => [(2,0),(7,0)]
  | 54 => [(7,3),(8,3)]
  | 55 => [(5,2),(5,5),(8,5)]
  | 56 => stateChoices
  | 57 => [(0,0),(0,5),(6,0),(6,3)]
  | 58 => [(3,1),(4,4),(7,2)]
  | 59 => [(0,1),(1,4),(7,4)]
  | _ => [(0,5),(1,3),(6,2),(6,3)]
def root5Node0Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0),(6,5)]
  | 1 => some [(0,4),(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 3 => none
  | 4 => none
  | 5 => some [(1,2),(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 6 => some [(4,0),(7,0),(8,0)]
  | 7 => some [(4,3),(7,3),(8,3)]
  | 8 => some [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 9 => none
  | 10 => none
  | 11 => some [(0,3),(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 12 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 13 => some [(0,1),(1,4),(7,4)]
  | 14 => some [(0,5),(6,2),(6,3)]
  | 15 => some [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 16 => some [(0,0),(1,3),(3,3),(7,3)]
  | 17 => none
  | 18 => some [(0,2),(1,0),(4,2),(6,0),(7,0)]
  | 19 => some [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 20 => some [(4,1),(7,5),(8,5)]
  | 21 => some [(0,2),(1,0),(6,0)]
  | 22 => some [(1,1),(3,1),(7,1)]
  | 23 => some [(0,1),(1,5),(6,5)]
  | 24 => some [(0,4),(6,1),(6,2)]
  | 25 => none
  | 26 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => some [(4,0),(7,4),(8,0)]
  | 28 => some [(1,3),(7,3)]
  | 29 => some [(5,2),(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0),(7,0)]
  | 33 => some [(4,3),(7,1),(8,3)]
  | 34 => none
  | 35 => some [(5,1),(5,4),(8,1),(8,4)]
  | 36 => some [(0,1),(6,4),(6,5)]
  | 37 => some [(0,4),(1,2),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0),(7,4)]
  | 42 => some [(1,3),(6,3),(7,3)]
  | 43 => some [(5,5),(7,5),(8,5)]
  | 44 => some [(0,3),(1,0),(7,0)]
  | 45 => some [(4,3),(7,1),(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1),(5,1),(8,1)]
  | 49 => some [(0,1),(0,2),(6,5)]
  | 50 => none
  | 51 => some [(1,4),(5,0),(5,3)]
  | 52 => some [(0,5),(4,5),(5,5),(8,5)]
  | 53 => some [(2,0),(7,0)]
  | 54 => some [(7,3),(8,3)]
  | 55 => some [(5,2),(5,5),(8,5)]
  | 56 => none
  | 57 => some [(0,0),(0,5),(6,0),(6,3)]
  | 58 => some [(3,1),(4,4),(7,2)]
  | 59 => some [(0,1),(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,2),(6,3)]
theorem root5Node0Domains2_fast_eq : root5Node0Domains2 = expandDomains root5Node0Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node0Domains2 v = expandDomains root5Node0Domains2Fast v from by decide) v
theorem root5Node0Step2Chunk0_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_0⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk0_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_1⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk0_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_2⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk0_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_3⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk0_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_4⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk0_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_5⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk1_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_0⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk1_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_1⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk1_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_2⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk1_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_3⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk1_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_4⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk1_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_5⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk2_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_0⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk2_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_1⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk2_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_2⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk2_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_3⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk2_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_4⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk2_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_5⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk3_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_0⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk3_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_1⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk3_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_2⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk3_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_3⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk3_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_4⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk3_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_5⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk4_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_0⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk4_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_1⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk4_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_2⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk4_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_3⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk4_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_4⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk4_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_5⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk5_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_0⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk5_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_1⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk5_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_2⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk5_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_3⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk5_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_4⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk5_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_5⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk6_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_0⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk6_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_1⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk6_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_2⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk6_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_3⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk6_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_4⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk6_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_5⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk7_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_0⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk7_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_1⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk7_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_2⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk7_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_3⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk7_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_4⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk7_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_5⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk8_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_0⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk8_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_1⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk8_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_2⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk8_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_3⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk8_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_4⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2Chunk8_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_5⟩
      root5Node0Domains1 root5Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains1 root5Node0Domains2
    root5Node0Domains1Fast root5Node0Domains2Fast
    root5Node0Domains1_fast_eq root5Node0Domains2_fast_eq (by decide)
theorem root5Node0Step2_checked :
    checkReplacement table20 root5Node0Domains1 root5Node0Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node0Step2Chunk0_0_checked, root5Node0Step2Chunk0_1_checked, root5Node0Step2Chunk0_2_checked, root5Node0Step2Chunk0_3_checked, root5Node0Step2Chunk0_4_checked, root5Node0Step2Chunk0_5_checked, root5Node0Step2Chunk1_0_checked, root5Node0Step2Chunk1_1_checked, root5Node0Step2Chunk1_2_checked, root5Node0Step2Chunk1_3_checked, root5Node0Step2Chunk1_4_checked, root5Node0Step2Chunk1_5_checked, root5Node0Step2Chunk2_0_checked, root5Node0Step2Chunk2_1_checked, root5Node0Step2Chunk2_2_checked, root5Node0Step2Chunk2_3_checked, root5Node0Step2Chunk2_4_checked, root5Node0Step2Chunk2_5_checked, root5Node0Step2Chunk3_0_checked, root5Node0Step2Chunk3_1_checked, root5Node0Step2Chunk3_2_checked, root5Node0Step2Chunk3_3_checked, root5Node0Step2Chunk3_4_checked, root5Node0Step2Chunk3_5_checked, root5Node0Step2Chunk4_0_checked, root5Node0Step2Chunk4_1_checked, root5Node0Step2Chunk4_2_checked, root5Node0Step2Chunk4_3_checked, root5Node0Step2Chunk4_4_checked, root5Node0Step2Chunk4_5_checked, root5Node0Step2Chunk5_0_checked, root5Node0Step2Chunk5_1_checked, root5Node0Step2Chunk5_2_checked, root5Node0Step2Chunk5_3_checked, root5Node0Step2Chunk5_4_checked, root5Node0Step2Chunk5_5_checked, root5Node0Step2Chunk6_0_checked, root5Node0Step2Chunk6_1_checked, root5Node0Step2Chunk6_2_checked, root5Node0Step2Chunk6_3_checked, root5Node0Step2Chunk6_4_checked, root5Node0Step2Chunk6_5_checked, root5Node0Step2Chunk7_0_checked, root5Node0Step2Chunk7_1_checked, root5Node0Step2Chunk7_2_checked, root5Node0Step2Chunk7_3_checked, root5Node0Step2Chunk7_4_checked, root5Node0Step2Chunk7_5_checked, root5Node0Step2Chunk8_0_checked, root5Node0Step2Chunk8_1_checked, root5Node0Step2Chunk8_2_checked, root5Node0Step2Chunk8_3_checked, root5Node0Step2Chunk8_4_checked, root5Node0Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node0Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(1,5),(6,0),(6,5)]
  | 1 => [(0,4),(1,1),(6,1),(7,1)]
  | 2 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 3 => [(0,0),(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 4 => [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 5 => [(1,2),(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 6 => [(4,0),(7,0),(8,0)]
  | 7 => [(4,3),(7,3),(8,3)]
  | 8 => [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 9 => [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 10 => [(2,1),(2,5),(4,1),(4,5)]
  | 11 => [(0,3),(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 12 => [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 13 => [(0,1),(1,4),(7,4)]
  | 14 => [(0,5),(6,2),(6,3)]
  | 15 => [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 16 => [(0,0),(1,3),(3,3),(7,3)]
  | 17 => [(3,2),(5,2),(7,2)]
  | 18 => [(0,2),(1,0),(4,2),(6,0),(7,0)]
  | 19 => [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 20 => [(4,1),(7,5),(8,5)]
  | 21 => [(0,2),(1,0),(6,0)]
  | 22 => [(1,1),(3,1),(7,1)]
  | 23 => [(0,1),(1,5),(6,5)]
  | 24 => [(0,4),(6,1),(6,2)]
  | 25 => [(5,1),(5,4),(8,1),(8,4)]
  | 26 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => [(4,0),(7,4),(8,0)]
  | 28 => [(1,3),(7,3)]
  | 29 => [(5,2),(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(1,0),(7,0)]
  | 33 => [(4,3),(7,1),(8,3)]
  | 34 => [(7,5),(8,5)]
  | 35 => [(5,1),(5,4),(8,1),(8,4)]
  | 36 => [(0,1),(6,4),(6,5)]
  | 37 => [(0,4),(1,2),(6,2)]
  | 38 => [(5,4),(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0),(7,4)]
  | 42 => [(1,3),(6,3),(7,3)]
  | 43 => [(5,5),(7,5),(8,5)]
  | 44 => [(0,3),(1,0),(7,0)]
  | 45 => [(4,3),(7,1),(8,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(4,1),(5,1),(8,1)]
  | 49 => [(0,1),(0,2),(6,5)]
  | 50 => stateChoices
  | 51 => [(1,4),(5,0),(5,3)]
  | 52 => [(0,5),(4,5),(5,5),(8,5)]
  | 53 => [(2,0),(7,0)]
  | 54 => [(7,3),(8,3)]
  | 55 => [(5,2),(5,5),(8,5)]
  | 56 => stateChoices
  | 57 => [(0,0),(0,5),(6,0),(6,3)]
  | 58 => [(3,1),(4,4),(7,2)]
  | 59 => [(0,1),(1,4),(7,4)]
  | _ => [(0,5),(1,3),(6,2),(6,3)]
def root5Node0Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0),(6,5)]
  | 1 => some [(0,4),(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 3 => some [(0,0),(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 4 => some [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 5 => some [(1,2),(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 6 => some [(4,0),(7,0),(8,0)]
  | 7 => some [(4,3),(7,3),(8,3)]
  | 8 => some [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 9 => some [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 10 => some [(2,1),(2,5),(4,1),(4,5)]
  | 11 => some [(0,3),(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 12 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 13 => some [(0,1),(1,4),(7,4)]
  | 14 => some [(0,5),(6,2),(6,3)]
  | 15 => some [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 16 => some [(0,0),(1,3),(3,3),(7,3)]
  | 17 => some [(3,2),(5,2),(7,2)]
  | 18 => some [(0,2),(1,0),(4,2),(6,0),(7,0)]
  | 19 => some [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 20 => some [(4,1),(7,5),(8,5)]
  | 21 => some [(0,2),(1,0),(6,0)]
  | 22 => some [(1,1),(3,1),(7,1)]
  | 23 => some [(0,1),(1,5),(6,5)]
  | 24 => some [(0,4),(6,1),(6,2)]
  | 25 => some [(5,1),(5,4),(8,1),(8,4)]
  | 26 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => some [(4,0),(7,4),(8,0)]
  | 28 => some [(1,3),(7,3)]
  | 29 => some [(5,2),(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0),(7,0)]
  | 33 => some [(4,3),(7,1),(8,3)]
  | 34 => some [(7,5),(8,5)]
  | 35 => some [(5,1),(5,4),(8,1),(8,4)]
  | 36 => some [(0,1),(6,4),(6,5)]
  | 37 => some [(0,4),(1,2),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0),(7,4)]
  | 42 => some [(1,3),(6,3),(7,3)]
  | 43 => some [(5,5),(7,5),(8,5)]
  | 44 => some [(0,3),(1,0),(7,0)]
  | 45 => some [(4,3),(7,1),(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1),(5,1),(8,1)]
  | 49 => some [(0,1),(0,2),(6,5)]
  | 50 => none
  | 51 => some [(1,4),(5,0),(5,3)]
  | 52 => some [(0,5),(4,5),(5,5),(8,5)]
  | 53 => some [(2,0),(7,0)]
  | 54 => some [(7,3),(8,3)]
  | 55 => some [(5,2),(5,5),(8,5)]
  | 56 => none
  | 57 => some [(0,0),(0,5),(6,0),(6,3)]
  | 58 => some [(3,1),(4,4),(7,2)]
  | 59 => some [(0,1),(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,2),(6,3)]
theorem root5Node0Domains3_fast_eq : root5Node0Domains3 = expandDomains root5Node0Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node0Domains3 v = expandDomains root5Node0Domains3Fast v from by decide) v
theorem root5Node0Step3Chunk0_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_0⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk0_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_1⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk0_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_2⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk0_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_3⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk0_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_4⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk0_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_5⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk1_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_0⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk1_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_1⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk1_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_2⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk1_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_3⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk1_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_4⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk1_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_5⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk2_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_0⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk2_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_1⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk2_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_2⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk2_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_3⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk2_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_4⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk2_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_5⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk3_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_0⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk3_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_1⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk3_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_2⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk3_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_3⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk3_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_4⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk3_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_5⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk4_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_0⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk4_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_1⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk4_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_2⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk4_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_3⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk4_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_4⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk4_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_5⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk5_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_0⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk5_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_1⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk5_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_2⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk5_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_3⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk5_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_4⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk5_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_5⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk6_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_0⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk6_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_1⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk6_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_2⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk6_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_3⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk6_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_4⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk6_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_5⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk7_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_0⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk7_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_1⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk7_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_2⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk7_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_3⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk7_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_4⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk7_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_5⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk8_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_0⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk8_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_1⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk8_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_2⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk8_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_3⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk8_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_4⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3Chunk8_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_5⟩
      root5Node0Domains2 root5Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains2 root5Node0Domains3
    root5Node0Domains2Fast root5Node0Domains3Fast
    root5Node0Domains2_fast_eq root5Node0Domains3_fast_eq (by decide)
theorem root5Node0Step3_checked :
    checkReplacement table10 root5Node0Domains2 root5Node0Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node0Step3Chunk0_0_checked, root5Node0Step3Chunk0_1_checked, root5Node0Step3Chunk0_2_checked, root5Node0Step3Chunk0_3_checked, root5Node0Step3Chunk0_4_checked, root5Node0Step3Chunk0_5_checked, root5Node0Step3Chunk1_0_checked, root5Node0Step3Chunk1_1_checked, root5Node0Step3Chunk1_2_checked, root5Node0Step3Chunk1_3_checked, root5Node0Step3Chunk1_4_checked, root5Node0Step3Chunk1_5_checked, root5Node0Step3Chunk2_0_checked, root5Node0Step3Chunk2_1_checked, root5Node0Step3Chunk2_2_checked, root5Node0Step3Chunk2_3_checked, root5Node0Step3Chunk2_4_checked, root5Node0Step3Chunk2_5_checked, root5Node0Step3Chunk3_0_checked, root5Node0Step3Chunk3_1_checked, root5Node0Step3Chunk3_2_checked, root5Node0Step3Chunk3_3_checked, root5Node0Step3Chunk3_4_checked, root5Node0Step3Chunk3_5_checked, root5Node0Step3Chunk4_0_checked, root5Node0Step3Chunk4_1_checked, root5Node0Step3Chunk4_2_checked, root5Node0Step3Chunk4_3_checked, root5Node0Step3Chunk4_4_checked, root5Node0Step3Chunk4_5_checked, root5Node0Step3Chunk5_0_checked, root5Node0Step3Chunk5_1_checked, root5Node0Step3Chunk5_2_checked, root5Node0Step3Chunk5_3_checked, root5Node0Step3Chunk5_4_checked, root5Node0Step3Chunk5_5_checked, root5Node0Step3Chunk6_0_checked, root5Node0Step3Chunk6_1_checked, root5Node0Step3Chunk6_2_checked, root5Node0Step3Chunk6_3_checked, root5Node0Step3Chunk6_4_checked, root5Node0Step3Chunk6_5_checked, root5Node0Step3Chunk7_0_checked, root5Node0Step3Chunk7_1_checked, root5Node0Step3Chunk7_2_checked, root5Node0Step3Chunk7_3_checked, root5Node0Step3Chunk7_4_checked, root5Node0Step3Chunk7_5_checked, root5Node0Step3Chunk8_0_checked, root5Node0Step3Chunk8_1_checked, root5Node0Step3Chunk8_2_checked, root5Node0Step3Chunk8_3_checked, root5Node0Step3Chunk8_4_checked, root5Node0Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node0Domains4 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(1,5),(6,0),(6,5)]
  | 1 => [(0,4),(1,1),(6,1),(7,1)]
  | 2 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 3 => [(0,0),(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 4 => [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 5 => [(1,2),(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 6 => [(4,0),(7,0),(8,0)]
  | 7 => [(4,3),(7,3),(8,3)]
  | 8 => [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 9 => [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 10 => [(2,1),(2,5),(4,1),(4,5)]
  | 11 => [(0,3),(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 12 => [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 13 => [(0,1),(1,4),(7,4)]
  | 14 => [(0,5),(6,2),(6,3)]
  | 15 => [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 16 => [(0,0),(1,3),(3,3),(7,3)]
  | 17 => [(3,2),(5,2),(7,2)]
  | 18 => [(0,2),(1,0),(4,2),(6,0),(7,0)]
  | 19 => [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 20 => [(4,1),(7,5),(8,5)]
  | 21 => [(0,2),(1,0),(6,0)]
  | 22 => [(1,1),(3,1),(7,1)]
  | 23 => [(0,1),(1,5),(6,5)]
  | 24 => [(0,4),(6,1),(6,2)]
  | 25 => [(5,1),(5,4),(8,1),(8,4)]
  | 26 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => [(4,0),(7,4),(8,0)]
  | 28 => [(1,3),(7,3)]
  | 29 => [(5,2),(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(1,0),(7,0)]
  | 33 => [(4,3),(7,1),(8,3)]
  | 34 => [(7,5),(8,5)]
  | 35 => [(5,1),(5,4),(8,1),(8,4)]
  | 36 => [(0,1),(6,4),(6,5)]
  | 37 => [(0,4),(1,2),(6,2)]
  | 38 => [(5,4),(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0),(7,4)]
  | 42 => [(1,3),(6,3),(7,3)]
  | 43 => [(5,5),(7,5),(8,5)]
  | 44 => [(0,3),(1,0),(7,0)]
  | 45 => [(4,3),(7,1),(8,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(4,1),(5,1),(8,1)]
  | 49 => [(0,1),(0,2),(6,5)]
  | 50 => [(4,2),(4,4),(8,2)]
  | 51 => [(1,4),(5,0),(5,3)]
  | 52 => [(0,5),(4,5),(5,5),(8,5)]
  | 53 => [(2,0),(7,0)]
  | 54 => [(7,3),(8,3)]
  | 55 => [(5,2),(5,5),(8,5)]
  | 56 => [(1,4),(3,4),(5,4),(7,4),(7,5)]
  | 57 => [(0,0),(0,5),(6,0),(6,3)]
  | 58 => [(3,1),(4,4),(7,2)]
  | 59 => [(0,1),(1,4),(7,4)]
  | _ => [(0,5),(1,3),(6,2),(6,3)]
def root5Node0Domains4Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0),(6,5)]
  | 1 => some [(0,4),(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 3 => some [(0,0),(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 4 => some [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 5 => some [(1,2),(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 6 => some [(4,0),(7,0),(8,0)]
  | 7 => some [(4,3),(7,3),(8,3)]
  | 8 => some [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 9 => some [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 10 => some [(2,1),(2,5),(4,1),(4,5)]
  | 11 => some [(0,3),(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 12 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 13 => some [(0,1),(1,4),(7,4)]
  | 14 => some [(0,5),(6,2),(6,3)]
  | 15 => some [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 16 => some [(0,0),(1,3),(3,3),(7,3)]
  | 17 => some [(3,2),(5,2),(7,2)]
  | 18 => some [(0,2),(1,0),(4,2),(6,0),(7,0)]
  | 19 => some [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 20 => some [(4,1),(7,5),(8,5)]
  | 21 => some [(0,2),(1,0),(6,0)]
  | 22 => some [(1,1),(3,1),(7,1)]
  | 23 => some [(0,1),(1,5),(6,5)]
  | 24 => some [(0,4),(6,1),(6,2)]
  | 25 => some [(5,1),(5,4),(8,1),(8,4)]
  | 26 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => some [(4,0),(7,4),(8,0)]
  | 28 => some [(1,3),(7,3)]
  | 29 => some [(5,2),(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0),(7,0)]
  | 33 => some [(4,3),(7,1),(8,3)]
  | 34 => some [(7,5),(8,5)]
  | 35 => some [(5,1),(5,4),(8,1),(8,4)]
  | 36 => some [(0,1),(6,4),(6,5)]
  | 37 => some [(0,4),(1,2),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0),(7,4)]
  | 42 => some [(1,3),(6,3),(7,3)]
  | 43 => some [(5,5),(7,5),(8,5)]
  | 44 => some [(0,3),(1,0),(7,0)]
  | 45 => some [(4,3),(7,1),(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1),(5,1),(8,1)]
  | 49 => some [(0,1),(0,2),(6,5)]
  | 50 => some [(4,2),(4,4),(8,2)]
  | 51 => some [(1,4),(5,0),(5,3)]
  | 52 => some [(0,5),(4,5),(5,5),(8,5)]
  | 53 => some [(2,0),(7,0)]
  | 54 => some [(7,3),(8,3)]
  | 55 => some [(5,2),(5,5),(8,5)]
  | 56 => some [(1,4),(3,4),(5,4),(7,4),(7,5)]
  | 57 => some [(0,0),(0,5),(6,0),(6,3)]
  | 58 => some [(3,1),(4,4),(7,2)]
  | 59 => some [(0,1),(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,2),(6,3)]
theorem root5Node0Domains4_fast_eq : root5Node0Domains4 = expandDomains root5Node0Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node0Domains4 v = expandDomains root5Node0Domains4Fast v from by decide) v
theorem root5Node0Step4Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4_checked :
    checkReplacement table35 root5Node0Domains3 root5Node0Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node0Step4Chunk0_0_checked, root5Node0Step4Chunk0_1_checked, root5Node0Step4Chunk0_2_checked, root5Node0Step4Chunk0_3_checked, root5Node0Step4Chunk0_4_checked, root5Node0Step4Chunk0_5_checked, root5Node0Step4Chunk1_0_checked, root5Node0Step4Chunk1_1_checked, root5Node0Step4Chunk1_2_checked, root5Node0Step4Chunk1_3_checked, root5Node0Step4Chunk1_4_checked, root5Node0Step4Chunk1_5_checked, root5Node0Step4Chunk2_0_checked, root5Node0Step4Chunk2_1_checked, root5Node0Step4Chunk2_2_checked, root5Node0Step4Chunk2_3_checked, root5Node0Step4Chunk2_4_checked, root5Node0Step4Chunk2_5_checked, root5Node0Step4Chunk3_0_checked, root5Node0Step4Chunk3_1_checked, root5Node0Step4Chunk3_2_checked, root5Node0Step4Chunk3_3_checked, root5Node0Step4Chunk3_4_checked, root5Node0Step4Chunk3_5_checked, root5Node0Step4Chunk4_0_checked, root5Node0Step4Chunk4_1_checked, root5Node0Step4Chunk4_2_checked, root5Node0Step4Chunk4_3_checked, root5Node0Step4Chunk4_4_checked, root5Node0Step4Chunk4_5_checked, root5Node0Step4Chunk5_0_checked, root5Node0Step4Chunk5_1_checked, root5Node0Step4Chunk5_2_checked, root5Node0Step4Chunk5_3_checked, root5Node0Step4Chunk5_4_checked, root5Node0Step4Chunk5_5_checked, root5Node0Step4Chunk6_0_checked, root5Node0Step4Chunk6_1_checked, root5Node0Step4Chunk6_2_checked, root5Node0Step4Chunk6_3_checked, root5Node0Step4Chunk6_4_checked, root5Node0Step4Chunk6_5_checked, root5Node0Step4Chunk7_0_checked, root5Node0Step4Chunk7_1_checked, root5Node0Step4Chunk7_2_checked, root5Node0Step4Chunk7_3_checked, root5Node0Step4Chunk7_4_checked, root5Node0Step4Chunk7_5_checked, root5Node0Step4Chunk8_0_checked, root5Node0Step4Chunk8_1_checked, root5Node0Step4Chunk8_2_checked, root5Node0Step4Chunk8_3_checked, root5Node0Step4Chunk8_4_checked, root5Node0Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node1Domains0 : Domains 61 State := restrict root5Node0Domains4 28 (1,3)
def root5Node1Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0),(6,5)]
  | 1 => some [(0,4),(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 3 => some [(0,0),(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 4 => some [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 5 => some [(1,2),(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 6 => some [(4,0),(7,0),(8,0)]
  | 7 => some [(4,3),(7,3),(8,3)]
  | 8 => some [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 9 => some [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 10 => some [(2,1),(2,5),(4,1),(4,5)]
  | 11 => some [(0,3),(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 12 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 13 => some [(0,1),(1,4),(7,4)]
  | 14 => some [(0,5),(6,2),(6,3)]
  | 15 => some [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 16 => some [(0,0),(1,3),(3,3),(7,3)]
  | 17 => some [(3,2),(5,2),(7,2)]
  | 18 => some [(0,2),(1,0),(4,2),(6,0),(7,0)]
  | 19 => some [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 20 => some [(4,1),(7,5),(8,5)]
  | 21 => some [(0,2),(1,0),(6,0)]
  | 22 => some [(1,1),(3,1),(7,1)]
  | 23 => some [(0,1),(1,5),(6,5)]
  | 24 => some [(0,4),(6,1),(6,2)]
  | 25 => some [(5,1),(5,4),(8,1),(8,4)]
  | 26 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => some [(4,0),(7,4),(8,0)]
  | 28 => some [(1,3)]
  | 29 => some [(5,2),(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0),(7,0)]
  | 33 => some [(4,3),(7,1),(8,3)]
  | 34 => some [(7,5),(8,5)]
  | 35 => some [(5,1),(5,4),(8,1),(8,4)]
  | 36 => some [(0,1),(6,4),(6,5)]
  | 37 => some [(0,4),(1,2),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0),(7,4)]
  | 42 => some [(1,3),(6,3),(7,3)]
  | 43 => some [(5,5),(7,5),(8,5)]
  | 44 => some [(0,3),(1,0),(7,0)]
  | 45 => some [(4,3),(7,1),(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1),(5,1),(8,1)]
  | 49 => some [(0,1),(0,2),(6,5)]
  | 50 => some [(4,2),(4,4),(8,2)]
  | 51 => some [(1,4),(5,0),(5,3)]
  | 52 => some [(0,5),(4,5),(5,5),(8,5)]
  | 53 => some [(2,0),(7,0)]
  | 54 => some [(7,3),(8,3)]
  | 55 => some [(5,2),(5,5),(8,5)]
  | 56 => some [(1,4),(3,4),(5,4),(7,4),(7,5)]
  | 57 => some [(0,0),(0,5),(6,0),(6,3)]
  | 58 => some [(3,1),(4,4),(7,2)]
  | 59 => some [(0,1),(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,2),(6,3)]
theorem root5Node1Domains0_fast_eq : root5Node1Domains0 = expandDomains root5Node1Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node1Domains0 v = expandDomains root5Node1Domains0Fast v from by decide) v
def root5Node1Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(1,5),(6,0),(6,5)]
  | 1 => [(0,4),(1,1),(6,1),(7,1)]
  | 2 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 3 => [(0,0),(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 4 => [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 5 => [(1,2),(3,2),(5,2),(7,2)]
  | 6 => [(4,0),(8,0)]
  | 7 => [(7,3),(8,3)]
  | 8 => [(5,2),(5,5),(8,2)]
  | 9 => [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 10 => [(2,1),(2,5),(4,1),(4,5)]
  | 11 => [(0,3),(0,4),(6,1)]
  | 12 => [(5,1),(5,4)]
  | 13 => [(0,1),(1,4)]
  | 14 => [(0,5),(6,2)]
  | 15 => [(4,4),(8,4)]
  | 16 => [(0,0),(1,3),(3,3),(7,3)]
  | 17 => [(3,2),(5,2),(7,2)]
  | 18 => [(4,2),(7,0)]
  | 19 => [(4,3),(5,3),(8,3)]
  | 20 => [(7,5),(8,5)]
  | 21 => [(1,0),(6,0)]
  | 22 => [(7,1)]
  | 23 => [(1,5)]
  | 24 => [(0,4),(6,1),(6,2)]
  | 25 => [(5,1),(5,4),(8,1),(8,4)]
  | 26 => [(1,2),(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(4,3),(7,1),(8,3)]
  | 34 => [(7,5),(8,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0),(7,4)]
  | 42 => [(1,3),(6,3),(7,3)]
  | 43 => [(5,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(4,1),(5,1),(8,1)]
  | 49 => [(0,1),(0,2),(6,5)]
  | 50 => [(4,4)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(2,0)]
  | 54 => [(7,3),(8,3)]
  | 55 => [(5,2),(5,5),(8,5)]
  | 56 => [(1,4),(3,4),(5,4),(7,4),(7,5)]
  | 57 => [(0,0),(0,5),(6,0),(6,3)]
  | 58 => [(3,1),(4,4),(7,2)]
  | 59 => [(0,1),(1,4),(7,4)]
  | _ => [(0,5),(1,3),(6,2),(6,3)]
def root5Node1Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0),(6,5)]
  | 1 => some [(0,4),(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 3 => some [(0,0),(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 4 => some [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 5 => some [(1,2),(3,2),(5,2),(7,2)]
  | 6 => some [(4,0),(8,0)]
  | 7 => some [(7,3),(8,3)]
  | 8 => some [(5,2),(5,5),(8,2)]
  | 9 => some [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 10 => some [(2,1),(2,5),(4,1),(4,5)]
  | 11 => some [(0,3),(0,4),(6,1)]
  | 12 => some [(5,1),(5,4)]
  | 13 => some [(0,1),(1,4)]
  | 14 => some [(0,5),(6,2)]
  | 15 => some [(4,4),(8,4)]
  | 16 => some [(0,0),(1,3),(3,3),(7,3)]
  | 17 => some [(3,2),(5,2),(7,2)]
  | 18 => some [(4,2),(7,0)]
  | 19 => some [(4,3),(5,3),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(1,0),(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(0,4),(6,1),(6,2)]
  | 25 => some [(5,1),(5,4),(8,1),(8,4)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3),(7,1),(8,3)]
  | 34 => some [(7,5),(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0),(7,4)]
  | 42 => some [(1,3),(6,3),(7,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1),(5,1),(8,1)]
  | 49 => some [(0,1),(0,2),(6,5)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(2,0)]
  | 54 => some [(7,3),(8,3)]
  | 55 => some [(5,2),(5,5),(8,5)]
  | 56 => some [(1,4),(3,4),(5,4),(7,4),(7,5)]
  | 57 => some [(0,0),(0,5),(6,0),(6,3)]
  | 58 => some [(3,1),(4,4),(7,2)]
  | 59 => some [(0,1),(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,2),(6,3)]
theorem root5Node1Domains1_fast_eq : root5Node1Domains1 = expandDomains root5Node1Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node1Domains1 v = expandDomains root5Node1Domains1Fast v from by decide) v
theorem root5Node1Step1Chunk0_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk0_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk0_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk0_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk0_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk0_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk1_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk1_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk1_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk1_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk1_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk1_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk2_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk2_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk2_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk2_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk2_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk2_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk3_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk3_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk3_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk3_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk3_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk3_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk4_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk4_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk4_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk4_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk4_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk4_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk5_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk5_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk5_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk5_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk5_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk5_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk6_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk6_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk6_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk6_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk6_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk6_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk7_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk7_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk7_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk7_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk7_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk7_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk8_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk8_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk8_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk8_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk8_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk8_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1_checked :
    checkReplacement table29 root5Node1Domains0 root5Node1Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node1Step1Chunk0_0_checked, root5Node1Step1Chunk0_1_checked, root5Node1Step1Chunk0_2_checked, root5Node1Step1Chunk0_3_checked, root5Node1Step1Chunk0_4_checked, root5Node1Step1Chunk0_5_checked, root5Node1Step1Chunk1_0_checked, root5Node1Step1Chunk1_1_checked, root5Node1Step1Chunk1_2_checked, root5Node1Step1Chunk1_3_checked, root5Node1Step1Chunk1_4_checked, root5Node1Step1Chunk1_5_checked, root5Node1Step1Chunk2_0_checked, root5Node1Step1Chunk2_1_checked, root5Node1Step1Chunk2_2_checked, root5Node1Step1Chunk2_3_checked, root5Node1Step1Chunk2_4_checked, root5Node1Step1Chunk2_5_checked, root5Node1Step1Chunk3_0_checked, root5Node1Step1Chunk3_1_checked, root5Node1Step1Chunk3_2_checked, root5Node1Step1Chunk3_3_checked, root5Node1Step1Chunk3_4_checked, root5Node1Step1Chunk3_5_checked, root5Node1Step1Chunk4_0_checked, root5Node1Step1Chunk4_1_checked, root5Node1Step1Chunk4_2_checked, root5Node1Step1Chunk4_3_checked, root5Node1Step1Chunk4_4_checked, root5Node1Step1Chunk4_5_checked, root5Node1Step1Chunk5_0_checked, root5Node1Step1Chunk5_1_checked, root5Node1Step1Chunk5_2_checked, root5Node1Step1Chunk5_3_checked, root5Node1Step1Chunk5_4_checked, root5Node1Step1Chunk5_5_checked, root5Node1Step1Chunk6_0_checked, root5Node1Step1Chunk6_1_checked, root5Node1Step1Chunk6_2_checked, root5Node1Step1Chunk6_3_checked, root5Node1Step1Chunk6_4_checked, root5Node1Step1Chunk6_5_checked, root5Node1Step1Chunk7_0_checked, root5Node1Step1Chunk7_1_checked, root5Node1Step1Chunk7_2_checked, root5Node1Step1Chunk7_3_checked, root5Node1Step1Chunk7_4_checked, root5Node1Step1Chunk7_5_checked, root5Node1Step1Chunk8_0_checked, root5Node1Step1Chunk8_1_checked, root5Node1Step1Chunk8_2_checked, root5Node1Step1Chunk8_3_checked, root5Node1Step1Chunk8_4_checked, root5Node1Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
