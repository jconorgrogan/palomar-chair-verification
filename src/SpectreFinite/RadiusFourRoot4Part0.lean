module

public import SpectreFinite.RadiusFourRoot4Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable10
public import SpectreFinite.RadiusFourTable14
public import SpectreFinite.RadiusFourTable21
public import SpectreFinite.RadiusFourTable35
public import SpectreFinite.RadiusFourTable39

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node0Domains0 : Domains 61 State := domains (4,0)
def root4Node0Domains0Fast (v : Fin 61) : Option (List State) :=
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
  | 30 => some [(4,0)]
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
theorem root4Node0Domains0_fast_eq : root4Node0Domains0 = expandDomains root4Node0Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node0Domains0 v = expandDomains root4Node0Domains0Fast v from by decide) v
def root4Node0Domains1 (v : Fin 61) : List State :=
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
  | 13 => [(0,1),(1,4),(3,4),(7,4)]
  | 14 => [(0,5),(6,2),(6,3)]
  | 15 => [(4,4),(7,2),(8,4)]
  | 16 => [(1,4),(6,4),(7,4)]
  | 17 => stateChoices
  | 18 => stateChoices
  | 19 => stateChoices
  | 20 => [(2,1),(2,3),(2,5),(4,5),(8,5)]
  | 21 => [(0,2),(1,0),(6,0)]
  | 22 => [(1,1),(7,1)]
  | 23 => [(4,1),(7,5)]
  | 24 => [(0,2),(0,3),(6,0)]
  | 25 => stateChoices
  | 26 => stateChoices
  | 27 => stateChoices
  | 28 => [(0,0),(6,3),(6,4)]
  | 29 => [(1,2),(3,2),(7,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2),(5,2),(8,2)]
  | 33 => [(5,0),(5,3),(8,0)]
  | 34 => stateChoices
  | 35 => stateChoices
  | 36 => [(0,2),(1,5),(7,5)]
  | 37 => [(0,3),(1,1),(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(7,4),(8,4)]
  | 42 => [(0,0),(1,4),(6,3),(6,4)]
  | 43 => stateChoices
  | 44 => [(4,2),(7,0),(8,0)]
  | 45 => [(5,3),(8,3)]
  | 46 => [(5,5),(8,5)]
  | 47 => [(1,0)]
  | 48 => [(2,1),(7,1)]
  | 49 => [(0,2),(1,5),(7,5)]
  | 50 => stateChoices
  | 51 => [(1,4),(7,4)]
  | 52 => [(0,5),(1,3),(6,3)]
  | 53 => [(4,4),(7,2),(8,2)]
  | 54 => [(0,0),(4,0),(5,0),(8,0)]
  | 55 => [(3,2),(4,5),(7,3)]
  | 56 => stateChoices
  | 57 => [(0,2),(6,0),(6,5)]
  | 58 => [(0,4),(1,1),(7,1)]
  | 59 => [(1,5),(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
def root4Node0Domains1Fast (v : Fin 61) : Option (List State) :=
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
  | 13 => some [(0,1),(1,4),(3,4),(7,4)]
  | 14 => some [(0,5),(6,2),(6,3)]
  | 15 => some [(4,4),(7,2),(8,4)]
  | 16 => some [(1,4),(6,4),(7,4)]
  | 17 => none
  | 18 => none
  | 19 => none
  | 20 => some [(2,1),(2,3),(2,5),(4,5),(8,5)]
  | 21 => some [(0,2),(1,0),(6,0)]
  | 22 => some [(1,1),(7,1)]
  | 23 => some [(4,1),(7,5)]
  | 24 => some [(0,2),(0,3),(6,0)]
  | 25 => none
  | 26 => none
  | 27 => none
  | 28 => some [(0,0),(6,3),(6,4)]
  | 29 => some [(1,2),(3,2),(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(5,2),(8,2)]
  | 33 => some [(5,0),(5,3),(8,0)]
  | 34 => none
  | 35 => none
  | 36 => some [(0,2),(1,5),(7,5)]
  | 37 => some [(0,3),(1,1),(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(1,4),(6,3),(6,4)]
  | 43 => none
  | 44 => some [(4,2),(7,0),(8,0)]
  | 45 => some [(5,3),(8,3)]
  | 46 => some [(5,5),(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(2,1),(7,1)]
  | 49 => some [(0,2),(1,5),(7,5)]
  | 50 => none
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(1,3),(6,3)]
  | 53 => some [(4,4),(7,2),(8,2)]
  | 54 => some [(0,0),(4,0),(5,0),(8,0)]
  | 55 => some [(3,2),(4,5),(7,3)]
  | 56 => none
  | 57 => some [(0,2),(6,0),(6,5)]
  | 58 => some [(0,4),(1,1),(7,1)]
  | 59 => some [(1,5),(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,1),(6,4)]
theorem root4Node0Domains1_fast_eq : root4Node0Domains1 = expandDomains root4Node0Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node0Domains1 v = expandDomains root4Node0Domains1Fast v from by decide) v
theorem root4Node0Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root4Node0Domains0 root4Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains0 root4Node0Domains1
    root4Node0Domains0Fast root4Node0Domains1Fast
    root4Node0Domains0_fast_eq root4Node0Domains1_fast_eq (by decide)
theorem root4Node0Step1_checked :
    checkReplacement table39 root4Node0Domains0 root4Node0Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node0Step1Chunk0_0_checked, root4Node0Step1Chunk0_1_checked, root4Node0Step1Chunk0_2_checked, root4Node0Step1Chunk0_3_checked, root4Node0Step1Chunk0_4_checked, root4Node0Step1Chunk0_5_checked, root4Node0Step1Chunk1_0_checked, root4Node0Step1Chunk1_1_checked, root4Node0Step1Chunk1_2_checked, root4Node0Step1Chunk1_3_checked, root4Node0Step1Chunk1_4_checked, root4Node0Step1Chunk1_5_checked, root4Node0Step1Chunk2_0_checked, root4Node0Step1Chunk2_1_checked, root4Node0Step1Chunk2_2_checked, root4Node0Step1Chunk2_3_checked, root4Node0Step1Chunk2_4_checked, root4Node0Step1Chunk2_5_checked, root4Node0Step1Chunk3_0_checked, root4Node0Step1Chunk3_1_checked, root4Node0Step1Chunk3_2_checked, root4Node0Step1Chunk3_3_checked, root4Node0Step1Chunk3_4_checked, root4Node0Step1Chunk3_5_checked, root4Node0Step1Chunk4_0_checked, root4Node0Step1Chunk4_1_checked, root4Node0Step1Chunk4_2_checked, root4Node0Step1Chunk4_3_checked, root4Node0Step1Chunk4_4_checked, root4Node0Step1Chunk4_5_checked, root4Node0Step1Chunk5_0_checked, root4Node0Step1Chunk5_1_checked, root4Node0Step1Chunk5_2_checked, root4Node0Step1Chunk5_3_checked, root4Node0Step1Chunk5_4_checked, root4Node0Step1Chunk5_5_checked, root4Node0Step1Chunk6_0_checked, root4Node0Step1Chunk6_1_checked, root4Node0Step1Chunk6_2_checked, root4Node0Step1Chunk6_3_checked, root4Node0Step1Chunk6_4_checked, root4Node0Step1Chunk6_5_checked, root4Node0Step1Chunk7_0_checked, root4Node0Step1Chunk7_1_checked, root4Node0Step1Chunk7_2_checked, root4Node0Step1Chunk7_3_checked, root4Node0Step1Chunk7_4_checked, root4Node0Step1Chunk7_5_checked, root4Node0Step1Chunk8_0_checked, root4Node0Step1Chunk8_1_checked, root4Node0Step1Chunk8_2_checked, root4Node0Step1Chunk8_3_checked, root4Node0Step1Chunk8_4_checked, root4Node0Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node0Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 1 => [(0,3),(1,1),(6,1),(7,1)]
  | 2 => [(4,1),(7,5),(8,1)]
  | 3 => [(0,2),(1,5),(6,0),(6,5)]
  | 4 => [(0,4),(1,1),(6,1),(7,1)]
  | 5 => [(0,5),(1,2),(1,3),(3,2),(6,3),(7,2),(7,3)]
  | 6 => [(2,0),(2,2),(4,0),(4,2)]
  | 7 => [(3,3),(5,3),(7,3)]
  | 8 => [(5,2),(5,5),(8,2),(8,5)]
  | 9 => [(7,0),(8,0)]
  | 10 => [(4,3),(7,3),(8,3)]
  | 11 => [(0,1),(0,2),(0,3),(6,0),(6,1),(6,5)]
  | 12 => [(0,4),(1,1),(3,1),(5,1),(6,2)]
  | 13 => [(0,1),(1,4),(3,4),(7,4)]
  | 14 => [(0,5),(6,2),(6,3)]
  | 15 => [(4,4),(7,2),(8,4)]
  | 16 => [(1,4),(6,4),(7,4)]
  | 17 => [(0,5),(1,2),(6,3)]
  | 18 => stateChoices
  | 19 => [(1,0),(3,0),(5,0),(5,3),(7,0),(8,3)]
  | 20 => [(2,1),(2,3),(2,5),(4,5),(8,5)]
  | 21 => [(0,2),(1,0),(6,0)]
  | 22 => [(1,1),(7,1)]
  | 23 => [(4,1),(7,5)]
  | 24 => [(0,2),(0,3),(6,0)]
  | 25 => stateChoices
  | 26 => stateChoices
  | 27 => stateChoices
  | 28 => [(0,0),(6,3),(6,4)]
  | 29 => [(1,2),(3,2),(7,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2),(5,2),(8,2)]
  | 33 => [(5,0),(5,3),(8,0)]
  | 34 => stateChoices
  | 35 => stateChoices
  | 36 => [(0,2),(1,5),(7,5)]
  | 37 => [(0,3),(1,1),(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(7,4),(8,4)]
  | 42 => [(0,0),(1,4),(6,3),(6,4)]
  | 43 => stateChoices
  | 44 => [(4,2),(7,0),(8,0)]
  | 45 => [(5,3),(8,3)]
  | 46 => [(5,5),(8,5)]
  | 47 => [(1,0)]
  | 48 => [(2,1),(7,1)]
  | 49 => [(0,2),(1,5),(7,5)]
  | 50 => stateChoices
  | 51 => [(1,4),(7,4)]
  | 52 => [(0,5),(1,3),(6,3)]
  | 53 => [(4,4),(7,2),(8,2)]
  | 54 => [(0,0),(4,0),(5,0),(8,0)]
  | 55 => [(3,2),(4,5),(7,3)]
  | 56 => stateChoices
  | 57 => [(0,2),(6,0),(6,5)]
  | 58 => [(0,4),(1,1),(7,1)]
  | 59 => [(1,5),(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
def root4Node0Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 1 => some [(0,3),(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(7,5),(8,1)]
  | 3 => some [(0,2),(1,5),(6,0),(6,5)]
  | 4 => some [(0,4),(1,1),(6,1),(7,1)]
  | 5 => some [(0,5),(1,2),(1,3),(3,2),(6,3),(7,2),(7,3)]
  | 6 => some [(2,0),(2,2),(4,0),(4,2)]
  | 7 => some [(3,3),(5,3),(7,3)]
  | 8 => some [(5,2),(5,5),(8,2),(8,5)]
  | 9 => some [(7,0),(8,0)]
  | 10 => some [(4,3),(7,3),(8,3)]
  | 11 => some [(0,1),(0,2),(0,3),(6,0),(6,1),(6,5)]
  | 12 => some [(0,4),(1,1),(3,1),(5,1),(6,2)]
  | 13 => some [(0,1),(1,4),(3,4),(7,4)]
  | 14 => some [(0,5),(6,2),(6,3)]
  | 15 => some [(4,4),(7,2),(8,4)]
  | 16 => some [(1,4),(6,4),(7,4)]
  | 17 => some [(0,5),(1,2),(6,3)]
  | 18 => none
  | 19 => some [(1,0),(3,0),(5,0),(5,3),(7,0),(8,3)]
  | 20 => some [(2,1),(2,3),(2,5),(4,5),(8,5)]
  | 21 => some [(0,2),(1,0),(6,0)]
  | 22 => some [(1,1),(7,1)]
  | 23 => some [(4,1),(7,5)]
  | 24 => some [(0,2),(0,3),(6,0)]
  | 25 => none
  | 26 => none
  | 27 => none
  | 28 => some [(0,0),(6,3),(6,4)]
  | 29 => some [(1,2),(3,2),(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(5,2),(8,2)]
  | 33 => some [(5,0),(5,3),(8,0)]
  | 34 => none
  | 35 => none
  | 36 => some [(0,2),(1,5),(7,5)]
  | 37 => some [(0,3),(1,1),(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(1,4),(6,3),(6,4)]
  | 43 => none
  | 44 => some [(4,2),(7,0),(8,0)]
  | 45 => some [(5,3),(8,3)]
  | 46 => some [(5,5),(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(2,1),(7,1)]
  | 49 => some [(0,2),(1,5),(7,5)]
  | 50 => none
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(1,3),(6,3)]
  | 53 => some [(4,4),(7,2),(8,2)]
  | 54 => some [(0,0),(4,0),(5,0),(8,0)]
  | 55 => some [(3,2),(4,5),(7,3)]
  | 56 => none
  | 57 => some [(0,2),(6,0),(6,5)]
  | 58 => some [(0,4),(1,1),(7,1)]
  | 59 => some [(1,5),(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,1),(6,4)]
theorem root4Node0Domains2_fast_eq : root4Node0Domains2 = expandDomains root4Node0Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node0Domains2 v = expandDomains root4Node0Domains2Fast v from by decide) v
theorem root4Node0Step2Chunk0_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_0⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk0_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_1⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk0_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_2⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk0_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_3⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk0_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_4⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk0_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_5⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk1_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_0⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk1_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_1⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk1_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_2⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk1_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_3⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk1_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_4⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk1_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_5⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk2_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_0⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk2_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_1⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk2_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_2⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk2_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_3⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk2_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_4⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk2_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_5⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk3_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_0⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk3_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_1⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk3_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_2⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk3_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_3⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk3_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_4⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk3_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_5⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk4_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_0⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk4_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_1⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk4_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_2⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk4_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_3⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk4_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_4⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk4_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_5⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk5_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_0⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk5_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_1⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk5_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_2⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk5_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_3⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk5_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_4⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk5_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_5⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk6_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_0⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk6_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_1⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk6_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_2⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk6_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_3⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk6_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_4⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk6_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_5⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk7_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_0⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk7_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_1⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk7_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_2⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk7_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_3⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk7_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_4⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk7_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_5⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk8_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_0⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk8_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_1⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk8_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_2⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk8_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_3⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk8_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_4⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2Chunk8_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_5⟩
      root4Node0Domains1 root4Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains1 root4Node0Domains2
    root4Node0Domains1Fast root4Node0Domains2Fast
    root4Node0Domains1_fast_eq root4Node0Domains2_fast_eq (by decide)
theorem root4Node0Step2_checked :
    checkReplacement table14 root4Node0Domains1 root4Node0Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node0Step2Chunk0_0_checked, root4Node0Step2Chunk0_1_checked, root4Node0Step2Chunk0_2_checked, root4Node0Step2Chunk0_3_checked, root4Node0Step2Chunk0_4_checked, root4Node0Step2Chunk0_5_checked, root4Node0Step2Chunk1_0_checked, root4Node0Step2Chunk1_1_checked, root4Node0Step2Chunk1_2_checked, root4Node0Step2Chunk1_3_checked, root4Node0Step2Chunk1_4_checked, root4Node0Step2Chunk1_5_checked, root4Node0Step2Chunk2_0_checked, root4Node0Step2Chunk2_1_checked, root4Node0Step2Chunk2_2_checked, root4Node0Step2Chunk2_3_checked, root4Node0Step2Chunk2_4_checked, root4Node0Step2Chunk2_5_checked, root4Node0Step2Chunk3_0_checked, root4Node0Step2Chunk3_1_checked, root4Node0Step2Chunk3_2_checked, root4Node0Step2Chunk3_3_checked, root4Node0Step2Chunk3_4_checked, root4Node0Step2Chunk3_5_checked, root4Node0Step2Chunk4_0_checked, root4Node0Step2Chunk4_1_checked, root4Node0Step2Chunk4_2_checked, root4Node0Step2Chunk4_3_checked, root4Node0Step2Chunk4_4_checked, root4Node0Step2Chunk4_5_checked, root4Node0Step2Chunk5_0_checked, root4Node0Step2Chunk5_1_checked, root4Node0Step2Chunk5_2_checked, root4Node0Step2Chunk5_3_checked, root4Node0Step2Chunk5_4_checked, root4Node0Step2Chunk5_5_checked, root4Node0Step2Chunk6_0_checked, root4Node0Step2Chunk6_1_checked, root4Node0Step2Chunk6_2_checked, root4Node0Step2Chunk6_3_checked, root4Node0Step2Chunk6_4_checked, root4Node0Step2Chunk6_5_checked, root4Node0Step2Chunk7_0_checked, root4Node0Step2Chunk7_1_checked, root4Node0Step2Chunk7_2_checked, root4Node0Step2Chunk7_3_checked, root4Node0Step2Chunk7_4_checked, root4Node0Step2Chunk7_5_checked, root4Node0Step2Chunk8_0_checked, root4Node0Step2Chunk8_1_checked, root4Node0Step2Chunk8_2_checked, root4Node0Step2Chunk8_3_checked, root4Node0Step2Chunk8_4_checked, root4Node0Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node0Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 1 => [(0,3),(1,1),(6,1),(7,1)]
  | 2 => [(4,1),(7,5),(8,1)]
  | 3 => [(0,2),(1,5),(6,0),(6,5)]
  | 4 => [(0,4),(1,1),(6,1),(7,1)]
  | 5 => [(0,5),(1,2),(1,3),(3,2),(6,3),(7,2),(7,3)]
  | 6 => [(2,0),(2,2),(4,0),(4,2)]
  | 7 => [(3,3),(5,3),(7,3)]
  | 8 => [(5,2),(5,5),(8,2),(8,5)]
  | 9 => [(7,0),(8,0)]
  | 10 => [(4,3),(7,3),(8,3)]
  | 11 => [(0,1),(0,2),(0,3),(6,0),(6,1),(6,5)]
  | 12 => [(0,4),(1,1),(3,1),(5,1),(6,2)]
  | 13 => [(0,1),(1,4),(3,4),(7,4)]
  | 14 => [(0,5),(6,2),(6,3)]
  | 15 => [(4,4),(7,2),(8,4)]
  | 16 => [(1,4),(6,4),(7,4)]
  | 17 => [(0,5),(1,2),(6,3)]
  | 18 => [(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 19 => [(1,0),(3,0),(5,0),(5,3),(7,0),(8,3)]
  | 20 => [(2,1),(2,3),(2,5),(4,5),(8,5)]
  | 21 => [(0,2),(1,0),(6,0)]
  | 22 => [(1,1),(7,1)]
  | 23 => [(4,1),(7,5)]
  | 24 => [(0,2),(0,3),(6,0)]
  | 25 => stateChoices
  | 26 => [(0,5),(1,2),(6,2),(7,2)]
  | 27 => [(4,4),(7,4),(8,4)]
  | 28 => [(0,0),(6,3),(6,4)]
  | 29 => [(1,2),(3,2),(7,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2),(5,2),(8,2)]
  | 33 => [(5,0),(5,3),(8,0)]
  | 34 => stateChoices
  | 35 => [(4,1),(7,1),(8,1)]
  | 36 => [(0,2),(1,5),(7,5)]
  | 37 => [(0,3),(1,1),(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(7,4),(8,4)]
  | 42 => [(0,0),(1,4),(6,3),(6,4)]
  | 43 => [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 44 => [(4,2),(7,0),(8,0)]
  | 45 => [(5,3),(8,3)]
  | 46 => [(5,5),(8,5)]
  | 47 => [(1,0)]
  | 48 => [(2,1),(7,1)]
  | 49 => [(0,2),(1,5),(7,5)]
  | 50 => [(1,2),(4,4),(5,4),(7,2),(8,4)]
  | 51 => [(1,4),(7,4)]
  | 52 => [(0,5),(1,3),(6,3)]
  | 53 => [(4,4),(7,2),(8,2)]
  | 54 => [(0,0),(4,0),(5,0),(8,0)]
  | 55 => [(3,2),(4,5),(7,3)]
  | 56 => [(4,1),(7,5),(8,1)]
  | 57 => [(0,2),(6,0),(6,5)]
  | 58 => [(0,4),(1,1),(7,1)]
  | 59 => [(1,5),(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
def root4Node0Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 1 => some [(0,3),(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(7,5),(8,1)]
  | 3 => some [(0,2),(1,5),(6,0),(6,5)]
  | 4 => some [(0,4),(1,1),(6,1),(7,1)]
  | 5 => some [(0,5),(1,2),(1,3),(3,2),(6,3),(7,2),(7,3)]
  | 6 => some [(2,0),(2,2),(4,0),(4,2)]
  | 7 => some [(3,3),(5,3),(7,3)]
  | 8 => some [(5,2),(5,5),(8,2),(8,5)]
  | 9 => some [(7,0),(8,0)]
  | 10 => some [(4,3),(7,3),(8,3)]
  | 11 => some [(0,1),(0,2),(0,3),(6,0),(6,1),(6,5)]
  | 12 => some [(0,4),(1,1),(3,1),(5,1),(6,2)]
  | 13 => some [(0,1),(1,4),(3,4),(7,4)]
  | 14 => some [(0,5),(6,2),(6,3)]
  | 15 => some [(4,4),(7,2),(8,4)]
  | 16 => some [(1,4),(6,4),(7,4)]
  | 17 => some [(0,5),(1,2),(6,3)]
  | 18 => some [(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 19 => some [(1,0),(3,0),(5,0),(5,3),(7,0),(8,3)]
  | 20 => some [(2,1),(2,3),(2,5),(4,5),(8,5)]
  | 21 => some [(0,2),(1,0),(6,0)]
  | 22 => some [(1,1),(7,1)]
  | 23 => some [(4,1),(7,5)]
  | 24 => some [(0,2),(0,3),(6,0)]
  | 25 => none
  | 26 => some [(0,5),(1,2),(6,2),(7,2)]
  | 27 => some [(4,4),(7,4),(8,4)]
  | 28 => some [(0,0),(6,3),(6,4)]
  | 29 => some [(1,2),(3,2),(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(5,2),(8,2)]
  | 33 => some [(5,0),(5,3),(8,0)]
  | 34 => none
  | 35 => some [(4,1),(7,1),(8,1)]
  | 36 => some [(0,2),(1,5),(7,5)]
  | 37 => some [(0,3),(1,1),(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(1,4),(6,3),(6,4)]
  | 43 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 44 => some [(4,2),(7,0),(8,0)]
  | 45 => some [(5,3),(8,3)]
  | 46 => some [(5,5),(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(2,1),(7,1)]
  | 49 => some [(0,2),(1,5),(7,5)]
  | 50 => some [(1,2),(4,4),(5,4),(7,2),(8,4)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(1,3),(6,3)]
  | 53 => some [(4,4),(7,2),(8,2)]
  | 54 => some [(0,0),(4,0),(5,0),(8,0)]
  | 55 => some [(3,2),(4,5),(7,3)]
  | 56 => some [(4,1),(7,5),(8,1)]
  | 57 => some [(0,2),(6,0),(6,5)]
  | 58 => some [(0,4),(1,1),(7,1)]
  | 59 => some [(1,5),(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,1),(6,4)]
theorem root4Node0Domains3_fast_eq : root4Node0Domains3 = expandDomains root4Node0Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node0Domains3 v = expandDomains root4Node0Domains3Fast v from by decide) v
theorem root4Node0Step3Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root4Node0Domains2 root4Node0Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains2 root4Node0Domains3
    root4Node0Domains2Fast root4Node0Domains3Fast
    root4Node0Domains2_fast_eq root4Node0Domains3_fast_eq (by decide)
theorem root4Node0Step3_checked :
    checkReplacement table35 root4Node0Domains2 root4Node0Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node0Step3Chunk0_0_checked, root4Node0Step3Chunk0_1_checked, root4Node0Step3Chunk0_2_checked, root4Node0Step3Chunk0_3_checked, root4Node0Step3Chunk0_4_checked, root4Node0Step3Chunk0_5_checked, root4Node0Step3Chunk1_0_checked, root4Node0Step3Chunk1_1_checked, root4Node0Step3Chunk1_2_checked, root4Node0Step3Chunk1_3_checked, root4Node0Step3Chunk1_4_checked, root4Node0Step3Chunk1_5_checked, root4Node0Step3Chunk2_0_checked, root4Node0Step3Chunk2_1_checked, root4Node0Step3Chunk2_2_checked, root4Node0Step3Chunk2_3_checked, root4Node0Step3Chunk2_4_checked, root4Node0Step3Chunk2_5_checked, root4Node0Step3Chunk3_0_checked, root4Node0Step3Chunk3_1_checked, root4Node0Step3Chunk3_2_checked, root4Node0Step3Chunk3_3_checked, root4Node0Step3Chunk3_4_checked, root4Node0Step3Chunk3_5_checked, root4Node0Step3Chunk4_0_checked, root4Node0Step3Chunk4_1_checked, root4Node0Step3Chunk4_2_checked, root4Node0Step3Chunk4_3_checked, root4Node0Step3Chunk4_4_checked, root4Node0Step3Chunk4_5_checked, root4Node0Step3Chunk5_0_checked, root4Node0Step3Chunk5_1_checked, root4Node0Step3Chunk5_2_checked, root4Node0Step3Chunk5_3_checked, root4Node0Step3Chunk5_4_checked, root4Node0Step3Chunk5_5_checked, root4Node0Step3Chunk6_0_checked, root4Node0Step3Chunk6_1_checked, root4Node0Step3Chunk6_2_checked, root4Node0Step3Chunk6_3_checked, root4Node0Step3Chunk6_4_checked, root4Node0Step3Chunk6_5_checked, root4Node0Step3Chunk7_0_checked, root4Node0Step3Chunk7_1_checked, root4Node0Step3Chunk7_2_checked, root4Node0Step3Chunk7_3_checked, root4Node0Step3Chunk7_4_checked, root4Node0Step3Chunk7_5_checked, root4Node0Step3Chunk8_0_checked, root4Node0Step3Chunk8_1_checked, root4Node0Step3Chunk8_2_checked, root4Node0Step3Chunk8_3_checked, root4Node0Step3Chunk8_4_checked, root4Node0Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node0Domains4 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 1 => [(0,3),(1,1),(6,1),(7,1)]
  | 2 => [(4,1),(7,5),(8,1)]
  | 3 => [(0,2),(1,5),(6,0),(6,5)]
  | 4 => [(0,4),(1,1),(6,1),(7,1)]
  | 5 => [(0,5),(1,2),(1,3),(3,2),(6,3),(7,2),(7,3)]
  | 6 => [(2,0),(2,2),(4,0),(4,2)]
  | 7 => [(3,3),(5,3),(7,3)]
  | 8 => [(5,2),(5,5),(8,2),(8,5)]
  | 9 => [(7,0),(8,0)]
  | 10 => [(4,3),(7,3),(8,3)]
  | 11 => [(0,1),(0,2),(0,3),(6,0),(6,1),(6,5)]
  | 12 => [(0,4),(1,1),(3,1),(5,1),(6,2)]
  | 13 => [(0,1),(1,4),(3,4),(7,4)]
  | 14 => [(0,5),(6,2),(6,3)]
  | 15 => [(4,4),(7,2),(8,4)]
  | 16 => [(1,4),(6,4),(7,4)]
  | 17 => [(0,5),(1,2),(6,3)]
  | 18 => [(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 19 => [(1,0),(3,0),(5,0),(5,3),(7,0),(8,3)]
  | 20 => [(2,1),(2,3),(2,5),(4,5),(8,5)]
  | 21 => [(0,2),(1,0),(6,0)]
  | 22 => [(1,1),(7,1)]
  | 23 => [(4,1),(7,5)]
  | 24 => [(0,2),(0,3),(6,0)]
  | 25 => [(1,1),(3,1),(7,1),(8,1)]
  | 26 => [(0,5),(1,2),(6,2),(7,2)]
  | 27 => [(4,4),(7,4),(8,4)]
  | 28 => [(0,0),(6,3),(6,4)]
  | 29 => [(1,2),(3,2),(7,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2),(5,2),(8,2)]
  | 33 => [(5,0),(5,3),(8,0)]
  | 34 => [(4,5),(7,3),(8,3),(8,5)]
  | 35 => [(4,1),(7,1),(8,1)]
  | 36 => [(0,2),(1,5),(7,5)]
  | 37 => [(0,3),(1,1),(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(7,4),(8,4)]
  | 42 => [(0,0),(1,4),(6,3),(6,4)]
  | 43 => [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 44 => [(4,2),(7,0),(8,0)]
  | 45 => [(5,3),(8,3)]
  | 46 => [(5,5),(8,5)]
  | 47 => [(1,0)]
  | 48 => [(2,1),(7,1)]
  | 49 => [(0,2),(1,5),(7,5)]
  | 50 => [(1,2),(4,4),(5,4),(7,2),(8,4)]
  | 51 => [(1,4),(7,4)]
  | 52 => [(0,5),(1,3),(6,3)]
  | 53 => [(4,4),(7,2),(8,2)]
  | 54 => [(0,0),(4,0),(5,0),(8,0)]
  | 55 => [(3,2),(4,5),(7,3)]
  | 56 => [(4,1),(7,5),(8,1)]
  | 57 => [(0,2),(6,0),(6,5)]
  | 58 => [(0,4),(1,1),(7,1)]
  | 59 => [(1,5),(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
def root4Node0Domains4Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 1 => some [(0,3),(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(7,5),(8,1)]
  | 3 => some [(0,2),(1,5),(6,0),(6,5)]
  | 4 => some [(0,4),(1,1),(6,1),(7,1)]
  | 5 => some [(0,5),(1,2),(1,3),(3,2),(6,3),(7,2),(7,3)]
  | 6 => some [(2,0),(2,2),(4,0),(4,2)]
  | 7 => some [(3,3),(5,3),(7,3)]
  | 8 => some [(5,2),(5,5),(8,2),(8,5)]
  | 9 => some [(7,0),(8,0)]
  | 10 => some [(4,3),(7,3),(8,3)]
  | 11 => some [(0,1),(0,2),(0,3),(6,0),(6,1),(6,5)]
  | 12 => some [(0,4),(1,1),(3,1),(5,1),(6,2)]
  | 13 => some [(0,1),(1,4),(3,4),(7,4)]
  | 14 => some [(0,5),(6,2),(6,3)]
  | 15 => some [(4,4),(7,2),(8,4)]
  | 16 => some [(1,4),(6,4),(7,4)]
  | 17 => some [(0,5),(1,2),(6,3)]
  | 18 => some [(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 19 => some [(1,0),(3,0),(5,0),(5,3),(7,0),(8,3)]
  | 20 => some [(2,1),(2,3),(2,5),(4,5),(8,5)]
  | 21 => some [(0,2),(1,0),(6,0)]
  | 22 => some [(1,1),(7,1)]
  | 23 => some [(4,1),(7,5)]
  | 24 => some [(0,2),(0,3),(6,0)]
  | 25 => some [(1,1),(3,1),(7,1),(8,1)]
  | 26 => some [(0,5),(1,2),(6,2),(7,2)]
  | 27 => some [(4,4),(7,4),(8,4)]
  | 28 => some [(0,0),(6,3),(6,4)]
  | 29 => some [(1,2),(3,2),(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(5,2),(8,2)]
  | 33 => some [(5,0),(5,3),(8,0)]
  | 34 => some [(4,5),(7,3),(8,3),(8,5)]
  | 35 => some [(4,1),(7,1),(8,1)]
  | 36 => some [(0,2),(1,5),(7,5)]
  | 37 => some [(0,3),(1,1),(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(1,4),(6,3),(6,4)]
  | 43 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 44 => some [(4,2),(7,0),(8,0)]
  | 45 => some [(5,3),(8,3)]
  | 46 => some [(5,5),(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(2,1),(7,1)]
  | 49 => some [(0,2),(1,5),(7,5)]
  | 50 => some [(1,2),(4,4),(5,4),(7,2),(8,4)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(1,3),(6,3)]
  | 53 => some [(4,4),(7,2),(8,2)]
  | 54 => some [(0,0),(4,0),(5,0),(8,0)]
  | 55 => some [(3,2),(4,5),(7,3)]
  | 56 => some [(4,1),(7,5),(8,1)]
  | 57 => some [(0,2),(6,0),(6,5)]
  | 58 => some [(0,4),(1,1),(7,1)]
  | 59 => some [(1,5),(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,1),(6,4)]
theorem root4Node0Domains4_fast_eq : root4Node0Domains4 = expandDomains root4Node0Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node0Domains4 v = expandDomains root4Node0Domains4Fast v from by decide) v
theorem root4Node0Step4Chunk0_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_0⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk0_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_1⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk0_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_2⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk0_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_3⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk0_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_4⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk0_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_5⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk1_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_0⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk1_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_1⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk1_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_2⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk1_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_3⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk1_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_4⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk1_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_5⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk2_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_0⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk2_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_1⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk2_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_2⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk2_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_3⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk2_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_4⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk2_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_5⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk3_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_0⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk3_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_1⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk3_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_2⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk3_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_3⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk3_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_4⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk3_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_5⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk4_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_0⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk4_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_1⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk4_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_2⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk4_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_3⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk4_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_4⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk4_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_5⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk5_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_0⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk5_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_1⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk5_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_2⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk5_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_3⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk5_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_4⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk5_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_5⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk6_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_0⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk6_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_1⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk6_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_2⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk6_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_3⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk6_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_4⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk6_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_5⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk7_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_0⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk7_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_1⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk7_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_2⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk7_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_3⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk7_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_4⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk7_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_5⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk8_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_0⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk8_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_1⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk8_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_2⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk8_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_3⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk8_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_4⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4Chunk8_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_5⟩
      root4Node0Domains3 root4Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node0Domains3 root4Node0Domains4
    root4Node0Domains3Fast root4Node0Domains4Fast
    root4Node0Domains3_fast_eq root4Node0Domains4_fast_eq (by decide)
theorem root4Node0Step4_checked :
    checkReplacement table10 root4Node0Domains3 root4Node0Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node0Step4Chunk0_0_checked, root4Node0Step4Chunk0_1_checked, root4Node0Step4Chunk0_2_checked, root4Node0Step4Chunk0_3_checked, root4Node0Step4Chunk0_4_checked, root4Node0Step4Chunk0_5_checked, root4Node0Step4Chunk1_0_checked, root4Node0Step4Chunk1_1_checked, root4Node0Step4Chunk1_2_checked, root4Node0Step4Chunk1_3_checked, root4Node0Step4Chunk1_4_checked, root4Node0Step4Chunk1_5_checked, root4Node0Step4Chunk2_0_checked, root4Node0Step4Chunk2_1_checked, root4Node0Step4Chunk2_2_checked, root4Node0Step4Chunk2_3_checked, root4Node0Step4Chunk2_4_checked, root4Node0Step4Chunk2_5_checked, root4Node0Step4Chunk3_0_checked, root4Node0Step4Chunk3_1_checked, root4Node0Step4Chunk3_2_checked, root4Node0Step4Chunk3_3_checked, root4Node0Step4Chunk3_4_checked, root4Node0Step4Chunk3_5_checked, root4Node0Step4Chunk4_0_checked, root4Node0Step4Chunk4_1_checked, root4Node0Step4Chunk4_2_checked, root4Node0Step4Chunk4_3_checked, root4Node0Step4Chunk4_4_checked, root4Node0Step4Chunk4_5_checked, root4Node0Step4Chunk5_0_checked, root4Node0Step4Chunk5_1_checked, root4Node0Step4Chunk5_2_checked, root4Node0Step4Chunk5_3_checked, root4Node0Step4Chunk5_4_checked, root4Node0Step4Chunk5_5_checked, root4Node0Step4Chunk6_0_checked, root4Node0Step4Chunk6_1_checked, root4Node0Step4Chunk6_2_checked, root4Node0Step4Chunk6_3_checked, root4Node0Step4Chunk6_4_checked, root4Node0Step4Chunk6_5_checked, root4Node0Step4Chunk7_0_checked, root4Node0Step4Chunk7_1_checked, root4Node0Step4Chunk7_2_checked, root4Node0Step4Chunk7_3_checked, root4Node0Step4Chunk7_4_checked, root4Node0Step4Chunk7_5_checked, root4Node0Step4Chunk8_0_checked, root4Node0Step4Chunk8_1_checked, root4Node0Step4Chunk8_2_checked, root4Node0Step4Chunk8_3_checked, root4Node0Step4Chunk8_4_checked, root4Node0Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node1Domains0 : Domains 61 State := restrict root4Node0Domains4 9 (7,0)
def root4Node1Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 1 => some [(0,3),(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(7,5),(8,1)]
  | 3 => some [(0,2),(1,5),(6,0),(6,5)]
  | 4 => some [(0,4),(1,1),(6,1),(7,1)]
  | 5 => some [(0,5),(1,2),(1,3),(3,2),(6,3),(7,2),(7,3)]
  | 6 => some [(2,0),(2,2),(4,0),(4,2)]
  | 7 => some [(3,3),(5,3),(7,3)]
  | 8 => some [(5,2),(5,5),(8,2),(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3),(7,3),(8,3)]
  | 11 => some [(0,1),(0,2),(0,3),(6,0),(6,1),(6,5)]
  | 12 => some [(0,4),(1,1),(3,1),(5,1),(6,2)]
  | 13 => some [(0,1),(1,4),(3,4),(7,4)]
  | 14 => some [(0,5),(6,2),(6,3)]
  | 15 => some [(4,4),(7,2),(8,4)]
  | 16 => some [(1,4),(6,4),(7,4)]
  | 17 => some [(0,5),(1,2),(6,3)]
  | 18 => some [(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 19 => some [(1,0),(3,0),(5,0),(5,3),(7,0),(8,3)]
  | 20 => some [(2,1),(2,3),(2,5),(4,5),(8,5)]
  | 21 => some [(0,2),(1,0),(6,0)]
  | 22 => some [(1,1),(7,1)]
  | 23 => some [(4,1),(7,5)]
  | 24 => some [(0,2),(0,3),(6,0)]
  | 25 => some [(1,1),(3,1),(7,1),(8,1)]
  | 26 => some [(0,5),(1,2),(6,2),(7,2)]
  | 27 => some [(4,4),(7,4),(8,4)]
  | 28 => some [(0,0),(6,3),(6,4)]
  | 29 => some [(1,2),(3,2),(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(5,2),(8,2)]
  | 33 => some [(5,0),(5,3),(8,0)]
  | 34 => some [(4,5),(7,3),(8,3),(8,5)]
  | 35 => some [(4,1),(7,1),(8,1)]
  | 36 => some [(0,2),(1,5),(7,5)]
  | 37 => some [(0,3),(1,1),(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(1,4),(6,3),(6,4)]
  | 43 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 44 => some [(4,2),(7,0),(8,0)]
  | 45 => some [(5,3),(8,3)]
  | 46 => some [(5,5),(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(2,1),(7,1)]
  | 49 => some [(0,2),(1,5),(7,5)]
  | 50 => some [(1,2),(4,4),(5,4),(7,2),(8,4)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(1,3),(6,3)]
  | 53 => some [(4,4),(7,2),(8,2)]
  | 54 => some [(0,0),(4,0),(5,0),(8,0)]
  | 55 => some [(3,2),(4,5),(7,3)]
  | 56 => some [(4,1),(7,5),(8,1)]
  | 57 => some [(0,2),(6,0),(6,5)]
  | 58 => some [(0,4),(1,1),(7,1)]
  | 59 => some [(1,5),(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,1),(6,4)]
theorem root4Node1Domains0_fast_eq : root4Node1Domains0 = expandDomains root4Node1Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node1Domains0 v = expandDomains root4Node1Domains0Fast v from by decide) v
def root4Node1Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(1,5),(6,5)]
  | 4 => [(0,4),(1,1),(6,1),(7,1)]
  | 5 => [(1,3),(7,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(5,5),(8,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3),(7,3),(8,3)]
  | 11 => [(0,1),(6,5)]
  | 12 => [(0,4),(6,2)]
  | 13 => [(1,4),(3,4),(7,4)]
  | 14 => [(0,5),(6,3)]
  | 15 => [(4,4),(7,2)]
  | 16 => [(1,4),(7,4)]
  | 17 => [(0,5),(1,2),(6,3)]
  | 18 => [(5,5)]
  | 19 => [(1,0),(3,0),(7,0)]
  | 20 => [(2,1),(2,3),(2,5)]
  | 21 => [(0,2),(6,0)]
  | 22 => [(1,1),(7,1)]
  | 23 => [(4,1),(7,5)]
  | 24 => [(0,2),(6,0)]
  | 25 => [(1,1),(3,1),(7,1),(8,1)]
  | 26 => [(0,5),(1,2),(6,2),(7,2)]
  | 27 => [(4,4)]
  | 28 => [(0,0),(6,4)]
  | 29 => [(1,2),(3,2),(7,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2),(8,2)]
  | 33 => [(5,0),(5,3),(8,0)]
  | 34 => [(4,5),(7,3),(8,3),(8,5)]
  | 35 => [(4,1),(7,1),(8,1)]
  | 36 => [(1,5),(7,5)]
  | 37 => [(0,3),(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(7,4),(8,4)]
  | 42 => [(0,0),(1,4),(6,3),(6,4)]
  | 43 => [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 44 => [(4,2),(7,0)]
  | 45 => [(5,3),(8,3)]
  | 46 => [(8,5)]
  | 47 => [(1,0)]
  | 48 => [(2,1),(7,1)]
  | 49 => [(0,2),(1,5),(7,5)]
  | 50 => [(1,2),(4,4),(5,4),(7,2),(8,4)]
  | 51 => [(1,4),(7,4)]
  | 52 => [(0,5),(1,3),(6,3)]
  | 53 => [(4,4),(7,2),(8,2)]
  | 54 => [(0,0),(4,0),(5,0),(8,0)]
  | 55 => [(3,2),(4,5),(7,3)]
  | 56 => [(4,1),(7,5),(8,1)]
  | 57 => [(0,2),(6,0),(6,5)]
  | 58 => [(0,4),(1,1),(7,1)]
  | 59 => [(1,5),(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
def root4Node1Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5),(6,5)]
  | 4 => some [(0,4),(1,1),(6,1),(7,1)]
  | 5 => some [(1,3),(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(5,5),(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3),(7,3),(8,3)]
  | 11 => some [(0,1),(6,5)]
  | 12 => some [(0,4),(6,2)]
  | 13 => some [(1,4),(3,4),(7,4)]
  | 14 => some [(0,5),(6,3)]
  | 15 => some [(4,4),(7,2)]
  | 16 => some [(1,4),(7,4)]
  | 17 => some [(0,5),(1,2),(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(1,0),(3,0),(7,0)]
  | 20 => some [(2,1),(2,3),(2,5)]
  | 21 => some [(0,2),(6,0)]
  | 22 => some [(1,1),(7,1)]
  | 23 => some [(4,1),(7,5)]
  | 24 => some [(0,2),(6,0)]
  | 25 => some [(1,1),(3,1),(7,1),(8,1)]
  | 26 => some [(0,5),(1,2),(6,2),(7,2)]
  | 27 => some [(4,4)]
  | 28 => some [(0,0),(6,4)]
  | 29 => some [(1,2),(3,2),(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2),(8,2)]
  | 33 => some [(5,0),(5,3),(8,0)]
  | 34 => some [(4,5),(7,3),(8,3),(8,5)]
  | 35 => some [(4,1),(7,1),(8,1)]
  | 36 => some [(1,5),(7,5)]
  | 37 => some [(0,3),(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(1,4),(6,3),(6,4)]
  | 43 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 44 => some [(4,2),(7,0)]
  | 45 => some [(5,3),(8,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(2,1),(7,1)]
  | 49 => some [(0,2),(1,5),(7,5)]
  | 50 => some [(1,2),(4,4),(5,4),(7,2),(8,4)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(1,3),(6,3)]
  | 53 => some [(4,4),(7,2),(8,2)]
  | 54 => some [(0,0),(4,0),(5,0),(8,0)]
  | 55 => some [(3,2),(4,5),(7,3)]
  | 56 => some [(4,1),(7,5),(8,1)]
  | 57 => some [(0,2),(6,0),(6,5)]
  | 58 => some [(0,4),(1,1),(7,1)]
  | 59 => some [(1,5),(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,1),(6,4)]
theorem root4Node1Domains1_fast_eq : root4Node1Domains1 = expandDomains root4Node1Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node1Domains1 v = expandDomains root4Node1Domains1Fast v from by decide) v
theorem root4Node1Step1Chunk0_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_0⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk0_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_1⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk0_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_2⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk0_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_3⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk0_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_4⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk0_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_5⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk1_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_0⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk1_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_1⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk1_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_2⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk1_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_3⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk1_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_4⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk1_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_5⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk2_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_0⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk2_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_1⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk2_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_2⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk2_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_3⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk2_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_4⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk2_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_5⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk3_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_0⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk3_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_1⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk3_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_2⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk3_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_3⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk3_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_4⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk3_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_5⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk4_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_0⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk4_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_1⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk4_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_2⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk4_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_3⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk4_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_4⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk4_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_5⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk5_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_0⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk5_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_1⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk5_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_2⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk5_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_3⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk5_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_4⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk5_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_5⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk6_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_0⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk6_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_1⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk6_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_2⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk6_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_3⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk6_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_4⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk6_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_5⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk7_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_0⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk7_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_1⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk7_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_2⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk7_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_3⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk7_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_4⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk7_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_5⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk8_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_0⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk8_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_1⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk8_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_2⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk8_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_3⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk8_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_4⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk8_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_5⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1_checked :
    checkReplacement table21 root4Node1Domains0 root4Node1Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node1Step1Chunk0_0_checked, root4Node1Step1Chunk0_1_checked, root4Node1Step1Chunk0_2_checked, root4Node1Step1Chunk0_3_checked, root4Node1Step1Chunk0_4_checked, root4Node1Step1Chunk0_5_checked, root4Node1Step1Chunk1_0_checked, root4Node1Step1Chunk1_1_checked, root4Node1Step1Chunk1_2_checked, root4Node1Step1Chunk1_3_checked, root4Node1Step1Chunk1_4_checked, root4Node1Step1Chunk1_5_checked, root4Node1Step1Chunk2_0_checked, root4Node1Step1Chunk2_1_checked, root4Node1Step1Chunk2_2_checked, root4Node1Step1Chunk2_3_checked, root4Node1Step1Chunk2_4_checked, root4Node1Step1Chunk2_5_checked, root4Node1Step1Chunk3_0_checked, root4Node1Step1Chunk3_1_checked, root4Node1Step1Chunk3_2_checked, root4Node1Step1Chunk3_3_checked, root4Node1Step1Chunk3_4_checked, root4Node1Step1Chunk3_5_checked, root4Node1Step1Chunk4_0_checked, root4Node1Step1Chunk4_1_checked, root4Node1Step1Chunk4_2_checked, root4Node1Step1Chunk4_3_checked, root4Node1Step1Chunk4_4_checked, root4Node1Step1Chunk4_5_checked, root4Node1Step1Chunk5_0_checked, root4Node1Step1Chunk5_1_checked, root4Node1Step1Chunk5_2_checked, root4Node1Step1Chunk5_3_checked, root4Node1Step1Chunk5_4_checked, root4Node1Step1Chunk5_5_checked, root4Node1Step1Chunk6_0_checked, root4Node1Step1Chunk6_1_checked, root4Node1Step1Chunk6_2_checked, root4Node1Step1Chunk6_3_checked, root4Node1Step1Chunk6_4_checked, root4Node1Step1Chunk6_5_checked, root4Node1Step1Chunk7_0_checked, root4Node1Step1Chunk7_1_checked, root4Node1Step1Chunk7_2_checked, root4Node1Step1Chunk7_3_checked, root4Node1Step1Chunk7_4_checked, root4Node1Step1Chunk7_5_checked, root4Node1Step1Chunk8_0_checked, root4Node1Step1Chunk8_1_checked, root4Node1Step1Chunk8_2_checked, root4Node1Step1Chunk8_3_checked, root4Node1Step1Chunk8_4_checked, root4Node1Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
