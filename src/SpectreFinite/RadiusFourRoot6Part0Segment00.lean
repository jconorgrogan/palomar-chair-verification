module

public import SpectreFinite.RadiusFourRoot6Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable0
public import SpectreFinite.RadiusFourTable23
public import SpectreFinite.RadiusFourTable29
public import SpectreFinite.RadiusFourTable39
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node0Domains0 : Domains 61 State := domains (6,0)
def root6Node0Domains0Fast (v : Fin 61) : Option (List State) :=
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
  | 30 => some [(6,0)]
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
theorem root6Node0Domains0_fast_eq : root6Node0Domains0 = expandDomains root6Node0Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node0Domains0 v = expandDomains root6Node0Domains0Fast v from by decide) v
def root6Node0Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => stateChoices
  | 2 => stateChoices
  | 3 => stateChoices
  | 4 => stateChoices
  | 5 => [(4,1),(4,3),(8,1)]
  | 6 => [(0,2),(1,5),(6,5),(7,5)]
  | 7 => [(0,3),(0,4),(1,1),(6,1)]
  | 8 => [(5,1),(5,4),(8,1)]
  | 9 => stateChoices
  | 10 => stateChoices
  | 11 => [(1,3),(3,3),(5,3),(7,3),(7,4),(8,3)]
  | 12 => [(1,3),(5,2),(5,5)]
  | 13 => [(4,2),(7,0),(8,0)]
  | 14 => [(4,3),(5,3),(8,3)]
  | 15 => [(1,5),(3,5),(5,5)]
  | 16 => stateChoices
  | 17 => stateChoices
  | 18 => [(0,1),(1,4),(6,5),(8,1)]
  | 19 => [(0,4),(0,5),(6,2),(6,5)]
  | 20 => [(0,4),(4,4),(5,4),(8,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(2,0),(2,4),(4,4)]
  | 24 => stateChoices
  | 25 => stateChoices
  | 26 => [(2,5),(4,5),(7,5),(8,3),(8,5)]
  | 27 => [(1,0),(5,5),(6,0),(7,0)]
  | 28 => [(3,0),(4,3),(7,1)]
  | 29 => [(2,5),(7,5)]
  | 30 => [(6,0)]
  | 31 => [(3,1),(7,1)]
  | 32 => [(0,1),(1,5),(6,5),(7,5)]
  | 33 => stateChoices
  | 34 => stateChoices
  | 35 => [(0,5),(7,2),(8,2)]
  | 36 => [(4,0),(4,4),(7,4),(8,0)]
  | 37 => [(0,0),(1,3),(7,3)]
  | 38 => [(7,2),(8,2)]
  | 39 => [(4,0),(5,0),(8,0)]
  | 40 => [(4,5),(7,3)]
  | 41 => stateChoices
  | 42 => stateChoices
  | 43 => [(5,1),(5,4),(7,1),(8,1),(8,4)]
  | 44 => [(0,1),(1,5),(6,4),(6,5)]
  | 45 => [(0,4),(1,2),(6,1),(6,2)]
  | 46 => [(5,1),(5,4),(8,4)]
  | 47 => [(0,0),(0,1),(6,4)]
  | 48 => stateChoices
  | 49 => stateChoices
  | 50 => [(4,5),(5,5),(7,5),(8,5)]
  | 51 => [(0,3),(1,0),(7,0)]
  | 52 => [(4,3),(7,1),(8,1),(8,3)]
  | 53 => [(1,5),(3,5),(7,5),(8,5)]
  | 54 => stateChoices
  | 55 => stateChoices
  | 56 => stateChoices
  | 57 => stateChoices
  | 58 => stateChoices
  | 59 => stateChoices
  | _ => stateChoices
def root6Node0Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => none
  | 1 => none
  | 2 => none
  | 3 => none
  | 4 => none
  | 5 => some [(4,1),(4,3),(8,1)]
  | 6 => some [(0,2),(1,5),(6,5),(7,5)]
  | 7 => some [(0,3),(0,4),(1,1),(6,1)]
  | 8 => some [(5,1),(5,4),(8,1)]
  | 9 => none
  | 10 => none
  | 11 => some [(1,3),(3,3),(5,3),(7,3),(7,4),(8,3)]
  | 12 => some [(1,3),(5,2),(5,5)]
  | 13 => some [(4,2),(7,0),(8,0)]
  | 14 => some [(4,3),(5,3),(8,3)]
  | 15 => some [(1,5),(3,5),(5,5)]
  | 16 => none
  | 17 => none
  | 18 => some [(0,1),(1,4),(6,5),(8,1)]
  | 19 => some [(0,4),(0,5),(6,2),(6,5)]
  | 20 => some [(0,4),(4,4),(5,4),(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(2,0),(2,4),(4,4)]
  | 24 => none
  | 25 => none
  | 26 => some [(2,5),(4,5),(7,5),(8,3),(8,5)]
  | 27 => some [(1,0),(5,5),(6,0),(7,0)]
  | 28 => some [(3,0),(4,3),(7,1)]
  | 29 => some [(2,5),(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(3,1),(7,1)]
  | 32 => some [(0,1),(1,5),(6,5),(7,5)]
  | 33 => none
  | 34 => none
  | 35 => some [(0,5),(7,2),(8,2)]
  | 36 => some [(4,0),(4,4),(7,4),(8,0)]
  | 37 => some [(0,0),(1,3),(7,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => none
  | 42 => none
  | 43 => some [(5,1),(5,4),(7,1),(8,1),(8,4)]
  | 44 => some [(0,1),(1,5),(6,4),(6,5)]
  | 45 => some [(0,4),(1,2),(6,1),(6,2)]
  | 46 => some [(5,1),(5,4),(8,4)]
  | 47 => some [(0,0),(0,1),(6,4)]
  | 48 => none
  | 49 => none
  | 50 => some [(4,5),(5,5),(7,5),(8,5)]
  | 51 => some [(0,3),(1,0),(7,0)]
  | 52 => some [(4,3),(7,1),(8,1),(8,3)]
  | 53 => some [(1,5),(3,5),(7,5),(8,5)]
  | 54 => none
  | 55 => none
  | 56 => none
  | 57 => none
  | 58 => none
  | 59 => none
  | _ => none
theorem root6Node0Domains1_fast_eq : root6Node0Domains1 = expandDomains root6Node0Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node0Domains1 v = expandDomains root6Node0Domains1Fast v from by decide) v
theorem root6Node0Step1Chunk0_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_0⟩
      root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains0 root6Node0Domains1
    root6Node0Domains0Fast root6Node0Domains1Fast
    root6Node0Domains0_fast_eq root6Node0Domains1_fast_eq (by decide)
theorem root6Node0Step1Chunk0_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_1⟩
      root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains0 root6Node0Domains1
    root6Node0Domains0Fast root6Node0Domains1Fast
    root6Node0Domains0_fast_eq root6Node0Domains1_fast_eq (by decide)
theorem root6Node0Step1Chunk0_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_2⟩
      root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains0 root6Node0Domains1
    root6Node0Domains0Fast root6Node0Domains1Fast
    root6Node0Domains0_fast_eq root6Node0Domains1_fast_eq (by decide)
theorem root6Node0Step1Chunk0_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_3⟩
      root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains0 root6Node0Domains1
    root6Node0Domains0Fast root6Node0Domains1Fast
    root6Node0Domains0_fast_eq root6Node0Domains1_fast_eq (by decide)
theorem root6Node0Step1Chunk0_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_4⟩
      root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains0 root6Node0Domains1
    root6Node0Domains0Fast root6Node0Domains1Fast
    root6Node0Domains0_fast_eq root6Node0Domains1_fast_eq (by decide)
theorem root6Node0Step1Chunk0_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_5⟩
      root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains0 root6Node0Domains1
    root6Node0Domains0Fast root6Node0Domains1Fast
    root6Node0Domains0_fast_eq root6Node0Domains1_fast_eq (by decide)
theorem root6Node0Step1Chunk1_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_0⟩
      root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains0 root6Node0Domains1
    root6Node0Domains0Fast root6Node0Domains1Fast
    root6Node0Domains0_fast_eq root6Node0Domains1_fast_eq (by decide)
theorem root6Node0Step1Chunk1_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_1⟩
      root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains0 root6Node0Domains1
    root6Node0Domains0Fast root6Node0Domains1Fast
    root6Node0Domains0_fast_eq root6Node0Domains1_fast_eq (by decide)
theorem root6Node0Step1Chunk1_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_2⟩
      root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains0 root6Node0Domains1
    root6Node0Domains0Fast root6Node0Domains1Fast
    root6Node0Domains0_fast_eq root6Node0Domains1_fast_eq (by decide)
theorem root6Node0Step1Chunk1_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_3⟩
      root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains0 root6Node0Domains1
    root6Node0Domains0Fast root6Node0Domains1Fast
    root6Node0Domains0_fast_eq root6Node0Domains1_fast_eq (by decide)
theorem root6Node0Step1Chunk1_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_4⟩
      root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains0 root6Node0Domains1
    root6Node0Domains0Fast root6Node0Domains1Fast
    root6Node0Domains0_fast_eq root6Node0Domains1_fast_eq (by decide)
theorem root6Node0Step1Chunk1_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_5⟩
      root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains0 root6Node0Domains1
    root6Node0Domains0Fast root6Node0Domains1Fast
    root6Node0Domains0_fast_eq root6Node0Domains1_fast_eq (by decide)
theorem root6Node0Step1Chunk2_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_0⟩
      root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains0 root6Node0Domains1
    root6Node0Domains0Fast root6Node0Domains1Fast
    root6Node0Domains0_fast_eq root6Node0Domains1_fast_eq (by decide)
theorem root6Node0Step1Chunk2_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_1⟩
      root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains0 root6Node0Domains1
    root6Node0Domains0Fast root6Node0Domains1Fast
    root6Node0Domains0_fast_eq root6Node0Domains1_fast_eq (by decide)
theorem root6Node0Step1Chunk2_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_2⟩
      root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains0 root6Node0Domains1
    root6Node0Domains0Fast root6Node0Domains1Fast
    root6Node0Domains0_fast_eq root6Node0Domains1_fast_eq (by decide)
theorem root6Node0Step1Chunk2_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_3⟩
      root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains0 root6Node0Domains1
    root6Node0Domains0Fast root6Node0Domains1Fast
    root6Node0Domains0_fast_eq root6Node0Domains1_fast_eq (by decide)
theorem root6Node0Step1Chunk2_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_4⟩
      root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains0 root6Node0Domains1
    root6Node0Domains0Fast root6Node0Domains1Fast
    root6Node0Domains0_fast_eq root6Node0Domains1_fast_eq (by decide)
theorem root6Node0Step1Chunk2_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_5⟩
      root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains0 root6Node0Domains1
    root6Node0Domains0Fast root6Node0Domains1Fast
    root6Node0Domains0_fast_eq root6Node0Domains1_fast_eq (by decide)
theorem root6Node0Step1Chunk3_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_0⟩
      root6Node0Domains0 root6Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains0 root6Node0Domains1
    root6Node0Domains0Fast root6Node0Domains1Fast
    root6Node0Domains0_fast_eq root6Node0Domains1_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFour
