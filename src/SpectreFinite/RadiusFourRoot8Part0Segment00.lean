module

public import SpectreFinite.RadiusFourRoot8Data
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
def root8Node0Domains0 : Domains 61 State := domains (8,0)
def root8Node0Domains0Fast (v : Fin 61) : Option (List State) :=
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
  | 30 => some [(8,0)]
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
theorem root8Node0Domains0_fast_eq : root8Node0Domains0 = expandDomains root8Node0Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node0Domains0 v = expandDomains root8Node0Domains0Fast v from by decide) v
def root8Node0Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => stateChoices
  | 2 => stateChoices
  | 3 => stateChoices
  | 4 => stateChoices
  | 5 => stateChoices
  | 6 => [(4,0),(4,2),(7,0),(8,0)]
  | 7 => [(5,3),(7,3),(8,3)]
  | 8 => [(5,2),(5,5),(8,2),(8,5)]
  | 9 => [(1,0),(7,0),(8,0)]
  | 10 => stateChoices
  | 11 => stateChoices
  | 12 => [(1,2),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 13 => [(0,1),(1,4),(7,4)]
  | 14 => [(0,5),(6,2),(6,3)]
  | 15 => [(4,4),(7,2),(8,4)]
  | 16 => [(1,4),(4,0),(6,4),(7,4)]
  | 17 => stateChoices
  | 18 => stateChoices
  | 19 => [(0,3),(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 20 => [(4,1),(7,5),(8,5)]
  | 21 => [(0,2),(1,0),(6,0)]
  | 22 => [(1,1),(7,1)]
  | 23 => [(4,1),(5,1),(7,5),(8,1)]
  | 24 => [(0,1),(0,2),(0,3),(6,0),(6,5)]
  | 25 => stateChoices
  | 26 => stateChoices
  | 27 => [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 28 => [(1,3),(3,3),(7,3)]
  | 29 => [(5,2),(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3),(8,3)]
  | 32 => [(4,2),(5,2),(5,5),(8,2)]
  | 33 => [(1,0),(3,0),(5,0),(5,3),(7,0)]
  | 34 => stateChoices
  | 35 => stateChoices
  | 36 => [(0,1),(6,5)]
  | 37 => [(0,4),(6,2)]
  | 38 => [(5,4),(8,4)]
  | 39 => [(1,4),(6,4)]
  | 40 => [(0,5),(1,2)]
  | 41 => [(4,4),(7,4),(8,4)]
  | 42 => stateChoices
  | 43 => stateChoices
  | 44 => [(1,0),(7,0)]
  | 45 => [(4,3),(7,1)]
  | 46 => [(3,5),(7,5)]
  | 47 => [(0,3),(6,0)]
  | 48 => [(4,1),(7,1),(8,1)]
  | 49 => stateChoices
  | 50 => stateChoices
  | 51 => [(1,4),(4,0),(7,4),(8,0)]
  | 52 => [(0,5),(1,3),(6,3),(7,3)]
  | 53 => [(2,2),(2,4),(4,2),(8,2)]
  | 54 => [(1,3),(3,3),(5,0),(5,3),(8,0)]
  | 55 => stateChoices
  | 56 => stateChoices
  | 57 => stateChoices
  | 58 => stateChoices
  | 59 => stateChoices
  | _ => stateChoices
def root8Node0Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => none
  | 1 => none
  | 2 => none
  | 3 => none
  | 4 => none
  | 5 => none
  | 6 => some [(4,0),(4,2),(7,0),(8,0)]
  | 7 => some [(5,3),(7,3),(8,3)]
  | 8 => some [(5,2),(5,5),(8,2),(8,5)]
  | 9 => some [(1,0),(7,0),(8,0)]
  | 10 => none
  | 11 => none
  | 12 => some [(1,2),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 13 => some [(0,1),(1,4),(7,4)]
  | 14 => some [(0,5),(6,2),(6,3)]
  | 15 => some [(4,4),(7,2),(8,4)]
  | 16 => some [(1,4),(4,0),(6,4),(7,4)]
  | 17 => none
  | 18 => none
  | 19 => some [(0,3),(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 20 => some [(4,1),(7,5),(8,5)]
  | 21 => some [(0,2),(1,0),(6,0)]
  | 22 => some [(1,1),(7,1)]
  | 23 => some [(4,1),(5,1),(7,5),(8,1)]
  | 24 => some [(0,1),(0,2),(0,3),(6,0),(6,5)]
  | 25 => none
  | 26 => none
  | 27 => some [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 28 => some [(1,3),(3,3),(7,3)]
  | 29 => some [(5,2),(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(4,2),(5,2),(5,5),(8,2)]
  | 33 => some [(1,0),(3,0),(5,0),(5,3),(7,0)]
  | 34 => none
  | 35 => none
  | 36 => some [(0,1),(6,5)]
  | 37 => some [(0,4),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(0,5),(1,2)]
  | 41 => some [(4,4),(7,4),(8,4)]
  | 42 => none
  | 43 => none
  | 44 => some [(1,0),(7,0)]
  | 45 => some [(4,3),(7,1)]
  | 46 => some [(3,5),(7,5)]
  | 47 => some [(0,3),(6,0)]
  | 48 => some [(4,1),(7,1),(8,1)]
  | 49 => none
  | 50 => none
  | 51 => some [(1,4),(4,0),(7,4),(8,0)]
  | 52 => some [(0,5),(1,3),(6,3),(7,3)]
  | 53 => some [(2,2),(2,4),(4,2),(8,2)]
  | 54 => some [(1,3),(3,3),(5,0),(5,3),(8,0)]
  | 55 => none
  | 56 => none
  | 57 => none
  | 58 => none
  | 59 => none
  | _ => none
theorem root8Node0Domains1_fast_eq : root8Node0Domains1 = expandDomains root8Node0Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node0Domains1 v = expandDomains root8Node0Domains1Fast v from by decide) v
theorem root8Node0Step1Chunk0_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_0⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk0_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_1⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk0_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_2⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk0_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_3⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk0_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_4⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk0_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_5⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk1_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_0⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk1_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_1⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk1_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_2⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk1_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_3⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk1_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_4⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk1_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_5⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk2_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_0⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk2_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_1⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk2_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_2⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk2_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_3⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk2_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_4⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk2_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_5⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
theorem root8Node0Step1Chunk3_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_0⟩
      root8Node0Domains0 root8Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains0 root8Node0Domains1
    root8Node0Domains0Fast root8Node0Domains1Fast
    root8Node0Domains0_fast_eq root8Node0Domains1_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFour
