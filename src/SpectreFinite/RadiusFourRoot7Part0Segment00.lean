module

public import SpectreFinite.RadiusFourRoot7Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable0
public import SpectreFinite.RadiusFourTable23
public import SpectreFinite.RadiusFourTable30
public import SpectreFinite.RadiusFourTable37
public import SpectreFinite.RadiusFourTable39

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node0Domains0 : Domains 61 State := domains (7,0)
def root7Node0Domains0Fast (v : Fin 61) : Option (List State) :=
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
  | 30 => some [(7,0)]
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
theorem root7Node0Domains0_fast_eq : root7Node0Domains0 = expandDomains root7Node0Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node0Domains0 v = expandDomains root7Node0Domains0Fast v from by decide) v
def root7Node0Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => stateChoices
  | 2 => stateChoices
  | 3 => stateChoices
  | 4 => stateChoices
  | 5 => stateChoices
  | 6 => [(3,5),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 7 => [(0,3),(1,0),(3,0),(4,3),(5,0),(5,3),(8,3)]
  | 8 => [(2,1),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 9 => [(0,2),(0,3),(1,0),(6,0),(7,0)]
  | 10 => stateChoices
  | 11 => stateChoices
  | 12 => [(0,5),(1,2),(6,2),(7,2)]
  | 13 => [(2,4),(4,4),(7,4),(8,4)]
  | 14 => [(0,0),(1,3)]
  | 15 => [(3,2),(4,2),(5,2),(7,2),(8,2)]
  | 16 => [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 17 => stateChoices
  | 18 => stateChoices
  | 19 => [(0,3),(1,0),(1,1),(6,0),(6,1)]
  | 20 => [(7,1),(8,1)]
  | 21 => [(1,5),(6,5)]
  | 22 => [(0,4),(6,1)]
  | 23 => [(3,4),(5,1),(5,4),(8,1)]
  | 24 => [(0,0),(0,1),(1,4),(6,3),(6,4),(6,5)]
  | 25 => stateChoices
  | 26 => stateChoices
  | 27 => [(4,2),(7,0),(8,0),(8,2)]
  | 28 => [(5,0),(5,3),(8,3)]
  | 29 => [(4,5),(5,5),(8,5)]
  | 30 => [(7,0)]
  | 31 => [(2,3),(4,3),(8,3)]
  | 32 => [(0,2),(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 33 => [(0,3),(1,0),(1,1),(3,0),(6,0),(6,1),(7,0)]
  | 34 => stateChoices
  | 35 => stateChoices
  | 36 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 37 => [(0,0),(0,5),(6,3)]
  | 38 => [(4,4),(7,2)]
  | 39 => [(1,4),(6,4),(7,4)]
  | 40 => [(0,5),(1,2),(1,3),(6,3)]
  | 41 => [(2,0),(2,2),(2,4),(4,0),(4,2),(4,4),(7,2),(8,2)]
  | 42 => stateChoices
  | 43 => stateChoices
  | 44 => [(0,2),(1,5),(6,0)]
  | 45 => [(1,1),(6,1),(7,1)]
  | 46 => [(4,1),(7,5),(8,1)]
  | 47 => [(0,2),(0,3),(6,0),(6,5)]
  | 48 => [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 49 => stateChoices
  | 50 => stateChoices
  | 51 => [(2,0),(4,0),(7,0),(8,0)]
  | 52 => [(7,3),(8,3)]
  | 53 => [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | 54 => [(3,0),(5,0),(5,3),(7,0),(8,0)]
  | 55 => stateChoices
  | 56 => stateChoices
  | 57 => stateChoices
  | 58 => stateChoices
  | 59 => stateChoices
  | _ => stateChoices
def root7Node0Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => none
  | 1 => none
  | 2 => none
  | 3 => none
  | 4 => none
  | 5 => none
  | 6 => some [(3,5),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 7 => some [(0,3),(1,0),(3,0),(4,3),(5,0),(5,3),(8,3)]
  | 8 => some [(2,1),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 9 => some [(0,2),(0,3),(1,0),(6,0),(7,0)]
  | 10 => none
  | 11 => none
  | 12 => some [(0,5),(1,2),(6,2),(7,2)]
  | 13 => some [(2,4),(4,4),(7,4),(8,4)]
  | 14 => some [(0,0),(1,3)]
  | 15 => some [(3,2),(4,2),(5,2),(7,2),(8,2)]
  | 16 => some [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 17 => none
  | 18 => none
  | 19 => some [(0,3),(1,0),(1,1),(6,0),(6,1)]
  | 20 => some [(7,1),(8,1)]
  | 21 => some [(1,5),(6,5)]
  | 22 => some [(0,4),(6,1)]
  | 23 => some [(3,4),(5,1),(5,4),(8,1)]
  | 24 => some [(0,0),(0,1),(1,4),(6,3),(6,4),(6,5)]
  | 25 => none
  | 26 => none
  | 27 => some [(4,2),(7,0),(8,0),(8,2)]
  | 28 => some [(5,0),(5,3),(8,3)]
  | 29 => some [(4,5),(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(2,3),(4,3),(8,3)]
  | 32 => some [(0,2),(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 33 => some [(0,3),(1,0),(1,1),(3,0),(6,0),(6,1),(7,0)]
  | 34 => none
  | 35 => none
  | 36 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 37 => some [(0,0),(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(6,4),(7,4)]
  | 40 => some [(0,5),(1,2),(1,3),(6,3)]
  | 41 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(4,4),(7,2),(8,2)]
  | 42 => none
  | 43 => none
  | 44 => some [(0,2),(1,5),(6,0)]
  | 45 => some [(1,1),(6,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(0,3),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 49 => none
  | 50 => none
  | 51 => some [(2,0),(4,0),(7,0),(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | 54 => some [(3,0),(5,0),(5,3),(7,0),(8,0)]
  | 55 => none
  | 56 => none
  | 57 => none
  | 58 => none
  | 59 => none
  | _ => none
theorem root7Node0Domains1_fast_eq : root7Node0Domains1 = expandDomains root7Node0Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node0Domains1 v = expandDomains root7Node0Domains1Fast v from by decide) v
theorem root7Node0Step1Chunk0_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_0⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Chunk0_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_1⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Chunk0_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_2⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Chunk0_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_3⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Chunk0_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_4⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Chunk0_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_5⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Chunk1_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_0⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Chunk1_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_1⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Chunk1_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_2⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Chunk1_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_3⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Chunk1_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_4⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Chunk1_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_5⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Chunk2_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_0⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Chunk2_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_1⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Chunk2_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_2⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Chunk2_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_3⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Chunk2_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_4⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Chunk2_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_5⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Chunk3_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_0⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFour
