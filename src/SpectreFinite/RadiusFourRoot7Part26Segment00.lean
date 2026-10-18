module

public import SpectreFinite.RadiusFourRoot7Part25
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable19
public import SpectreFinite.RadiusFourTable23
public import SpectreFinite.RadiusFourTable29
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node80Domains0 : Domains 61 State := restrict root7Node0Domains5 14 (1,3)
def root7Node80Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5),(4,1),(5,1),(5,4),(6,5),(7,5),(8,1)]
  | 1 => some [(0,1),(0,2),(0,3),(0,4),(6,0),(6,1),(6,4),(6,5)]
  | 2 => some [(0,4),(1,1),(1,2),(3,1),(5,1),(5,4),(6,2),(7,1)]
  | 3 => some [(0,1),(1,4),(1,5),(6,4),(6,5),(7,4)]
  | 4 => some [(0,4),(0,5),(1,2),(6,1),(6,2),(6,3)]
  | 5 => some [(4,3),(4,5),(7,3),(8,3),(8,5)]
  | 6 => some [(3,5),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 7 => some [(0,3),(1,0),(3,0),(4,3),(5,0),(5,3),(8,3)]
  | 8 => some [(2,1),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 9 => some [(0,2),(0,3),(1,0),(6,0),(7,0)]
  | 10 => some [(1,1),(4,3),(7,1),(8,1),(8,3)]
  | 11 => some [(0,0),(0,1),(1,4),(6,3),(6,4)]
  | 12 => some [(0,5),(1,2),(6,2),(7,2)]
  | 13 => some [(2,4),(4,4),(7,4),(8,4)]
  | 14 => some [(1,3)]
  | 15 => some [(3,2),(4,2),(5,2),(7,2),(8,2)]
  | 16 => some [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 17 => some [(1,3),(4,5),(7,3),(8,3),(8,5)]
  | 18 => some [(0,2),(1,5),(7,5),(8,5)]
  | 19 => some [(0,3),(1,0),(1,1),(6,0),(6,1)]
  | 20 => some [(7,1),(8,1)]
  | 21 => some [(1,5),(6,5)]
  | 22 => some [(0,4),(6,1)]
  | 23 => some [(3,4),(5,1),(5,4),(8,1)]
  | 24 => some [(0,0),(0,1),(1,4),(6,3),(6,4),(6,5)]
  | 25 => some [(0,4),(0,5),(1,2),(6,2),(7,2)]
  | 26 => some [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 27 => some [(4,2),(7,0),(8,0),(8,2)]
  | 28 => some [(5,0),(5,3),(8,3)]
  | 29 => some [(4,5),(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(2,3),(4,3),(8,3)]
  | 32 => some [(0,2),(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 33 => some [(0,3),(1,0),(1,1),(3,0),(6,0),(6,1),(7,0)]
  | 34 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(8,1)]
  | 35 => some [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 36 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 37 => some [(0,0),(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(6,4),(7,4)]
  | 40 => some [(0,5),(1,2),(1,3),(6,3)]
  | 41 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(4,4),(7,2),(8,2)]
  | 42 => some [(0,0),(1,3),(1,4),(3,3),(4,0),(5,0),(5,3),(6,4),(7,3),(7,4),(8,0)]
  | 43 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(7,5),(8,1)]
  | 44 => some [(0,2),(1,5),(6,0)]
  | 45 => some [(1,1),(6,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(0,3),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 49 => some [(0,1),(1,4),(1,5),(3,4),(4,1),(5,1),(5,4),(6,5),(7,5),(8,1)]
  | 50 => some [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 51 => some [(2,0),(4,0),(7,0),(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | 54 => some [(3,0),(5,0),(5,3),(7,0),(8,0)]
  | 55 => some [(2,3),(2,5),(4,3),(4,5),(7,3),(8,3),(8,5)]
  | 56 => some [(3,1),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 57 => some [(0,1),(1,4),(6,4),(7,4)]
  | 58 => some [(0,5),(1,2),(6,2),(6,3)]
  | 59 => some [(4,4),(7,2),(7,4),(8,4)]
  | _ => some [(0,0),(1,3),(1,4),(6,3),(6,4),(7,4)]
theorem root7Node80Domains0_fast_eq : root7Node80Domains0 = expandDomains root7Node80Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node80Domains0 v = expandDomains root7Node80Domains0Fast v from by decide) v
def root7Node80Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5),(4,1),(5,1),(5,4),(6,5),(7,5),(8,1)]
  | 1 => [(0,1),(0,2),(0,3),(0,4),(6,0),(6,1),(6,4),(6,5)]
  | 2 => [(1,2),(5,1),(5,4)]
  | 3 => [(0,1),(1,4),(6,4),(7,4)]
  | 4 => [(0,5),(1,2),(6,2),(6,3)]
  | 5 => [(4,3),(4,5),(7,3),(8,3),(8,5)]
  | 6 => [(3,5),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 7 => [(0,3),(4,3),(5,3),(8,3)]
  | 8 => [(4,1),(7,5),(8,5)]
  | 9 => [(0,2),(0,3),(1,0),(6,0)]
  | 10 => [(1,1),(7,1),(8,1)]
  | 11 => [(0,0),(0,1),(1,4),(6,3),(6,4)]
  | 12 => [(0,5),(1,2),(6,2),(7,2)]
  | 13 => [(2,4),(7,4)]
  | 14 => [(1,3)]
  | 15 => [(4,2),(5,2),(8,2)]
  | 16 => [(5,0),(5,3),(8,0)]
  | 17 => [(4,5),(7,3),(8,3),(8,5)]
  | 18 => [(0,2),(1,5),(7,5),(8,5)]
  | 19 => [(0,3),(1,0),(1,1),(6,0),(6,1)]
  | 20 => [(7,1),(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(3,4),(5,4)]
  | 24 => [(0,0),(1,4),(6,3),(6,4)]
  | 25 => [(0,5),(1,2),(7,2)]
  | 26 => [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 27 => [(4,2),(7,0),(8,0),(8,2)]
  | 28 => [(5,0),(5,3),(8,3)]
  | 29 => [(4,5),(5,5),(8,5)]
  | 30 => [(7,0)]
  | 31 => [(2,3),(4,3)]
  | 32 => [(0,2),(1,5),(3,5),(7,5)]
  | 33 => [(0,3),(1,1),(6,0),(6,1)]
  | 34 => [(4,1),(7,1),(8,1)]
  | 35 => [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 36 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 37 => [(0,0),(0,5),(6,3)]
  | 38 => [(4,4),(7,2)]
  | 39 => [(1,4),(6,4),(7,4)]
  | 40 => [(0,5),(1,2),(1,3),(6,3)]
  | 41 => [(2,0),(2,2),(2,4),(4,0),(4,2),(8,2)]
  | 42 => [(1,3),(3,3),(5,0),(5,3),(7,3),(8,0)]
  | 43 => [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(7,5),(8,1)]
  | 44 => [(0,2),(1,5),(6,0)]
  | 45 => [(1,1),(6,1),(7,1)]
  | 46 => [(4,1),(7,5),(8,1)]
  | 47 => [(0,2),(0,3),(6,0),(6,5)]
  | 48 => [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 49 => [(0,1),(1,4),(3,4),(5,4),(6,5)]
  | 50 => [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 51 => [(2,0),(4,0),(7,0),(8,0)]
  | 52 => [(7,3),(8,3)]
  | 53 => [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | 54 => [(3,0),(5,0),(5,3),(7,0),(8,0)]
  | 55 => [(2,3),(2,5),(4,3),(4,5),(7,3),(8,3),(8,5)]
  | 56 => [(3,1),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 57 => [(0,1),(1,4),(6,4),(7,4)]
  | 58 => [(0,5),(1,2),(6,2),(6,3)]
  | 59 => [(4,4),(7,2),(7,4),(8,4)]
  | _ => [(0,0),(1,3),(1,4),(6,3),(6,4),(7,4)]
def root7Node80Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5),(4,1),(5,1),(5,4),(6,5),(7,5),(8,1)]
  | 1 => some [(0,1),(0,2),(0,3),(0,4),(6,0),(6,1),(6,4),(6,5)]
  | 2 => some [(1,2),(5,1),(5,4)]
  | 3 => some [(0,1),(1,4),(6,4),(7,4)]
  | 4 => some [(0,5),(1,2),(6,2),(6,3)]
  | 5 => some [(4,3),(4,5),(7,3),(8,3),(8,5)]
  | 6 => some [(3,5),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 7 => some [(0,3),(4,3),(5,3),(8,3)]
  | 8 => some [(4,1),(7,5),(8,5)]
  | 9 => some [(0,2),(0,3),(1,0),(6,0)]
  | 10 => some [(1,1),(7,1),(8,1)]
  | 11 => some [(0,0),(0,1),(1,4),(6,3),(6,4)]
  | 12 => some [(0,5),(1,2),(6,2),(7,2)]
  | 13 => some [(2,4),(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2),(5,2),(8,2)]
  | 16 => some [(5,0),(5,3),(8,0)]
  | 17 => some [(4,5),(7,3),(8,3),(8,5)]
  | 18 => some [(0,2),(1,5),(7,5),(8,5)]
  | 19 => some [(0,3),(1,0),(1,1),(6,0),(6,1)]
  | 20 => some [(7,1),(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(3,4),(5,4)]
  | 24 => some [(0,0),(1,4),(6,3),(6,4)]
  | 25 => some [(0,5),(1,2),(7,2)]
  | 26 => some [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 27 => some [(4,2),(7,0),(8,0),(8,2)]
  | 28 => some [(5,0),(5,3),(8,3)]
  | 29 => some [(4,5),(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(2,3),(4,3)]
  | 32 => some [(0,2),(1,5),(3,5),(7,5)]
  | 33 => some [(0,3),(1,1),(6,0),(6,1)]
  | 34 => some [(4,1),(7,1),(8,1)]
  | 35 => some [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 36 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 37 => some [(0,0),(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(6,4),(7,4)]
  | 40 => some [(0,5),(1,2),(1,3),(6,3)]
  | 41 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(8,2)]
  | 42 => some [(1,3),(3,3),(5,0),(5,3),(7,3),(8,0)]
  | 43 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(7,5),(8,1)]
  | 44 => some [(0,2),(1,5),(6,0)]
  | 45 => some [(1,1),(6,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(0,3),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 49 => some [(0,1),(1,4),(3,4),(5,4),(6,5)]
  | 50 => some [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 51 => some [(2,0),(4,0),(7,0),(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | 54 => some [(3,0),(5,0),(5,3),(7,0),(8,0)]
  | 55 => some [(2,3),(2,5),(4,3),(4,5),(7,3),(8,3),(8,5)]
  | 56 => some [(3,1),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 57 => some [(0,1),(1,4),(6,4),(7,4)]
  | 58 => some [(0,5),(1,2),(6,2),(6,3)]
  | 59 => some [(4,4),(7,2),(7,4),(8,4)]
  | _ => some [(0,0),(1,3),(1,4),(6,3),(6,4),(7,4)]
theorem root7Node80Domains1_fast_eq : root7Node80Domains1 = expandDomains root7Node80Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node80Domains1 v = expandDomains root7Node80Domains1Fast v from by decide) v
theorem root7Node80Step1Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root7Node80Domains0 root7Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node80Domains0 root7Node80Domains1
    root7Node80Domains0Fast root7Node80Domains1Fast
    root7Node80Domains0_fast_eq root7Node80Domains1_fast_eq (by decide)
theorem root7Node80Step1Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root7Node80Domains0 root7Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node80Domains0 root7Node80Domains1
    root7Node80Domains0Fast root7Node80Domains1Fast
    root7Node80Domains0_fast_eq root7Node80Domains1_fast_eq (by decide)
theorem root7Node80Step1Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root7Node80Domains0 root7Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node80Domains0 root7Node80Domains1
    root7Node80Domains0Fast root7Node80Domains1Fast
    root7Node80Domains0_fast_eq root7Node80Domains1_fast_eq (by decide)
theorem root7Node80Step1Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root7Node80Domains0 root7Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node80Domains0 root7Node80Domains1
    root7Node80Domains0Fast root7Node80Domains1Fast
    root7Node80Domains0_fast_eq root7Node80Domains1_fast_eq (by decide)
theorem root7Node80Step1Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root7Node80Domains0 root7Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node80Domains0 root7Node80Domains1
    root7Node80Domains0Fast root7Node80Domains1Fast
    root7Node80Domains0_fast_eq root7Node80Domains1_fast_eq (by decide)
theorem root7Node80Step1Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root7Node80Domains0 root7Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node80Domains0 root7Node80Domains1
    root7Node80Domains0Fast root7Node80Domains1Fast
    root7Node80Domains0_fast_eq root7Node80Domains1_fast_eq (by decide)
theorem root7Node80Step1Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root7Node80Domains0 root7Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node80Domains0 root7Node80Domains1
    root7Node80Domains0Fast root7Node80Domains1Fast
    root7Node80Domains0_fast_eq root7Node80Domains1_fast_eq (by decide)
theorem root7Node80Step1Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root7Node80Domains0 root7Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node80Domains0 root7Node80Domains1
    root7Node80Domains0Fast root7Node80Domains1Fast
    root7Node80Domains0_fast_eq root7Node80Domains1_fast_eq (by decide)
theorem root7Node80Step1Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root7Node80Domains0 root7Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node80Domains0 root7Node80Domains1
    root7Node80Domains0Fast root7Node80Domains1Fast
    root7Node80Domains0_fast_eq root7Node80Domains1_fast_eq (by decide)
theorem root7Node80Step1Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root7Node80Domains0 root7Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node80Domains0 root7Node80Domains1
    root7Node80Domains0Fast root7Node80Domains1Fast
    root7Node80Domains0_fast_eq root7Node80Domains1_fast_eq (by decide)
theorem root7Node80Step1Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root7Node80Domains0 root7Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node80Domains0 root7Node80Domains1
    root7Node80Domains0Fast root7Node80Domains1Fast
    root7Node80Domains0_fast_eq root7Node80Domains1_fast_eq (by decide)
theorem root7Node80Step1Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root7Node80Domains0 root7Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node80Domains0 root7Node80Domains1
    root7Node80Domains0Fast root7Node80Domains1Fast
    root7Node80Domains0_fast_eq root7Node80Domains1_fast_eq (by decide)
theorem root7Node80Step1Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root7Node80Domains0 root7Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node80Domains0 root7Node80Domains1
    root7Node80Domains0Fast root7Node80Domains1Fast
    root7Node80Domains0_fast_eq root7Node80Domains1_fast_eq (by decide)
theorem root7Node80Step1Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root7Node80Domains0 root7Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node80Domains0 root7Node80Domains1
    root7Node80Domains0Fast root7Node80Domains1Fast
    root7Node80Domains0_fast_eq root7Node80Domains1_fast_eq (by decide)
theorem root7Node80Step1Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root7Node80Domains0 root7Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node80Domains0 root7Node80Domains1
    root7Node80Domains0Fast root7Node80Domains1Fast
    root7Node80Domains0_fast_eq root7Node80Domains1_fast_eq (by decide)
theorem root7Node80Step1Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root7Node80Domains0 root7Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node80Domains0 root7Node80Domains1
    root7Node80Domains0Fast root7Node80Domains1Fast
    root7Node80Domains0_fast_eq root7Node80Domains1_fast_eq (by decide)
theorem root7Node80Step1Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root7Node80Domains0 root7Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node80Domains0 root7Node80Domains1
    root7Node80Domains0Fast root7Node80Domains1Fast
    root7Node80Domains0_fast_eq root7Node80Domains1_fast_eq (by decide)
theorem root7Node80Step1Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root7Node80Domains0 root7Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node80Domains0 root7Node80Domains1
    root7Node80Domains0Fast root7Node80Domains1Fast
    root7Node80Domains0_fast_eq root7Node80Domains1_fast_eq (by decide)
theorem root7Node80Step1Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root7Node80Domains0 root7Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node80Domains0 root7Node80Domains1
    root7Node80Domains0Fast root7Node80Domains1Fast
    root7Node80Domains0_fast_eq root7Node80Domains1_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFour
