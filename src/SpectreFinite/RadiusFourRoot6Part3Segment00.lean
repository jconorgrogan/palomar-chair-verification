module

public import SpectreFinite.RadiusFourRoot6Part2
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable2
public import SpectreFinite.RadiusFourTable29
public import SpectreFinite.RadiusFourTable39
public import SpectreFinite.RadiusFourTable40

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node8Domains0 : Domains 61 State := restrict root6Node7Domains1 58 (1,3)
def root6Node8Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(4,3)]
  | 6 => some [(7,5)]
  | 7 => some [(0,3)]
  | 8 => some [(8,1)]
  | 9 => some [(1,5)]
  | 10 => some [(6,1)]
  | 11 => some [(7,4)]
  | 12 => some [(1,3)]
  | 13 => some [(4,2)]
  | 14 => some [(5,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(8,3)]
  | 18 => some [(8,1)]
  | 19 => some [(6,5)]
  | 20 => some [(0,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(8,3)]
  | 27 => some [(5,5)]
  | 28 => some [(3,0)]
  | 29 => some [(2,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(7,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(4,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3)]
  | 59 => some [(7,2),(8,2)]
  | _ => some [(4,0),(8,0)]
theorem root6Node8Domains0_fast_eq : root6Node8Domains0 = expandDomains root6Node8Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node8Domains0 v = expandDomains root6Node8Domains0Fast v from by decide) v
def root6Node8Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(8,4)]
  | 4 => [(0,0)]
  | 5 => [(4,3)]
  | 6 => [(7,5)]
  | 7 => [(0,3)]
  | 8 => [(8,1)]
  | 9 => [(1,5)]
  | 10 => [(6,1)]
  | 11 => [(7,4)]
  | 12 => [(1,3)]
  | 13 => [(4,2)]
  | 14 => [(5,3)]
  | 15 => [(5,5)]
  | 16 => [(7,0)]
  | 17 => [(8,3)]
  | 18 => [(8,1)]
  | 19 => [(6,5)]
  | 20 => [(0,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(8,3)]
  | 27 => [(5,5)]
  | 28 => [(3,0)]
  | 29 => [(2,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(6,0)]
  | 34 => [(7,1)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(8,2)]
  | 42 => [(8,0)]
  | 43 => [(7,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(4,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(8,5)]
  | 54 => [(1,0)]
  | 55 => [(7,1)]
  | 56 => [(7,2)]
  | 57 => [(7,4)]
  | 58 => [(1,3)]
  | 59 => [(8,2)]
  | _ => [(8,0)]
def root6Node8Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(4,3)]
  | 6 => some [(7,5)]
  | 7 => some [(0,3)]
  | 8 => some [(8,1)]
  | 9 => some [(1,5)]
  | 10 => some [(6,1)]
  | 11 => some [(7,4)]
  | 12 => some [(1,3)]
  | 13 => some [(4,2)]
  | 14 => some [(5,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(8,3)]
  | 18 => some [(8,1)]
  | 19 => some [(6,5)]
  | 20 => some [(0,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(8,3)]
  | 27 => some [(5,5)]
  | 28 => some [(3,0)]
  | 29 => some [(2,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(7,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(4,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3)]
  | 59 => some [(8,2)]
  | _ => some [(8,0)]
theorem root6Node8Domains1_fast_eq : root6Node8Domains1 = expandDomains root6Node8Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node8Domains1 v = expandDomains root6Node8Domains1Fast v from by decide) v
theorem root6Node8Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root6Node8Domains0 root6Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node8Domains0 root6Node8Domains1
    root6Node8Domains0Fast root6Node8Domains1Fast
    root6Node8Domains0_fast_eq root6Node8Domains1_fast_eq (by decide)
theorem root6Node8Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root6Node8Domains0 root6Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node8Domains0 root6Node8Domains1
    root6Node8Domains0Fast root6Node8Domains1Fast
    root6Node8Domains0_fast_eq root6Node8Domains1_fast_eq (by decide)
theorem root6Node8Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root6Node8Domains0 root6Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node8Domains0 root6Node8Domains1
    root6Node8Domains0Fast root6Node8Domains1Fast
    root6Node8Domains0_fast_eq root6Node8Domains1_fast_eq (by decide)
theorem root6Node8Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root6Node8Domains0 root6Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node8Domains0 root6Node8Domains1
    root6Node8Domains0Fast root6Node8Domains1Fast
    root6Node8Domains0_fast_eq root6Node8Domains1_fast_eq (by decide)
theorem root6Node8Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root6Node8Domains0 root6Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node8Domains0 root6Node8Domains1
    root6Node8Domains0Fast root6Node8Domains1Fast
    root6Node8Domains0_fast_eq root6Node8Domains1_fast_eq (by decide)
theorem root6Node8Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root6Node8Domains0 root6Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node8Domains0 root6Node8Domains1
    root6Node8Domains0Fast root6Node8Domains1Fast
    root6Node8Domains0_fast_eq root6Node8Domains1_fast_eq (by decide)
theorem root6Node8Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root6Node8Domains0 root6Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node8Domains0 root6Node8Domains1
    root6Node8Domains0Fast root6Node8Domains1Fast
    root6Node8Domains0_fast_eq root6Node8Domains1_fast_eq (by decide)
theorem root6Node8Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root6Node8Domains0 root6Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node8Domains0 root6Node8Domains1
    root6Node8Domains0Fast root6Node8Domains1Fast
    root6Node8Domains0_fast_eq root6Node8Domains1_fast_eq (by decide)
theorem root6Node8Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root6Node8Domains0 root6Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node8Domains0 root6Node8Domains1
    root6Node8Domains0Fast root6Node8Domains1Fast
    root6Node8Domains0_fast_eq root6Node8Domains1_fast_eq (by decide)
theorem root6Node8Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root6Node8Domains0 root6Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node8Domains0 root6Node8Domains1
    root6Node8Domains0Fast root6Node8Domains1Fast
    root6Node8Domains0_fast_eq root6Node8Domains1_fast_eq (by decide)
theorem root6Node8Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root6Node8Domains0 root6Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node8Domains0 root6Node8Domains1
    root6Node8Domains0Fast root6Node8Domains1Fast
    root6Node8Domains0_fast_eq root6Node8Domains1_fast_eq (by decide)
theorem root6Node8Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root6Node8Domains0 root6Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node8Domains0 root6Node8Domains1
    root6Node8Domains0Fast root6Node8Domains1Fast
    root6Node8Domains0_fast_eq root6Node8Domains1_fast_eq (by decide)
theorem root6Node8Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root6Node8Domains0 root6Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node8Domains0 root6Node8Domains1
    root6Node8Domains0Fast root6Node8Domains1Fast
    root6Node8Domains0_fast_eq root6Node8Domains1_fast_eq (by decide)
theorem root6Node8Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root6Node8Domains0 root6Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node8Domains0 root6Node8Domains1
    root6Node8Domains0Fast root6Node8Domains1Fast
    root6Node8Domains0_fast_eq root6Node8Domains1_fast_eq (by decide)
theorem root6Node8Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root6Node8Domains0 root6Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node8Domains0 root6Node8Domains1
    root6Node8Domains0Fast root6Node8Domains1Fast
    root6Node8Domains0_fast_eq root6Node8Domains1_fast_eq (by decide)
theorem root6Node8Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root6Node8Domains0 root6Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node8Domains0 root6Node8Domains1
    root6Node8Domains0Fast root6Node8Domains1Fast
    root6Node8Domains0_fast_eq root6Node8Domains1_fast_eq (by decide)
theorem root6Node8Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root6Node8Domains0 root6Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node8Domains0 root6Node8Domains1
    root6Node8Domains0Fast root6Node8Domains1Fast
    root6Node8Domains0_fast_eq root6Node8Domains1_fast_eq (by decide)
theorem root6Node8Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root6Node8Domains0 root6Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node8Domains0 root6Node8Domains1
    root6Node8Domains0Fast root6Node8Domains1Fast
    root6Node8Domains0_fast_eq root6Node8Domains1_fast_eq (by decide)
theorem root6Node8Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root6Node8Domains0 root6Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node8Domains0 root6Node8Domains1
    root6Node8Domains0Fast root6Node8Domains1Fast
    root6Node8Domains0_fast_eq root6Node8Domains1_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFour
