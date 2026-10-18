module

public import SpectreFinite.RadiusFourRoot6Part6
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable37

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node21Domains0 : Domains 61 State := restrict root6Node20Domains2 11 (5,3)
def root6Node21Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,1)]
  | 6 => some [(6,5)]
  | 7 => some [(0,4)]
  | 8 => some [(5,4)]
  | 9 => some [(6,4)]
  | 10 => some [(1,2)]
  | 11 => some [(5,3)]
  | 12 => some [(5,5)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(1,4)]
  | 19 => some [(0,5)]
  | 20 => some [(4,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(2,4)]
  | 24 => some [(1,3)]
  | 25 => some [(5,2)]
  | 26 => some [(2,5),(7,5)]
  | 27 => some [(6,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(6,5)]
  | 33 => some [(0,4)]
  | 34 => some [(5,4)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(8,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(4,3)]
  | 43 => some [(5,1),(5,4),(8,4)]
  | 44 => some [(0,1),(6,4)]
  | 45 => some [(1,2),(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(7,5),(8,5)]
  | 51 => some [(0,3),(1,0)]
  | 52 => some [(7,1),(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(8,1)]
  | 56 => some [(4,2),(8,2)]
  | 57 => some [(5,0),(5,3)]
  | 58 => some [(4,5),(5,5),(8,5)]
  | 59 => some [(7,0)]
  | _ => some [(8,3)]
theorem root6Node21Domains0_fast_eq : root6Node21Domains0 = expandDomains root6Node21Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node21Domains0 v = expandDomains root6Node21Domains0Fast v from by decide) v
def root6Node21Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3)]
  | 5 => [(8,1)]
  | 6 => [(6,5)]
  | 7 => [(0,4)]
  | 8 => [(5,4)]
  | 9 => [(6,4)]
  | 10 => [(1,2)]
  | 11 => [(5,3)]
  | 12 => [(5,5)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(3,5)]
  | 16 => [(0,3)]
  | 17 => [(4,1)]
  | 18 => [(1,4)]
  | 19 => [(0,5)]
  | 20 => [(4,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(2,4)]
  | 24 => [(1,3)]
  | 25 => [(5,2)]
  | 26 => [(2,5)]
  | 27 => [(6,0)]
  | 28 => [(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(6,5)]
  | 33 => [(0,4)]
  | 34 => [(5,4)]
  | 35 => [(7,2)]
  | 36 => [(4,0)]
  | 37 => [(7,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(7,0)]
  | 42 => [(4,3)]
  | 43 => [(5,1)]
  | 44 => [(0,1)]
  | 45 => [(6,2)]
  | 46 => [(8,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(7,4)]
  | 50 => [(8,5)]
  | 51 => [(1,0)]
  | 52 => [(7,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(8,1)]
  | 56 => [(8,2)]
  | 57 => [(5,0)]
  | 58 => [(4,5)]
  | 59 => [(7,0)]
  | _ => [(8,3)]
def root6Node21Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,1)]
  | 6 => some [(6,5)]
  | 7 => some [(0,4)]
  | 8 => some [(5,4)]
  | 9 => some [(6,4)]
  | 10 => some [(1,2)]
  | 11 => some [(5,3)]
  | 12 => some [(5,5)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(1,4)]
  | 19 => some [(0,5)]
  | 20 => some [(4,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(2,4)]
  | 24 => some [(1,3)]
  | 25 => some [(5,2)]
  | 26 => some [(2,5)]
  | 27 => some [(6,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(6,5)]
  | 33 => some [(0,4)]
  | 34 => some [(5,4)]
  | 35 => some [(7,2)]
  | 36 => some [(4,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(4,3)]
  | 43 => some [(5,1)]
  | 44 => some [(0,1)]
  | 45 => some [(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(8,5)]
  | 51 => some [(1,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(8,1)]
  | 56 => some [(8,2)]
  | 57 => some [(5,0)]
  | 58 => some [(4,5)]
  | 59 => some [(7,0)]
  | _ => some [(8,3)]
theorem root6Node21Domains1_fast_eq : root6Node21Domains1 = expandDomains root6Node21Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node21Domains1 v = expandDomains root6Node21Domains1Fast v from by decide) v
theorem root6Node21Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root6Node21Domains0 root6Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains0 root6Node21Domains1
    root6Node21Domains0Fast root6Node21Domains1Fast
    root6Node21Domains0_fast_eq root6Node21Domains1_fast_eq (by decide)
theorem root6Node21Step1_checked :
    checkReplacement table37 root6Node21Domains0 root6Node21Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node21Step1Chunk0_0_checked, root6Node21Step1Chunk0_1_checked, root6Node21Step1Chunk0_2_checked, root6Node21Step1Chunk0_3_checked, root6Node21Step1Chunk0_4_checked, root6Node21Step1Chunk0_5_checked, root6Node21Step1Chunk1_0_checked, root6Node21Step1Chunk1_1_checked, root6Node21Step1Chunk1_2_checked, root6Node21Step1Chunk1_3_checked, root6Node21Step1Chunk1_4_checked, root6Node21Step1Chunk1_5_checked, root6Node21Step1Chunk2_0_checked, root6Node21Step1Chunk2_1_checked, root6Node21Step1Chunk2_2_checked, root6Node21Step1Chunk2_3_checked, root6Node21Step1Chunk2_4_checked, root6Node21Step1Chunk2_5_checked, root6Node21Step1Chunk3_0_checked, root6Node21Step1Chunk3_1_checked, root6Node21Step1Chunk3_2_checked, root6Node21Step1Chunk3_3_checked, root6Node21Step1Chunk3_4_checked, root6Node21Step1Chunk3_5_checked, root6Node21Step1Chunk4_0_checked, root6Node21Step1Chunk4_1_checked, root6Node21Step1Chunk4_2_checked, root6Node21Step1Chunk4_3_checked, root6Node21Step1Chunk4_4_checked, root6Node21Step1Chunk4_5_checked, root6Node21Step1Chunk5_0_checked, root6Node21Step1Chunk5_1_checked, root6Node21Step1Chunk5_2_checked, root6Node21Step1Chunk5_3_checked, root6Node21Step1Chunk5_4_checked, root6Node21Step1Chunk5_5_checked, root6Node21Step1Chunk6_0_checked, root6Node21Step1Chunk6_1_checked, root6Node21Step1Chunk6_2_checked, root6Node21Step1Chunk6_3_checked, root6Node21Step1Chunk6_4_checked, root6Node21Step1Chunk6_5_checked, root6Node21Step1Chunk7_0_checked, root6Node21Step1Chunk7_1_checked, root6Node21Step1Chunk7_2_checked, root6Node21Step1Chunk7_3_checked, root6Node21Step1Chunk7_4_checked, root6Node21Step1Chunk7_5_checked, root6Node21Step1Chunk8_0_checked, root6Node21Step1Chunk8_1_checked, root6Node21Step1Chunk8_2_checked, root6Node21Step1Chunk8_3_checked, root6Node21Step1Chunk8_4_checked, root6Node21Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root6Node21Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node21Domains1 (.output 9) = true := by decide
def root6Node22Domains0 : Domains 61 State := restrict root6Node20Domains2 11 (8,3)
def root6Node22Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,1)]
  | 6 => some [(6,5)]
  | 7 => some [(0,4)]
  | 8 => some [(5,4)]
  | 9 => some [(6,4)]
  | 10 => some [(1,2)]
  | 11 => some [(8,3)]
  | 12 => some [(5,5)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(1,4)]
  | 19 => some [(0,5)]
  | 20 => some [(4,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(2,4)]
  | 24 => some [(1,3)]
  | 25 => some [(5,2)]
  | 26 => some [(2,5),(7,5)]
  | 27 => some [(6,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(6,5)]
  | 33 => some [(0,4)]
  | 34 => some [(5,4)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(8,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(4,3)]
  | 43 => some [(5,1),(5,4),(8,4)]
  | 44 => some [(0,1),(6,4)]
  | 45 => some [(1,2),(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(7,5),(8,5)]
  | 51 => some [(0,3),(1,0)]
  | 52 => some [(7,1),(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(8,1)]
  | 56 => some [(4,2),(8,2)]
  | 57 => some [(5,0),(5,3)]
  | 58 => some [(4,5),(5,5),(8,5)]
  | 59 => some [(7,0)]
  | _ => some [(8,3)]
theorem root6Node22Domains0_fast_eq : root6Node22Domains0 = expandDomains root6Node22Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node22Domains0 v = expandDomains root6Node22Domains0Fast v from by decide) v
def root6Node22Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3)]
  | 5 => [(8,1)]
  | 6 => [(6,5)]
  | 7 => [(0,4)]
  | 8 => [(5,4)]
  | 9 => [(6,4)]
  | 10 => [(1,2)]
  | 11 => [(8,3)]
  | 12 => [(5,5)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(3,5)]
  | 16 => [(0,3)]
  | 17 => [(4,1)]
  | 18 => [(1,4)]
  | 19 => [(0,5)]
  | 20 => [(4,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(2,4)]
  | 24 => [(1,3)]
  | 25 => [(5,2)]
  | 26 => [(7,5)]
  | 27 => [(6,0)]
  | 28 => [(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(6,5)]
  | 33 => [(0,4)]
  | 34 => [(5,4)]
  | 35 => [(8,2)]
  | 36 => [(8,0)]
  | 37 => [(7,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(7,0)]
  | 42 => [(4,3)]
  | 43 => [(5,4),(8,4)]
  | 44 => [(6,4)]
  | 45 => [(1,2)]
  | 46 => [(8,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(7,4)]
  | 50 => [(7,5)]
  | 51 => [(0,3)]
  | 52 => [(8,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(8,1)]
  | 56 => [(4,2)]
  | 57 => [(5,3)]
  | 58 => [(5,5),(8,5)]
  | 59 => [(7,0)]
  | _ => [(8,3)]
def root6Node22Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,1)]
  | 6 => some [(6,5)]
  | 7 => some [(0,4)]
  | 8 => some [(5,4)]
  | 9 => some [(6,4)]
  | 10 => some [(1,2)]
  | 11 => some [(8,3)]
  | 12 => some [(5,5)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(1,4)]
  | 19 => some [(0,5)]
  | 20 => some [(4,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(2,4)]
  | 24 => some [(1,3)]
  | 25 => some [(5,2)]
  | 26 => some [(7,5)]
  | 27 => some [(6,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(6,5)]
  | 33 => some [(0,4)]
  | 34 => some [(5,4)]
  | 35 => some [(8,2)]
  | 36 => some [(8,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(4,3)]
  | 43 => some [(5,4),(8,4)]
  | 44 => some [(6,4)]
  | 45 => some [(1,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(7,5)]
  | 51 => some [(0,3)]
  | 52 => some [(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(8,1)]
  | 56 => some [(4,2)]
  | 57 => some [(5,3)]
  | 58 => some [(5,5),(8,5)]
  | 59 => some [(7,0)]
  | _ => some [(8,3)]
theorem root6Node22Domains1_fast_eq : root6Node22Domains1 = expandDomains root6Node22Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node22Domains1 v = expandDomains root6Node22Domains1Fast v from by decide) v
theorem root6Node22Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1_checked :
    checkReplacement table37 root6Node22Domains0 root6Node22Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node22Step1Chunk0_0_checked, root6Node22Step1Chunk0_1_checked, root6Node22Step1Chunk0_2_checked, root6Node22Step1Chunk0_3_checked, root6Node22Step1Chunk0_4_checked, root6Node22Step1Chunk0_5_checked, root6Node22Step1Chunk1_0_checked, root6Node22Step1Chunk1_1_checked, root6Node22Step1Chunk1_2_checked, root6Node22Step1Chunk1_3_checked, root6Node22Step1Chunk1_4_checked, root6Node22Step1Chunk1_5_checked, root6Node22Step1Chunk2_0_checked, root6Node22Step1Chunk2_1_checked, root6Node22Step1Chunk2_2_checked, root6Node22Step1Chunk2_3_checked, root6Node22Step1Chunk2_4_checked, root6Node22Step1Chunk2_5_checked, root6Node22Step1Chunk3_0_checked, root6Node22Step1Chunk3_1_checked, root6Node22Step1Chunk3_2_checked, root6Node22Step1Chunk3_3_checked, root6Node22Step1Chunk3_4_checked, root6Node22Step1Chunk3_5_checked, root6Node22Step1Chunk4_0_checked, root6Node22Step1Chunk4_1_checked, root6Node22Step1Chunk4_2_checked, root6Node22Step1Chunk4_3_checked, root6Node22Step1Chunk4_4_checked, root6Node22Step1Chunk4_5_checked, root6Node22Step1Chunk5_0_checked, root6Node22Step1Chunk5_1_checked, root6Node22Step1Chunk5_2_checked, root6Node22Step1Chunk5_3_checked, root6Node22Step1Chunk5_4_checked, root6Node22Step1Chunk5_5_checked, root6Node22Step1Chunk6_0_checked, root6Node22Step1Chunk6_1_checked, root6Node22Step1Chunk6_2_checked, root6Node22Step1Chunk6_3_checked, root6Node22Step1Chunk6_4_checked, root6Node22Step1Chunk6_5_checked, root6Node22Step1Chunk7_0_checked, root6Node22Step1Chunk7_1_checked, root6Node22Step1Chunk7_2_checked, root6Node22Step1Chunk7_3_checked, root6Node22Step1Chunk7_4_checked, root6Node22Step1Chunk7_5_checked, root6Node22Step1Chunk8_0_checked, root6Node22Step1Chunk8_1_checked, root6Node22Step1Chunk8_2_checked, root6Node22Step1Chunk8_3_checked, root6Node22Step1Chunk8_4_checked, root6Node22Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node23Domains0 : Domains 61 State := restrict root6Node22Domains1 43 (5,4)
def root6Node23Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,1)]
  | 6 => some [(6,5)]
  | 7 => some [(0,4)]
  | 8 => some [(5,4)]
  | 9 => some [(6,4)]
  | 10 => some [(1,2)]
  | 11 => some [(8,3)]
  | 12 => some [(5,5)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(1,4)]
  | 19 => some [(0,5)]
  | 20 => some [(4,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(2,4)]
  | 24 => some [(1,3)]
  | 25 => some [(5,2)]
  | 26 => some [(7,5)]
  | 27 => some [(6,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(6,5)]
  | 33 => some [(0,4)]
  | 34 => some [(5,4)]
  | 35 => some [(8,2)]
  | 36 => some [(8,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(4,3)]
  | 43 => some [(5,4)]
  | 44 => some [(6,4)]
  | 45 => some [(1,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(7,5)]
  | 51 => some [(0,3)]
  | 52 => some [(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(8,1)]
  | 56 => some [(4,2)]
  | 57 => some [(5,3)]
  | 58 => some [(5,5),(8,5)]
  | 59 => some [(7,0)]
  | _ => some [(8,3)]
theorem root6Node23Domains0_fast_eq : root6Node23Domains0 = expandDomains root6Node23Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node23Domains0 v = expandDomains root6Node23Domains0Fast v from by decide) v
def root6Node24Domains0 : Domains 61 State := restrict root6Node23Domains0 58 (5,5)
def root6Node24Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,1)]
  | 6 => some [(6,5)]
  | 7 => some [(0,4)]
  | 8 => some [(5,4)]
  | 9 => some [(6,4)]
  | 10 => some [(1,2)]
  | 11 => some [(8,3)]
  | 12 => some [(5,5)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(1,4)]
  | 19 => some [(0,5)]
  | 20 => some [(4,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(2,4)]
  | 24 => some [(1,3)]
  | 25 => some [(5,2)]
  | 26 => some [(7,5)]
  | 27 => some [(6,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(6,5)]
  | 33 => some [(0,4)]
  | 34 => some [(5,4)]
  | 35 => some [(8,2)]
  | 36 => some [(8,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(4,3)]
  | 43 => some [(5,4)]
  | 44 => some [(6,4)]
  | 45 => some [(1,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(7,5)]
  | 51 => some [(0,3)]
  | 52 => some [(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(8,1)]
  | 56 => some [(4,2)]
  | 57 => some [(5,3)]
  | 58 => some [(5,5)]
  | 59 => some [(7,0)]
  | _ => some [(8,3)]
theorem root6Node24Domains0_fast_eq : root6Node24Domains0 = expandDomains root6Node24Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node24Domains0 v = expandDomains root6Node24Domains0Fast v from by decide) v
theorem root6Node24Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node24Domains0 (.output 10) = true := by decide
def root6Node25Domains0 : Domains 61 State := restrict root6Node23Domains0 58 (8,5)
def root6Node25Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,1)]
  | 6 => some [(6,5)]
  | 7 => some [(0,4)]
  | 8 => some [(5,4)]
  | 9 => some [(6,4)]
  | 10 => some [(1,2)]
  | 11 => some [(8,3)]
  | 12 => some [(5,5)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(1,4)]
  | 19 => some [(0,5)]
  | 20 => some [(4,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(2,4)]
  | 24 => some [(1,3)]
  | 25 => some [(5,2)]
  | 26 => some [(7,5)]
  | 27 => some [(6,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(6,5)]
  | 33 => some [(0,4)]
  | 34 => some [(5,4)]
  | 35 => some [(8,2)]
  | 36 => some [(8,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(4,3)]
  | 43 => some [(5,4)]
  | 44 => some [(6,4)]
  | 45 => some [(1,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(7,5)]
  | 51 => some [(0,3)]
  | 52 => some [(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(8,1)]
  | 56 => some [(4,2)]
  | 57 => some [(5,3)]
  | 58 => some [(8,5)]
  | 59 => some [(7,0)]
  | _ => some [(8,3)]
theorem root6Node25Domains0_fast_eq : root6Node25Domains0 = expandDomains root6Node25Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node25Domains0 v = expandDomains root6Node25Domains0Fast v from by decide) v
theorem root6Node25Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node25Domains0 (.output 11) = true := by decide
end SpectreFinite.HexSearch.RadiusFour
