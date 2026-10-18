module

public import SpectreFinite.RadiusFourRoot6Part7
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable18
public import SpectreFinite.RadiusFourTable22
public import SpectreFinite.RadiusFourTable23
public import SpectreFinite.RadiusFourTable31
public import SpectreFinite.RadiusFourTable37

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node26Domains0 : Domains 61 State := restrict root6Node22Domains1 43 (8,4)
def root6Node26Domains0Fast (v : Fin 61) : Option (List State) :=
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
  | 43 => some [(8,4)]
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
theorem root6Node26Domains0_fast_eq : root6Node26Domains0 = expandDomains root6Node26Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node26Domains0 v = expandDomains root6Node26Domains0Fast v from by decide) v
def root6Node26Domains1 (v : Fin 61) : List State :=
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
  | 43 => [(8,4)]
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
  | 58 => [(8,5)]
  | 59 => [(7,0)]
  | _ => [(8,3)]
def root6Node26Domains1Fast (v : Fin 61) : Option (List State) :=
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
  | 43 => some [(8,4)]
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
theorem root6Node26Domains1_fast_eq : root6Node26Domains1 = expandDomains root6Node26Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node26Domains1 v = expandDomains root6Node26Domains1Fast v from by decide) v
theorem root6Node26Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root6Node26Domains0 root6Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node26Domains0 root6Node26Domains1
    root6Node26Domains0Fast root6Node26Domains1Fast
    root6Node26Domains0_fast_eq root6Node26Domains1_fast_eq (by decide)
theorem root6Node26Step1_checked :
    checkReplacement table37 root6Node26Domains0 root6Node26Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node26Step1Chunk0_0_checked, root6Node26Step1Chunk0_1_checked, root6Node26Step1Chunk0_2_checked, root6Node26Step1Chunk0_3_checked, root6Node26Step1Chunk0_4_checked, root6Node26Step1Chunk0_5_checked, root6Node26Step1Chunk1_0_checked, root6Node26Step1Chunk1_1_checked, root6Node26Step1Chunk1_2_checked, root6Node26Step1Chunk1_3_checked, root6Node26Step1Chunk1_4_checked, root6Node26Step1Chunk1_5_checked, root6Node26Step1Chunk2_0_checked, root6Node26Step1Chunk2_1_checked, root6Node26Step1Chunk2_2_checked, root6Node26Step1Chunk2_3_checked, root6Node26Step1Chunk2_4_checked, root6Node26Step1Chunk2_5_checked, root6Node26Step1Chunk3_0_checked, root6Node26Step1Chunk3_1_checked, root6Node26Step1Chunk3_2_checked, root6Node26Step1Chunk3_3_checked, root6Node26Step1Chunk3_4_checked, root6Node26Step1Chunk3_5_checked, root6Node26Step1Chunk4_0_checked, root6Node26Step1Chunk4_1_checked, root6Node26Step1Chunk4_2_checked, root6Node26Step1Chunk4_3_checked, root6Node26Step1Chunk4_4_checked, root6Node26Step1Chunk4_5_checked, root6Node26Step1Chunk5_0_checked, root6Node26Step1Chunk5_1_checked, root6Node26Step1Chunk5_2_checked, root6Node26Step1Chunk5_3_checked, root6Node26Step1Chunk5_4_checked, root6Node26Step1Chunk5_5_checked, root6Node26Step1Chunk6_0_checked, root6Node26Step1Chunk6_1_checked, root6Node26Step1Chunk6_2_checked, root6Node26Step1Chunk6_3_checked, root6Node26Step1Chunk6_4_checked, root6Node26Step1Chunk6_5_checked, root6Node26Step1Chunk7_0_checked, root6Node26Step1Chunk7_1_checked, root6Node26Step1Chunk7_2_checked, root6Node26Step1Chunk7_3_checked, root6Node26Step1Chunk7_4_checked, root6Node26Step1Chunk7_5_checked, root6Node26Step1Chunk8_0_checked, root6Node26Step1Chunk8_1_checked, root6Node26Step1Chunk8_2_checked, root6Node26Step1Chunk8_3_checked, root6Node26Step1Chunk8_4_checked, root6Node26Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root6Node26Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node26Domains1 (.output 12) = true := by decide
def root6Node27Domains0 : Domains 61 State := restrict root6Node11Domains1 1 (6,3)
def root6Node27Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2),(8,2)]
  | 3 => some [(4,0),(5,0),(7,4),(8,0)]
  | 4 => some [(1,3),(4,5),(7,3)]
  | 5 => some [(4,1),(8,1)]
  | 6 => some [(0,2),(6,5)]
  | 7 => some [(0,4),(1,1)]
  | 8 => some [(5,1),(5,4),(8,1)]
  | 9 => some [(0,0),(0,1),(6,4),(6,5)]
  | 10 => some [(0,4),(1,2),(6,2),(7,2)]
  | 11 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 12 => some [(5,2),(5,5)]
  | 13 => some [(7,0),(8,0)]
  | 14 => some [(4,3),(8,3)]
  | 15 => some [(1,5),(3,5),(5,5)]
  | 16 => some [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 17 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 18 => some [(0,1),(1,4),(6,5)]
  | 19 => some [(0,4),(0,5),(6,2)]
  | 20 => some [(4,4),(5,4),(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(2,0),(2,4),(4,4)]
  | 24 => some [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 25 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 26 => some [(2,5),(4,5),(7,5),(8,5)]
  | 27 => some [(1,0),(6,0),(7,0)]
  | 28 => some [(4,3),(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(3,1),(7,1)]
  | 32 => some [(0,1),(1,5),(6,5),(7,5)]
  | 33 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 34 => some [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(7,4),(8,0)]
  | 37 => some [(1,3),(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(1,0),(4,2),(7,0),(8,2)]
  | 42 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 43 => some [(5,1),(5,4),(8,1),(8,4)]
  | 44 => some [(0,1),(6,4),(6,5)]
  | 45 => some [(0,4),(1,2),(6,2)]
  | 46 => some [(5,4),(8,4)]
  | 47 => some [(0,0),(6,4)]
  | 48 => some [(1,2),(7,2)]
  | 49 => some [(4,0),(7,4),(8,4)]
  | 50 => some [(5,5),(7,5),(8,5)]
  | 51 => some [(0,3),(1,0),(7,0)]
  | 52 => some [(4,3),(7,1),(8,1)]
  | 53 => some [(1,5),(3,5),(7,5)]
  | 54 => some [(0,3),(6,1)]
  | 55 => some [(4,1),(5,1),(8,1)]
  | 56 => some [(4,2),(4,4),(7,2),(8,2)]
  | 57 => some [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 58 => some [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | _ => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
theorem root6Node27Domains0_fast_eq : root6Node27Domains0 = expandDomains root6Node27Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node27Domains0 v = expandDomains root6Node27Domains0Fast v from by decide) v
def root6Node27Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,0),(7,4)]
  | 4 => [(1,3),(7,3)]
  | 5 => [(4,1),(8,1)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(5,1),(8,1)]
  | 9 => [(0,1),(6,5)]
  | 10 => [(0,4),(6,2)]
  | 11 => [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 12 => [(5,2)]
  | 13 => [(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(1,0),(3,0),(7,0)]
  | 17 => [(2,1),(2,3),(2,5),(4,3)]
  | 18 => [(0,1),(1,4),(6,5)]
  | 19 => [(0,4),(6,2)]
  | 20 => [(5,4),(8,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(0,0),(1,4),(6,4)]
  | 25 => [(0,5),(1,2),(3,2),(7,2)]
  | 26 => [(2,5),(4,5),(7,5),(8,5)]
  | 27 => [(1,0),(6,0),(7,0)]
  | 28 => [(4,3),(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5),(7,5)]
  | 33 => [(0,3),(6,0),(6,1)]
  | 34 => [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 35 => [(7,2),(8,2)]
  | 36 => [(4,0),(7,4),(8,0)]
  | 37 => [(1,3),(7,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0),(8,0)]
  | 40 => [(4,5),(7,3)]
  | 41 => [(4,2),(7,0),(8,2)]
  | 42 => [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 43 => [(5,1),(5,4),(8,1),(8,4)]
  | 44 => [(0,1),(6,4),(6,5)]
  | 45 => [(0,4),(1,2),(6,2)]
  | 46 => [(5,4),(8,4)]
  | 47 => [(0,0),(6,4)]
  | 48 => [(1,2),(7,2)]
  | 49 => [(4,0),(7,4),(8,4)]
  | 50 => [(5,5),(7,5),(8,5)]
  | 51 => [(0,3),(1,0),(7,0)]
  | 52 => [(4,3),(7,1),(8,1)]
  | 53 => [(1,5),(3,5),(7,5)]
  | 54 => [(0,3),(6,1)]
  | 55 => [(4,1),(5,1),(8,1)]
  | 56 => [(4,2),(4,4),(7,2),(8,2)]
  | 57 => [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 58 => [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 59 => [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | _ => [(1,3),(3,3),(5,3),(7,3),(8,3)]
def root6Node27Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0),(7,4)]
  | 4 => some [(1,3),(7,3)]
  | 5 => some [(4,1),(8,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(5,1),(8,1)]
  | 9 => some [(0,1),(6,5)]
  | 10 => some [(0,4),(6,2)]
  | 11 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(1,0),(3,0),(7,0)]
  | 17 => some [(2,1),(2,3),(2,5),(4,3)]
  | 18 => some [(0,1),(1,4),(6,5)]
  | 19 => some [(0,4),(6,2)]
  | 20 => some [(5,4),(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0),(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(3,2),(7,2)]
  | 26 => some [(2,5),(4,5),(7,5),(8,5)]
  | 27 => some [(1,0),(6,0),(7,0)]
  | 28 => some [(4,3),(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,0),(6,1)]
  | 34 => some [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(7,4),(8,0)]
  | 37 => some [(1,3),(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 43 => some [(5,1),(5,4),(8,1),(8,4)]
  | 44 => some [(0,1),(6,4),(6,5)]
  | 45 => some [(0,4),(1,2),(6,2)]
  | 46 => some [(5,4),(8,4)]
  | 47 => some [(0,0),(6,4)]
  | 48 => some [(1,2),(7,2)]
  | 49 => some [(4,0),(7,4),(8,4)]
  | 50 => some [(5,5),(7,5),(8,5)]
  | 51 => some [(0,3),(1,0),(7,0)]
  | 52 => some [(4,3),(7,1),(8,1)]
  | 53 => some [(1,5),(3,5),(7,5)]
  | 54 => some [(0,3),(6,1)]
  | 55 => some [(4,1),(5,1),(8,1)]
  | 56 => some [(4,2),(4,4),(7,2),(8,2)]
  | 57 => some [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 58 => some [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | _ => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
theorem root6Node27Domains1_fast_eq : root6Node27Domains1 = expandDomains root6Node27Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node27Domains1 v = expandDomains root6Node27Domains1Fast v from by decide) v
theorem root6Node27Step1Chunk0_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_0⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk0_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_1⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk0_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_2⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk0_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_3⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk0_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_4⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk0_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_5⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk1_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_0⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk1_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_1⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk1_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_2⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk1_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_3⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk1_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_4⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk1_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_5⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk2_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_0⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk2_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_1⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk2_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_2⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk2_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_3⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk2_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_4⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk2_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_5⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk3_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_0⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk3_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_1⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk3_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_2⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk3_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_3⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk3_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_4⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk3_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_5⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk4_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_0⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk4_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_1⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk4_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_2⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk4_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_3⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk4_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_4⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk4_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_5⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk5_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_0⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk5_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_1⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk5_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_2⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk5_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_3⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk5_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_4⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk5_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_5⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk6_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_0⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk6_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_1⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk6_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_2⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk6_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_3⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk6_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_4⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk6_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_5⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk7_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_0⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk7_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_1⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk7_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_2⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk7_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_3⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk7_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_4⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk7_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_5⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk8_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_0⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk8_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_1⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk8_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_2⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk8_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_3⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk8_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_4⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk8_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_5⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1_checked :
    checkReplacement table22 root6Node27Domains0 root6Node27Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node27Step1Chunk0_0_checked, root6Node27Step1Chunk0_1_checked, root6Node27Step1Chunk0_2_checked, root6Node27Step1Chunk0_3_checked, root6Node27Step1Chunk0_4_checked, root6Node27Step1Chunk0_5_checked, root6Node27Step1Chunk1_0_checked, root6Node27Step1Chunk1_1_checked, root6Node27Step1Chunk1_2_checked, root6Node27Step1Chunk1_3_checked, root6Node27Step1Chunk1_4_checked, root6Node27Step1Chunk1_5_checked, root6Node27Step1Chunk2_0_checked, root6Node27Step1Chunk2_1_checked, root6Node27Step1Chunk2_2_checked, root6Node27Step1Chunk2_3_checked, root6Node27Step1Chunk2_4_checked, root6Node27Step1Chunk2_5_checked, root6Node27Step1Chunk3_0_checked, root6Node27Step1Chunk3_1_checked, root6Node27Step1Chunk3_2_checked, root6Node27Step1Chunk3_3_checked, root6Node27Step1Chunk3_4_checked, root6Node27Step1Chunk3_5_checked, root6Node27Step1Chunk4_0_checked, root6Node27Step1Chunk4_1_checked, root6Node27Step1Chunk4_2_checked, root6Node27Step1Chunk4_3_checked, root6Node27Step1Chunk4_4_checked, root6Node27Step1Chunk4_5_checked, root6Node27Step1Chunk5_0_checked, root6Node27Step1Chunk5_1_checked, root6Node27Step1Chunk5_2_checked, root6Node27Step1Chunk5_3_checked, root6Node27Step1Chunk5_4_checked, root6Node27Step1Chunk5_5_checked, root6Node27Step1Chunk6_0_checked, root6Node27Step1Chunk6_1_checked, root6Node27Step1Chunk6_2_checked, root6Node27Step1Chunk6_3_checked, root6Node27Step1Chunk6_4_checked, root6Node27Step1Chunk6_5_checked, root6Node27Step1Chunk7_0_checked, root6Node27Step1Chunk7_1_checked, root6Node27Step1Chunk7_2_checked, root6Node27Step1Chunk7_3_checked, root6Node27Step1Chunk7_4_checked, root6Node27Step1Chunk7_5_checked, root6Node27Step1Chunk8_0_checked, root6Node27Step1Chunk8_1_checked, root6Node27Step1Chunk8_2_checked, root6Node27Step1Chunk8_3_checked, root6Node27Step1Chunk8_4_checked, root6Node27Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node27Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,0),(7,4)]
  | 4 => [(1,3),(7,3)]
  | 5 => [(4,1)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(5,1),(8,1)]
  | 9 => [(0,1),(6,5)]
  | 10 => [(0,4),(6,2)]
  | 11 => [(1,3),(3,3),(7,3)]
  | 12 => [(5,2)]
  | 13 => [(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(1,0),(3,0),(7,0)]
  | 17 => [(2,1),(2,3),(2,5),(4,3)]
  | 18 => [(0,1),(6,5)]
  | 19 => [(0,4),(6,2)]
  | 20 => [(5,4),(8,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(0,0),(1,4),(6,4)]
  | 25 => [(0,5),(1,2),(3,2),(7,2)]
  | 26 => [(4,5),(8,5)]
  | 27 => [(1,0),(7,0)]
  | 28 => [(4,3),(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5),(7,5)]
  | 33 => [(0,3),(6,0),(6,1)]
  | 34 => [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 35 => [(7,2),(8,2)]
  | 36 => [(4,0),(7,4),(8,0)]
  | 37 => [(1,3),(7,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0),(8,0)]
  | 40 => [(4,5),(7,3)]
  | 41 => [(4,2),(7,0),(8,2)]
  | 42 => [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 43 => [(5,1),(5,4),(8,1)]
  | 44 => [(0,1),(6,4),(6,5)]
  | 45 => [(0,4),(1,2),(6,2)]
  | 46 => [(5,4),(8,4)]
  | 47 => [(0,0),(6,4)]
  | 48 => [(1,2),(7,2)]
  | 49 => [(4,0),(7,4),(8,4)]
  | 50 => [(5,5),(7,5),(8,5)]
  | 51 => [(0,3),(1,0),(7,0)]
  | 52 => [(4,3),(7,1),(8,1)]
  | 53 => [(1,5),(3,5),(7,5)]
  | 54 => [(0,3),(6,1)]
  | 55 => [(4,1),(5,1),(8,1)]
  | 56 => [(4,2),(4,4),(7,2),(8,2)]
  | 57 => [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 58 => [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 59 => [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | _ => [(1,3),(3,3),(5,3),(7,3),(8,3)]
def root6Node27Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0),(7,4)]
  | 4 => some [(1,3),(7,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(5,1),(8,1)]
  | 9 => some [(0,1),(6,5)]
  | 10 => some [(0,4),(6,2)]
  | 11 => some [(1,3),(3,3),(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(1,0),(3,0),(7,0)]
  | 17 => some [(2,1),(2,3),(2,5),(4,3)]
  | 18 => some [(0,1),(6,5)]
  | 19 => some [(0,4),(6,2)]
  | 20 => some [(5,4),(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0),(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(3,2),(7,2)]
  | 26 => some [(4,5),(8,5)]
  | 27 => some [(1,0),(7,0)]
  | 28 => some [(4,3),(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,0),(6,1)]
  | 34 => some [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(7,4),(8,0)]
  | 37 => some [(1,3),(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 43 => some [(5,1),(5,4),(8,1)]
  | 44 => some [(0,1),(6,4),(6,5)]
  | 45 => some [(0,4),(1,2),(6,2)]
  | 46 => some [(5,4),(8,4)]
  | 47 => some [(0,0),(6,4)]
  | 48 => some [(1,2),(7,2)]
  | 49 => some [(4,0),(7,4),(8,4)]
  | 50 => some [(5,5),(7,5),(8,5)]
  | 51 => some [(0,3),(1,0),(7,0)]
  | 52 => some [(4,3),(7,1),(8,1)]
  | 53 => some [(1,5),(3,5),(7,5)]
  | 54 => some [(0,3),(6,1)]
  | 55 => some [(4,1),(5,1),(8,1)]
  | 56 => some [(4,2),(4,4),(7,2),(8,2)]
  | 57 => some [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 58 => some [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | _ => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
theorem root6Node27Domains2_fast_eq : root6Node27Domains2 = expandDomains root6Node27Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node27Domains2 v = expandDomains root6Node27Domains2Fast v from by decide) v
theorem root6Node27Step2Chunk0_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk0_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk0_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk0_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk0_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk0_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk1_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk1_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk1_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk1_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk1_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk1_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk2_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk2_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk2_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk2_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk2_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk2_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk3_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk3_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk3_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk3_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk3_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk3_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk4_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk4_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk4_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk4_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk4_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk4_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk5_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk5_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk5_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk5_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk5_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk5_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk6_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk6_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk6_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk6_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk6_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk6_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk7_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk7_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk7_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk7_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk7_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk7_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk8_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk8_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk8_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk8_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk8_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk8_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2_checked :
    checkReplacement table18 root6Node27Domains1 root6Node27Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node27Step2Chunk0_0_checked, root6Node27Step2Chunk0_1_checked, root6Node27Step2Chunk0_2_checked, root6Node27Step2Chunk0_3_checked, root6Node27Step2Chunk0_4_checked, root6Node27Step2Chunk0_5_checked, root6Node27Step2Chunk1_0_checked, root6Node27Step2Chunk1_1_checked, root6Node27Step2Chunk1_2_checked, root6Node27Step2Chunk1_3_checked, root6Node27Step2Chunk1_4_checked, root6Node27Step2Chunk1_5_checked, root6Node27Step2Chunk2_0_checked, root6Node27Step2Chunk2_1_checked, root6Node27Step2Chunk2_2_checked, root6Node27Step2Chunk2_3_checked, root6Node27Step2Chunk2_4_checked, root6Node27Step2Chunk2_5_checked, root6Node27Step2Chunk3_0_checked, root6Node27Step2Chunk3_1_checked, root6Node27Step2Chunk3_2_checked, root6Node27Step2Chunk3_3_checked, root6Node27Step2Chunk3_4_checked, root6Node27Step2Chunk3_5_checked, root6Node27Step2Chunk4_0_checked, root6Node27Step2Chunk4_1_checked, root6Node27Step2Chunk4_2_checked, root6Node27Step2Chunk4_3_checked, root6Node27Step2Chunk4_4_checked, root6Node27Step2Chunk4_5_checked, root6Node27Step2Chunk5_0_checked, root6Node27Step2Chunk5_1_checked, root6Node27Step2Chunk5_2_checked, root6Node27Step2Chunk5_3_checked, root6Node27Step2Chunk5_4_checked, root6Node27Step2Chunk5_5_checked, root6Node27Step2Chunk6_0_checked, root6Node27Step2Chunk6_1_checked, root6Node27Step2Chunk6_2_checked, root6Node27Step2Chunk6_3_checked, root6Node27Step2Chunk6_4_checked, root6Node27Step2Chunk6_5_checked, root6Node27Step2Chunk7_0_checked, root6Node27Step2Chunk7_1_checked, root6Node27Step2Chunk7_2_checked, root6Node27Step2Chunk7_3_checked, root6Node27Step2Chunk7_4_checked, root6Node27Step2Chunk7_5_checked, root6Node27Step2Chunk8_0_checked, root6Node27Step2Chunk8_1_checked, root6Node27Step2Chunk8_2_checked, root6Node27Step2Chunk8_3_checked, root6Node27Step2Chunk8_4_checked, root6Node27Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node27Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,0),(7,4)]
  | 4 => [(1,3),(7,3)]
  | 5 => [(4,1)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(5,1),(8,1)]
  | 9 => [(0,1),(6,5)]
  | 10 => [(0,4),(6,2)]
  | 11 => [(1,3),(3,3),(7,3)]
  | 12 => [(5,2)]
  | 13 => [(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(1,0),(3,0),(7,0)]
  | 17 => [(2,1),(2,3),(2,5),(4,3)]
  | 18 => [(0,1),(6,5)]
  | 19 => [(0,4),(6,2)]
  | 20 => [(5,4),(8,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(0,0),(1,4),(6,4)]
  | 25 => [(0,5),(1,2),(3,2),(7,2)]
  | 26 => [(4,5),(8,5)]
  | 27 => [(1,0),(7,0)]
  | 28 => [(4,3),(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5),(7,5)]
  | 33 => [(0,3),(6,0),(6,1)]
  | 34 => [(3,1),(5,1),(7,1)]
  | 35 => [(7,2),(8,2)]
  | 36 => [(4,0),(7,4),(8,0)]
  | 37 => [(1,3),(7,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0),(8,0)]
  | 40 => [(4,5),(7,3)]
  | 41 => [(4,2),(7,0),(8,2)]
  | 42 => [(5,0),(5,3),(8,3)]
  | 43 => [(5,1),(5,4),(8,1)]
  | 44 => [(0,1),(6,4),(6,5)]
  | 45 => [(0,4),(1,2),(6,2)]
  | 46 => [(5,4),(8,4)]
  | 47 => [(0,0),(6,4)]
  | 48 => [(1,2),(7,2)]
  | 49 => [(7,4),(8,4)]
  | 50 => [(5,5),(7,5),(8,5)]
  | 51 => [(0,3),(1,0),(7,0)]
  | 52 => [(4,3),(7,1),(8,1)]
  | 53 => [(1,5),(3,5),(7,5)]
  | 54 => [(0,3),(6,1)]
  | 55 => [(4,1),(8,1)]
  | 56 => [(4,2),(4,4),(7,2),(8,2)]
  | 57 => [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 58 => [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 59 => [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | _ => [(1,3),(3,3),(5,3),(7,3),(8,3)]
def root6Node27Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0),(7,4)]
  | 4 => some [(1,3),(7,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(5,1),(8,1)]
  | 9 => some [(0,1),(6,5)]
  | 10 => some [(0,4),(6,2)]
  | 11 => some [(1,3),(3,3),(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(1,0),(3,0),(7,0)]
  | 17 => some [(2,1),(2,3),(2,5),(4,3)]
  | 18 => some [(0,1),(6,5)]
  | 19 => some [(0,4),(6,2)]
  | 20 => some [(5,4),(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0),(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(3,2),(7,2)]
  | 26 => some [(4,5),(8,5)]
  | 27 => some [(1,0),(7,0)]
  | 28 => some [(4,3),(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,0),(6,1)]
  | 34 => some [(3,1),(5,1),(7,1)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(7,4),(8,0)]
  | 37 => some [(1,3),(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(5,0),(5,3),(8,3)]
  | 43 => some [(5,1),(5,4),(8,1)]
  | 44 => some [(0,1),(6,4),(6,5)]
  | 45 => some [(0,4),(1,2),(6,2)]
  | 46 => some [(5,4),(8,4)]
  | 47 => some [(0,0),(6,4)]
  | 48 => some [(1,2),(7,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(5,5),(7,5),(8,5)]
  | 51 => some [(0,3),(1,0),(7,0)]
  | 52 => some [(4,3),(7,1),(8,1)]
  | 53 => some [(1,5),(3,5),(7,5)]
  | 54 => some [(0,3),(6,1)]
  | 55 => some [(4,1),(8,1)]
  | 56 => some [(4,2),(4,4),(7,2),(8,2)]
  | 57 => some [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 58 => some [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | _ => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
theorem root6Node27Domains3_fast_eq : root6Node27Domains3 = expandDomains root6Node27Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node27Domains3 v = expandDomains root6Node27Domains3Fast v from by decide) v
theorem root6Node27Step3Chunk0_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_0⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk0_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_1⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk0_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_2⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk0_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_3⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk0_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_4⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk0_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_5⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk1_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_0⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk1_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_1⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk1_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_2⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk1_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_3⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk1_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_4⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk1_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_5⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk2_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_0⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk2_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_1⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk2_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_2⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk2_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_3⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk2_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_4⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk2_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_5⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk3_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_0⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk3_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_1⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk3_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_2⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk3_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_3⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk3_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_4⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk3_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_5⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk4_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_0⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk4_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_1⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk4_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_2⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk4_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_3⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk4_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_4⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk4_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_5⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk5_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_0⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk5_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_1⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk5_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_2⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk5_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_3⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk5_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_4⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk5_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_5⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk6_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_0⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk6_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_1⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk6_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_2⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk6_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_3⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk6_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_4⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk6_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_5⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk7_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_0⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk7_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_1⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk7_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_2⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk7_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_3⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk7_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_4⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk7_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_5⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk8_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_0⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk8_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_1⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk8_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_2⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk8_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_3⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk8_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_4⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3Chunk8_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_5⟩
      root6Node27Domains2 root6Node27Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains2 root6Node27Domains3
    root6Node27Domains2Fast root6Node27Domains3Fast
    root6Node27Domains2_fast_eq root6Node27Domains3_fast_eq (by decide)
theorem root6Node27Step3_checked :
    checkReplacement table31 root6Node27Domains2 root6Node27Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node27Step3Chunk0_0_checked, root6Node27Step3Chunk0_1_checked, root6Node27Step3Chunk0_2_checked, root6Node27Step3Chunk0_3_checked, root6Node27Step3Chunk0_4_checked, root6Node27Step3Chunk0_5_checked, root6Node27Step3Chunk1_0_checked, root6Node27Step3Chunk1_1_checked, root6Node27Step3Chunk1_2_checked, root6Node27Step3Chunk1_3_checked, root6Node27Step3Chunk1_4_checked, root6Node27Step3Chunk1_5_checked, root6Node27Step3Chunk2_0_checked, root6Node27Step3Chunk2_1_checked, root6Node27Step3Chunk2_2_checked, root6Node27Step3Chunk2_3_checked, root6Node27Step3Chunk2_4_checked, root6Node27Step3Chunk2_5_checked, root6Node27Step3Chunk3_0_checked, root6Node27Step3Chunk3_1_checked, root6Node27Step3Chunk3_2_checked, root6Node27Step3Chunk3_3_checked, root6Node27Step3Chunk3_4_checked, root6Node27Step3Chunk3_5_checked, root6Node27Step3Chunk4_0_checked, root6Node27Step3Chunk4_1_checked, root6Node27Step3Chunk4_2_checked, root6Node27Step3Chunk4_3_checked, root6Node27Step3Chunk4_4_checked, root6Node27Step3Chunk4_5_checked, root6Node27Step3Chunk5_0_checked, root6Node27Step3Chunk5_1_checked, root6Node27Step3Chunk5_2_checked, root6Node27Step3Chunk5_3_checked, root6Node27Step3Chunk5_4_checked, root6Node27Step3Chunk5_5_checked, root6Node27Step3Chunk6_0_checked, root6Node27Step3Chunk6_1_checked, root6Node27Step3Chunk6_2_checked, root6Node27Step3Chunk6_3_checked, root6Node27Step3Chunk6_4_checked, root6Node27Step3Chunk6_5_checked, root6Node27Step3Chunk7_0_checked, root6Node27Step3Chunk7_1_checked, root6Node27Step3Chunk7_2_checked, root6Node27Step3Chunk7_3_checked, root6Node27Step3Chunk7_4_checked, root6Node27Step3Chunk7_5_checked, root6Node27Step3Chunk8_0_checked, root6Node27Step3Chunk8_1_checked, root6Node27Step3Chunk8_2_checked, root6Node27Step3Chunk8_3_checked, root6Node27Step3Chunk8_4_checked, root6Node27Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node28Domains0 : Domains 61 State := restrict root6Node27Domains3 3 (4,0)
def root6Node28Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(1,3),(7,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(5,1),(8,1)]
  | 9 => some [(0,1),(6,5)]
  | 10 => some [(0,4),(6,2)]
  | 11 => some [(1,3),(3,3),(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(1,0),(3,0),(7,0)]
  | 17 => some [(2,1),(2,3),(2,5),(4,3)]
  | 18 => some [(0,1),(6,5)]
  | 19 => some [(0,4),(6,2)]
  | 20 => some [(5,4),(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0),(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(3,2),(7,2)]
  | 26 => some [(4,5),(8,5)]
  | 27 => some [(1,0),(7,0)]
  | 28 => some [(4,3),(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,0),(6,1)]
  | 34 => some [(3,1),(5,1),(7,1)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(7,4),(8,0)]
  | 37 => some [(1,3),(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(5,0),(5,3),(8,3)]
  | 43 => some [(5,1),(5,4),(8,1)]
  | 44 => some [(0,1),(6,4),(6,5)]
  | 45 => some [(0,4),(1,2),(6,2)]
  | 46 => some [(5,4),(8,4)]
  | 47 => some [(0,0),(6,4)]
  | 48 => some [(1,2),(7,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(5,5),(7,5),(8,5)]
  | 51 => some [(0,3),(1,0),(7,0)]
  | 52 => some [(4,3),(7,1),(8,1)]
  | 53 => some [(1,5),(3,5),(7,5)]
  | 54 => some [(0,3),(6,1)]
  | 55 => some [(4,1),(8,1)]
  | 56 => some [(4,2),(4,4),(7,2),(8,2)]
  | 57 => some [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 58 => some [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | _ => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
theorem root6Node28Domains0_fast_eq : root6Node28Domains0 = expandDomains root6Node28Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node28Domains0 v = expandDomains root6Node28Domains0Fast v from by decide) v
def root6Node28Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(4,1)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(5,1)]
  | 9 => [(0,1)]
  | 10 => [(6,2)]
  | 11 => [(1,3),(3,3),(7,3)]
  | 12 => [(5,2)]
  | 13 => [(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(1,0)]
  | 17 => [(2,1)]
  | 18 => [(0,1),(6,5)]
  | 19 => [(0,4),(6,2)]
  | 20 => [(5,4),(8,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(0,0)]
  | 25 => [(3,2)]
  | 26 => [(4,5),(8,5)]
  | 27 => [(1,0),(7,0)]
  | 28 => [(4,3),(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5)]
  | 33 => [(6,1)]
  | 34 => [(5,1)]
  | 35 => [(7,2),(8,2)]
  | 36 => [(4,0),(7,4),(8,0)]
  | 37 => [(1,3),(7,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(7,0)]
  | 42 => [(8,3)]
  | 43 => [(5,1),(5,4),(8,1)]
  | 44 => [(0,1),(6,4),(6,5)]
  | 45 => [(0,4),(1,2),(6,2)]
  | 46 => [(5,4),(8,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(7,4)]
  | 50 => [(5,5),(7,5),(8,5)]
  | 51 => [(0,3),(1,0),(7,0)]
  | 52 => [(4,3),(7,1),(8,1)]
  | 53 => [(1,5),(3,5),(7,5)]
  | 54 => [(0,3),(6,1)]
  | 55 => [(4,1),(8,1)]
  | 56 => [(4,2),(4,4),(7,2),(8,2)]
  | 57 => [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 58 => [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 59 => [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | _ => [(1,3),(3,3),(5,3),(7,3),(8,3)]
def root6Node28Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(5,1)]
  | 9 => some [(0,1)]
  | 10 => some [(6,2)]
  | 11 => some [(1,3),(3,3),(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(1,0)]
  | 17 => some [(2,1)]
  | 18 => some [(0,1),(6,5)]
  | 19 => some [(0,4),(6,2)]
  | 20 => some [(5,4),(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0)]
  | 25 => some [(3,2)]
  | 26 => some [(4,5),(8,5)]
  | 27 => some [(1,0),(7,0)]
  | 28 => some [(4,3),(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(7,4),(8,0)]
  | 37 => some [(1,3),(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(8,3)]
  | 43 => some [(5,1),(5,4),(8,1)]
  | 44 => some [(0,1),(6,4),(6,5)]
  | 45 => some [(0,4),(1,2),(6,2)]
  | 46 => some [(5,4),(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,5),(7,5),(8,5)]
  | 51 => some [(0,3),(1,0),(7,0)]
  | 52 => some [(4,3),(7,1),(8,1)]
  | 53 => some [(1,5),(3,5),(7,5)]
  | 54 => some [(0,3),(6,1)]
  | 55 => some [(4,1),(8,1)]
  | 56 => some [(4,2),(4,4),(7,2),(8,2)]
  | 57 => some [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 58 => some [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | _ => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
theorem root6Node28Domains1_fast_eq : root6Node28Domains1 = expandDomains root6Node28Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node28Domains1 v = expandDomains root6Node28Domains1Fast v from by decide) v
theorem root6Node28Step1Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1_checked :
    checkReplacement table23 root6Node28Domains0 root6Node28Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node28Step1Chunk0_0_checked, root6Node28Step1Chunk0_1_checked, root6Node28Step1Chunk0_2_checked, root6Node28Step1Chunk0_3_checked, root6Node28Step1Chunk0_4_checked, root6Node28Step1Chunk0_5_checked, root6Node28Step1Chunk1_0_checked, root6Node28Step1Chunk1_1_checked, root6Node28Step1Chunk1_2_checked, root6Node28Step1Chunk1_3_checked, root6Node28Step1Chunk1_4_checked, root6Node28Step1Chunk1_5_checked, root6Node28Step1Chunk2_0_checked, root6Node28Step1Chunk2_1_checked, root6Node28Step1Chunk2_2_checked, root6Node28Step1Chunk2_3_checked, root6Node28Step1Chunk2_4_checked, root6Node28Step1Chunk2_5_checked, root6Node28Step1Chunk3_0_checked, root6Node28Step1Chunk3_1_checked, root6Node28Step1Chunk3_2_checked, root6Node28Step1Chunk3_3_checked, root6Node28Step1Chunk3_4_checked, root6Node28Step1Chunk3_5_checked, root6Node28Step1Chunk4_0_checked, root6Node28Step1Chunk4_1_checked, root6Node28Step1Chunk4_2_checked, root6Node28Step1Chunk4_3_checked, root6Node28Step1Chunk4_4_checked, root6Node28Step1Chunk4_5_checked, root6Node28Step1Chunk5_0_checked, root6Node28Step1Chunk5_1_checked, root6Node28Step1Chunk5_2_checked, root6Node28Step1Chunk5_3_checked, root6Node28Step1Chunk5_4_checked, root6Node28Step1Chunk5_5_checked, root6Node28Step1Chunk6_0_checked, root6Node28Step1Chunk6_1_checked, root6Node28Step1Chunk6_2_checked, root6Node28Step1Chunk6_3_checked, root6Node28Step1Chunk6_4_checked, root6Node28Step1Chunk6_5_checked, root6Node28Step1Chunk7_0_checked, root6Node28Step1Chunk7_1_checked, root6Node28Step1Chunk7_2_checked, root6Node28Step1Chunk7_3_checked, root6Node28Step1Chunk7_4_checked, root6Node28Step1Chunk7_5_checked, root6Node28Step1Chunk8_0_checked, root6Node28Step1Chunk8_1_checked, root6Node28Step1Chunk8_2_checked, root6Node28Step1Chunk8_3_checked, root6Node28Step1Chunk8_4_checked, root6Node28Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
