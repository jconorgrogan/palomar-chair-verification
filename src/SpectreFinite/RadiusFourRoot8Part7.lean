module

public import SpectreFinite.RadiusFourRoot8Part6
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable37

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node19Domains0 : Domains 61 State := restrict root8Node18Domains1 26 (1,2)
def root8Node19Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(1,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(1,5)]
  | 50 => some [(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,1),(5,4)]
  | 57 => some [(0,1),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root8Node19Domains0_fast_eq : root8Node19Domains0 = expandDomains root8Node19Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node19Domains0 v = expandDomains root8Node19Domains0Fast v from by decide) v
def root8Node20Domains0 : Domains 61 State := restrict root8Node19Domains0 50 (7,2)
def root8Node20Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(1,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(1,5)]
  | 50 => some [(7,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,1),(5,4)]
  | 57 => some [(0,1),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root8Node20Domains0_fast_eq : root8Node20Domains0 = expandDomains root8Node20Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node20Domains0 v = expandDomains root8Node20Domains0Fast v from by decide) v
def root8Node20Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(8,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(1,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(5,0)]
  | 34 => [(4,5)]
  | 35 => [(5,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(8,4)]
  | 42 => [(0,0)]
  | 43 => [(8,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(0,3)]
  | 48 => [(8,1)]
  | 49 => [(1,5)]
  | 50 => [(7,2)]
  | 51 => [(4,0)]
  | 52 => [(7,3)]
  | 53 => [(4,2)]
  | 54 => [(5,3)]
  | 55 => [(8,5)]
  | 56 => [(5,1)]
  | 57 => [(0,1)]
  | 58 => [(6,2)]
  | 59 => [(7,4)]
  | _ => [(6,3)]
def root8Node20Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(1,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(1,5)]
  | 50 => some [(7,2)]
  | 51 => some [(4,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root8Node20Domains1_fast_eq : root8Node20Domains1 = expandDomains root8Node20Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node20Domains1 v = expandDomains root8Node20Domains1Fast v from by decide) v
theorem root8Node20Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root8Node20Domains0 root8Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node20Domains0 root8Node20Domains1
    root8Node20Domains0Fast root8Node20Domains1Fast
    root8Node20Domains0_fast_eq root8Node20Domains1_fast_eq (by decide)
theorem root8Node20Step1_checked :
    checkReplacement table37 root8Node20Domains0 root8Node20Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node20Step1Chunk0_0_checked, root8Node20Step1Chunk0_1_checked, root8Node20Step1Chunk0_2_checked, root8Node20Step1Chunk0_3_checked, root8Node20Step1Chunk0_4_checked, root8Node20Step1Chunk0_5_checked, root8Node20Step1Chunk1_0_checked, root8Node20Step1Chunk1_1_checked, root8Node20Step1Chunk1_2_checked, root8Node20Step1Chunk1_3_checked, root8Node20Step1Chunk1_4_checked, root8Node20Step1Chunk1_5_checked, root8Node20Step1Chunk2_0_checked, root8Node20Step1Chunk2_1_checked, root8Node20Step1Chunk2_2_checked, root8Node20Step1Chunk2_3_checked, root8Node20Step1Chunk2_4_checked, root8Node20Step1Chunk2_5_checked, root8Node20Step1Chunk3_0_checked, root8Node20Step1Chunk3_1_checked, root8Node20Step1Chunk3_2_checked, root8Node20Step1Chunk3_3_checked, root8Node20Step1Chunk3_4_checked, root8Node20Step1Chunk3_5_checked, root8Node20Step1Chunk4_0_checked, root8Node20Step1Chunk4_1_checked, root8Node20Step1Chunk4_2_checked, root8Node20Step1Chunk4_3_checked, root8Node20Step1Chunk4_4_checked, root8Node20Step1Chunk4_5_checked, root8Node20Step1Chunk5_0_checked, root8Node20Step1Chunk5_1_checked, root8Node20Step1Chunk5_2_checked, root8Node20Step1Chunk5_3_checked, root8Node20Step1Chunk5_4_checked, root8Node20Step1Chunk5_5_checked, root8Node20Step1Chunk6_0_checked, root8Node20Step1Chunk6_1_checked, root8Node20Step1Chunk6_2_checked, root8Node20Step1Chunk6_3_checked, root8Node20Step1Chunk6_4_checked, root8Node20Step1Chunk6_5_checked, root8Node20Step1Chunk7_0_checked, root8Node20Step1Chunk7_1_checked, root8Node20Step1Chunk7_2_checked, root8Node20Step1Chunk7_3_checked, root8Node20Step1Chunk7_4_checked, root8Node20Step1Chunk7_5_checked, root8Node20Step1Chunk8_0_checked, root8Node20Step1Chunk8_1_checked, root8Node20Step1Chunk8_2_checked, root8Node20Step1Chunk8_3_checked, root8Node20Step1Chunk8_4_checked, root8Node20Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node20Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node20Domains1 (.output 8) = true := by decide
def root8Node21Domains0 : Domains 61 State := restrict root8Node19Domains0 50 (8,2)
def root8Node21Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(1,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(1,5)]
  | 50 => some [(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,1),(5,4)]
  | 57 => some [(0,1),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root8Node21Domains0_fast_eq : root8Node21Domains0 = expandDomains root8Node21Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node21Domains0 v = expandDomains root8Node21Domains0Fast v from by decide) v
def root8Node21Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(8,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(1,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(5,0)]
  | 34 => [(4,5)]
  | 35 => [(5,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(8,4)]
  | 42 => [(0,0)]
  | 43 => [(8,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(0,3)]
  | 48 => [(8,1)]
  | 49 => [(1,5)]
  | 50 => [(8,2)]
  | 51 => [(8,0)]
  | 52 => [(7,3)]
  | 53 => [(4,2)]
  | 54 => [(5,3)]
  | 55 => [(8,5)]
  | 56 => [(5,4)]
  | 57 => [(6,4)]
  | 58 => [(1,2)]
  | 59 => [(7,4)]
  | _ => [(6,3)]
def root8Node21Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(1,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(1,5)]
  | 50 => some [(8,2)]
  | 51 => some [(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,4)]
  | 57 => some [(6,4)]
  | 58 => some [(1,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root8Node21Domains1_fast_eq : root8Node21Domains1 = expandDomains root8Node21Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node21Domains1 v = expandDomains root8Node21Domains1Fast v from by decide) v
theorem root8Node21Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root8Node21Domains0 root8Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node21Domains0 root8Node21Domains1
    root8Node21Domains0Fast root8Node21Domains1Fast
    root8Node21Domains0_fast_eq root8Node21Domains1_fast_eq (by decide)
theorem root8Node21Step1_checked :
    checkReplacement table37 root8Node21Domains0 root8Node21Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node21Step1Chunk0_0_checked, root8Node21Step1Chunk0_1_checked, root8Node21Step1Chunk0_2_checked, root8Node21Step1Chunk0_3_checked, root8Node21Step1Chunk0_4_checked, root8Node21Step1Chunk0_5_checked, root8Node21Step1Chunk1_0_checked, root8Node21Step1Chunk1_1_checked, root8Node21Step1Chunk1_2_checked, root8Node21Step1Chunk1_3_checked, root8Node21Step1Chunk1_4_checked, root8Node21Step1Chunk1_5_checked, root8Node21Step1Chunk2_0_checked, root8Node21Step1Chunk2_1_checked, root8Node21Step1Chunk2_2_checked, root8Node21Step1Chunk2_3_checked, root8Node21Step1Chunk2_4_checked, root8Node21Step1Chunk2_5_checked, root8Node21Step1Chunk3_0_checked, root8Node21Step1Chunk3_1_checked, root8Node21Step1Chunk3_2_checked, root8Node21Step1Chunk3_3_checked, root8Node21Step1Chunk3_4_checked, root8Node21Step1Chunk3_5_checked, root8Node21Step1Chunk4_0_checked, root8Node21Step1Chunk4_1_checked, root8Node21Step1Chunk4_2_checked, root8Node21Step1Chunk4_3_checked, root8Node21Step1Chunk4_4_checked, root8Node21Step1Chunk4_5_checked, root8Node21Step1Chunk5_0_checked, root8Node21Step1Chunk5_1_checked, root8Node21Step1Chunk5_2_checked, root8Node21Step1Chunk5_3_checked, root8Node21Step1Chunk5_4_checked, root8Node21Step1Chunk5_5_checked, root8Node21Step1Chunk6_0_checked, root8Node21Step1Chunk6_1_checked, root8Node21Step1Chunk6_2_checked, root8Node21Step1Chunk6_3_checked, root8Node21Step1Chunk6_4_checked, root8Node21Step1Chunk6_5_checked, root8Node21Step1Chunk7_0_checked, root8Node21Step1Chunk7_1_checked, root8Node21Step1Chunk7_2_checked, root8Node21Step1Chunk7_3_checked, root8Node21Step1Chunk7_4_checked, root8Node21Step1Chunk7_5_checked, root8Node21Step1Chunk8_0_checked, root8Node21Step1Chunk8_1_checked, root8Node21Step1Chunk8_2_checked, root8Node21Step1Chunk8_3_checked, root8Node21Step1Chunk8_4_checked, root8Node21Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node21Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node21Domains1 (.output 9) = true := by decide
def root8Node22Domains0 : Domains 61 State := restrict root8Node18Domains1 26 (3,2)
def root8Node22Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(3,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(1,5)]
  | 50 => some [(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,1),(5,4)]
  | 57 => some [(0,1),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root8Node22Domains0_fast_eq : root8Node22Domains0 = expandDomains root8Node22Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node22Domains0 v = expandDomains root8Node22Domains0Fast v from by decide) v
def root8Node23Domains0 : Domains 61 State := restrict root8Node22Domains0 50 (7,2)
def root8Node23Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(3,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(1,5)]
  | 50 => some [(7,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,1),(5,4)]
  | 57 => some [(0,1),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root8Node23Domains0_fast_eq : root8Node23Domains0 = expandDomains root8Node23Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node23Domains0 v = expandDomains root8Node23Domains0Fast v from by decide) v
def root8Node23Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(8,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(3,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(5,0)]
  | 34 => [(4,5)]
  | 35 => [(5,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(8,4)]
  | 42 => [(0,0)]
  | 43 => [(8,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(0,3)]
  | 48 => [(8,1)]
  | 49 => [(1,5)]
  | 50 => [(7,2)]
  | 51 => [(4,0)]
  | 52 => [(7,3)]
  | 53 => [(4,2)]
  | 54 => [(5,3)]
  | 55 => [(8,5)]
  | 56 => [(5,1)]
  | 57 => [(0,1)]
  | 58 => [(6,2)]
  | 59 => [(7,4)]
  | _ => [(6,3)]
def root8Node23Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(3,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(1,5)]
  | 50 => some [(7,2)]
  | 51 => some [(4,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root8Node23Domains1_fast_eq : root8Node23Domains1 = expandDomains root8Node23Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node23Domains1 v = expandDomains root8Node23Domains1Fast v from by decide) v
theorem root8Node23Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1_checked :
    checkReplacement table37 root8Node23Domains0 root8Node23Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node23Step1Chunk0_0_checked, root8Node23Step1Chunk0_1_checked, root8Node23Step1Chunk0_2_checked, root8Node23Step1Chunk0_3_checked, root8Node23Step1Chunk0_4_checked, root8Node23Step1Chunk0_5_checked, root8Node23Step1Chunk1_0_checked, root8Node23Step1Chunk1_1_checked, root8Node23Step1Chunk1_2_checked, root8Node23Step1Chunk1_3_checked, root8Node23Step1Chunk1_4_checked, root8Node23Step1Chunk1_5_checked, root8Node23Step1Chunk2_0_checked, root8Node23Step1Chunk2_1_checked, root8Node23Step1Chunk2_2_checked, root8Node23Step1Chunk2_3_checked, root8Node23Step1Chunk2_4_checked, root8Node23Step1Chunk2_5_checked, root8Node23Step1Chunk3_0_checked, root8Node23Step1Chunk3_1_checked, root8Node23Step1Chunk3_2_checked, root8Node23Step1Chunk3_3_checked, root8Node23Step1Chunk3_4_checked, root8Node23Step1Chunk3_5_checked, root8Node23Step1Chunk4_0_checked, root8Node23Step1Chunk4_1_checked, root8Node23Step1Chunk4_2_checked, root8Node23Step1Chunk4_3_checked, root8Node23Step1Chunk4_4_checked, root8Node23Step1Chunk4_5_checked, root8Node23Step1Chunk5_0_checked, root8Node23Step1Chunk5_1_checked, root8Node23Step1Chunk5_2_checked, root8Node23Step1Chunk5_3_checked, root8Node23Step1Chunk5_4_checked, root8Node23Step1Chunk5_5_checked, root8Node23Step1Chunk6_0_checked, root8Node23Step1Chunk6_1_checked, root8Node23Step1Chunk6_2_checked, root8Node23Step1Chunk6_3_checked, root8Node23Step1Chunk6_4_checked, root8Node23Step1Chunk6_5_checked, root8Node23Step1Chunk7_0_checked, root8Node23Step1Chunk7_1_checked, root8Node23Step1Chunk7_2_checked, root8Node23Step1Chunk7_3_checked, root8Node23Step1Chunk7_4_checked, root8Node23Step1Chunk7_5_checked, root8Node23Step1Chunk8_0_checked, root8Node23Step1Chunk8_1_checked, root8Node23Step1Chunk8_2_checked, root8Node23Step1Chunk8_3_checked, root8Node23Step1Chunk8_4_checked, root8Node23Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node23Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node23Domains1 (.output 10) = true := by decide
end SpectreFinite.HexSearch.RadiusFour
