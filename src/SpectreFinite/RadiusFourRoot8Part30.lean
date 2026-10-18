module

public import SpectreFinite.RadiusFourRoot8Part29
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable37
public import SpectreFinite.RadiusFourTable40

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node99Domains0 : Domains 61 State := restrict root8Node98Domains1 25 (3,1)
def root8Node99Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(3,1)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(8,2)]
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
theorem root8Node99Domains0_fast_eq : root8Node99Domains0 = expandDomains root8Node99Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node99Domains0 v = expandDomains root8Node99Domains0Fast v from by decide) v
def root8Node100Domains0 : Domains 61 State := restrict root8Node99Domains0 50 (7,2)
def root8Node100Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(3,1)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(8,2)]
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
theorem root8Node100Domains0_fast_eq : root8Node100Domains0 = expandDomains root8Node100Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node100Domains0 v = expandDomains root8Node100Domains0Fast v from by decide) v
def root8Node100Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(5,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(4,4)]
  | 16 => [(1,4)]
  | 17 => [(0,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(3,1)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(8,2)]
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
def root8Node100Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(3,1)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(8,2)]
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
theorem root8Node100Domains1_fast_eq : root8Node100Domains1 = expandDomains root8Node100Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node100Domains1 v = expandDomains root8Node100Domains1Fast v from by decide) v
theorem root8Node100Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1_checked :
    checkReplacement table37 root8Node100Domains0 root8Node100Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node100Step1Chunk0_0_checked, root8Node100Step1Chunk0_1_checked, root8Node100Step1Chunk0_2_checked, root8Node100Step1Chunk0_3_checked, root8Node100Step1Chunk0_4_checked, root8Node100Step1Chunk0_5_checked, root8Node100Step1Chunk1_0_checked, root8Node100Step1Chunk1_1_checked, root8Node100Step1Chunk1_2_checked, root8Node100Step1Chunk1_3_checked, root8Node100Step1Chunk1_4_checked, root8Node100Step1Chunk1_5_checked, root8Node100Step1Chunk2_0_checked, root8Node100Step1Chunk2_1_checked, root8Node100Step1Chunk2_2_checked, root8Node100Step1Chunk2_3_checked, root8Node100Step1Chunk2_4_checked, root8Node100Step1Chunk2_5_checked, root8Node100Step1Chunk3_0_checked, root8Node100Step1Chunk3_1_checked, root8Node100Step1Chunk3_2_checked, root8Node100Step1Chunk3_3_checked, root8Node100Step1Chunk3_4_checked, root8Node100Step1Chunk3_5_checked, root8Node100Step1Chunk4_0_checked, root8Node100Step1Chunk4_1_checked, root8Node100Step1Chunk4_2_checked, root8Node100Step1Chunk4_3_checked, root8Node100Step1Chunk4_4_checked, root8Node100Step1Chunk4_5_checked, root8Node100Step1Chunk5_0_checked, root8Node100Step1Chunk5_1_checked, root8Node100Step1Chunk5_2_checked, root8Node100Step1Chunk5_3_checked, root8Node100Step1Chunk5_4_checked, root8Node100Step1Chunk5_5_checked, root8Node100Step1Chunk6_0_checked, root8Node100Step1Chunk6_1_checked, root8Node100Step1Chunk6_2_checked, root8Node100Step1Chunk6_3_checked, root8Node100Step1Chunk6_4_checked, root8Node100Step1Chunk6_5_checked, root8Node100Step1Chunk7_0_checked, root8Node100Step1Chunk7_1_checked, root8Node100Step1Chunk7_2_checked, root8Node100Step1Chunk7_3_checked, root8Node100Step1Chunk7_4_checked, root8Node100Step1Chunk7_5_checked, root8Node100Step1Chunk8_0_checked, root8Node100Step1Chunk8_1_checked, root8Node100Step1Chunk8_2_checked, root8Node100Step1Chunk8_3_checked, root8Node100Step1Chunk8_4_checked, root8Node100Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node100Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node100Domains1 (.output 49) = true := by decide
def root8Node101Domains0 : Domains 61 State := restrict root8Node99Domains0 50 (8,2)
def root8Node101Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(3,1)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(8,2)]
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
theorem root8Node101Domains0_fast_eq : root8Node101Domains0 = expandDomains root8Node101Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node101Domains0 v = expandDomains root8Node101Domains0Fast v from by decide) v
def root8Node101Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(5,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(4,4)]
  | 16 => [(1,4)]
  | 17 => [(0,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(3,1)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(8,2)]
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
def root8Node101Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(3,1)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(8,2)]
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
theorem root8Node101Domains1_fast_eq : root8Node101Domains1 = expandDomains root8Node101Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node101Domains1 v = expandDomains root8Node101Domains1Fast v from by decide) v
theorem root8Node101Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1_checked :
    checkReplacement table37 root8Node101Domains0 root8Node101Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node101Step1Chunk0_0_checked, root8Node101Step1Chunk0_1_checked, root8Node101Step1Chunk0_2_checked, root8Node101Step1Chunk0_3_checked, root8Node101Step1Chunk0_4_checked, root8Node101Step1Chunk0_5_checked, root8Node101Step1Chunk1_0_checked, root8Node101Step1Chunk1_1_checked, root8Node101Step1Chunk1_2_checked, root8Node101Step1Chunk1_3_checked, root8Node101Step1Chunk1_4_checked, root8Node101Step1Chunk1_5_checked, root8Node101Step1Chunk2_0_checked, root8Node101Step1Chunk2_1_checked, root8Node101Step1Chunk2_2_checked, root8Node101Step1Chunk2_3_checked, root8Node101Step1Chunk2_4_checked, root8Node101Step1Chunk2_5_checked, root8Node101Step1Chunk3_0_checked, root8Node101Step1Chunk3_1_checked, root8Node101Step1Chunk3_2_checked, root8Node101Step1Chunk3_3_checked, root8Node101Step1Chunk3_4_checked, root8Node101Step1Chunk3_5_checked, root8Node101Step1Chunk4_0_checked, root8Node101Step1Chunk4_1_checked, root8Node101Step1Chunk4_2_checked, root8Node101Step1Chunk4_3_checked, root8Node101Step1Chunk4_4_checked, root8Node101Step1Chunk4_5_checked, root8Node101Step1Chunk5_0_checked, root8Node101Step1Chunk5_1_checked, root8Node101Step1Chunk5_2_checked, root8Node101Step1Chunk5_3_checked, root8Node101Step1Chunk5_4_checked, root8Node101Step1Chunk5_5_checked, root8Node101Step1Chunk6_0_checked, root8Node101Step1Chunk6_1_checked, root8Node101Step1Chunk6_2_checked, root8Node101Step1Chunk6_3_checked, root8Node101Step1Chunk6_4_checked, root8Node101Step1Chunk6_5_checked, root8Node101Step1Chunk7_0_checked, root8Node101Step1Chunk7_1_checked, root8Node101Step1Chunk7_2_checked, root8Node101Step1Chunk7_3_checked, root8Node101Step1Chunk7_4_checked, root8Node101Step1Chunk7_5_checked, root8Node101Step1Chunk8_0_checked, root8Node101Step1Chunk8_1_checked, root8Node101Step1Chunk8_2_checked, root8Node101Step1Chunk8_3_checked, root8Node101Step1Chunk8_4_checked, root8Node101Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node101Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node101Domains1 (.output 50) = true := by decide
def root8Node102Domains0 : Domains 61 State := restrict root8Node98Domains1 25 (7,1)
def root8Node102Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(8,2)]
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
theorem root8Node102Domains0_fast_eq : root8Node102Domains0 = expandDomains root8Node102Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node102Domains0 v = expandDomains root8Node102Domains0Fast v from by decide) v
def root8Node102Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(5,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(4,4)]
  | 16 => [(1,4)]
  | 17 => [(0,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(7,1)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(8,2)]
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
  | 50 => [(7,2),(8,2)]
  | 51 => [(4,0),(8,0)]
  | 52 => [(7,3)]
  | 53 => [(4,2)]
  | 54 => [(5,3)]
  | 55 => [(8,5)]
  | 56 => [(5,1),(5,4)]
  | 57 => [(0,1),(6,4)]
  | 58 => [(6,2)]
  | 59 => [(7,4)]
  | _ => [(6,3)]
def root8Node102Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(8,2)]
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
  | 58 => some [(6,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root8Node102Domains1_fast_eq : root8Node102Domains1 = expandDomains root8Node102Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node102Domains1 v = expandDomains root8Node102Domains1Fast v from by decide) v
theorem root8Node102Step1Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root8Node102Domains0 root8Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains0 root8Node102Domains1
    root8Node102Domains0Fast root8Node102Domains1Fast
    root8Node102Domains0_fast_eq root8Node102Domains1_fast_eq (by decide)
theorem root8Node102Step1_checked :
    checkReplacement table40 root8Node102Domains0 root8Node102Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node102Step1Chunk0_0_checked, root8Node102Step1Chunk0_1_checked, root8Node102Step1Chunk0_2_checked, root8Node102Step1Chunk0_3_checked, root8Node102Step1Chunk0_4_checked, root8Node102Step1Chunk0_5_checked, root8Node102Step1Chunk1_0_checked, root8Node102Step1Chunk1_1_checked, root8Node102Step1Chunk1_2_checked, root8Node102Step1Chunk1_3_checked, root8Node102Step1Chunk1_4_checked, root8Node102Step1Chunk1_5_checked, root8Node102Step1Chunk2_0_checked, root8Node102Step1Chunk2_1_checked, root8Node102Step1Chunk2_2_checked, root8Node102Step1Chunk2_3_checked, root8Node102Step1Chunk2_4_checked, root8Node102Step1Chunk2_5_checked, root8Node102Step1Chunk3_0_checked, root8Node102Step1Chunk3_1_checked, root8Node102Step1Chunk3_2_checked, root8Node102Step1Chunk3_3_checked, root8Node102Step1Chunk3_4_checked, root8Node102Step1Chunk3_5_checked, root8Node102Step1Chunk4_0_checked, root8Node102Step1Chunk4_1_checked, root8Node102Step1Chunk4_2_checked, root8Node102Step1Chunk4_3_checked, root8Node102Step1Chunk4_4_checked, root8Node102Step1Chunk4_5_checked, root8Node102Step1Chunk5_0_checked, root8Node102Step1Chunk5_1_checked, root8Node102Step1Chunk5_2_checked, root8Node102Step1Chunk5_3_checked, root8Node102Step1Chunk5_4_checked, root8Node102Step1Chunk5_5_checked, root8Node102Step1Chunk6_0_checked, root8Node102Step1Chunk6_1_checked, root8Node102Step1Chunk6_2_checked, root8Node102Step1Chunk6_3_checked, root8Node102Step1Chunk6_4_checked, root8Node102Step1Chunk6_5_checked, root8Node102Step1Chunk7_0_checked, root8Node102Step1Chunk7_1_checked, root8Node102Step1Chunk7_2_checked, root8Node102Step1Chunk7_3_checked, root8Node102Step1Chunk7_4_checked, root8Node102Step1Chunk7_5_checked, root8Node102Step1Chunk8_0_checked, root8Node102Step1Chunk8_1_checked, root8Node102Step1Chunk8_2_checked, root8Node102Step1Chunk8_3_checked, root8Node102Step1Chunk8_4_checked, root8Node102Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node102Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(5,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(4,4)]
  | 16 => [(1,4)]
  | 17 => [(0,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(7,1)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(8,2)]
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
def root8Node102Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(8,2)]
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
theorem root8Node102Domains2_fast_eq : root8Node102Domains2 = expandDomains root8Node102Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node102Domains2 v = expandDomains root8Node102Domains2Fast v from by decide) v
theorem root8Node102Step2Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root8Node102Domains1 root8Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node102Domains1 root8Node102Domains2
    root8Node102Domains1Fast root8Node102Domains2Fast
    root8Node102Domains1_fast_eq root8Node102Domains2_fast_eq (by decide)
theorem root8Node102Step2_checked :
    checkReplacement table37 root8Node102Domains1 root8Node102Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node102Step2Chunk0_0_checked, root8Node102Step2Chunk0_1_checked, root8Node102Step2Chunk0_2_checked, root8Node102Step2Chunk0_3_checked, root8Node102Step2Chunk0_4_checked, root8Node102Step2Chunk0_5_checked, root8Node102Step2Chunk1_0_checked, root8Node102Step2Chunk1_1_checked, root8Node102Step2Chunk1_2_checked, root8Node102Step2Chunk1_3_checked, root8Node102Step2Chunk1_4_checked, root8Node102Step2Chunk1_5_checked, root8Node102Step2Chunk2_0_checked, root8Node102Step2Chunk2_1_checked, root8Node102Step2Chunk2_2_checked, root8Node102Step2Chunk2_3_checked, root8Node102Step2Chunk2_4_checked, root8Node102Step2Chunk2_5_checked, root8Node102Step2Chunk3_0_checked, root8Node102Step2Chunk3_1_checked, root8Node102Step2Chunk3_2_checked, root8Node102Step2Chunk3_3_checked, root8Node102Step2Chunk3_4_checked, root8Node102Step2Chunk3_5_checked, root8Node102Step2Chunk4_0_checked, root8Node102Step2Chunk4_1_checked, root8Node102Step2Chunk4_2_checked, root8Node102Step2Chunk4_3_checked, root8Node102Step2Chunk4_4_checked, root8Node102Step2Chunk4_5_checked, root8Node102Step2Chunk5_0_checked, root8Node102Step2Chunk5_1_checked, root8Node102Step2Chunk5_2_checked, root8Node102Step2Chunk5_3_checked, root8Node102Step2Chunk5_4_checked, root8Node102Step2Chunk5_5_checked, root8Node102Step2Chunk6_0_checked, root8Node102Step2Chunk6_1_checked, root8Node102Step2Chunk6_2_checked, root8Node102Step2Chunk6_3_checked, root8Node102Step2Chunk6_4_checked, root8Node102Step2Chunk6_5_checked, root8Node102Step2Chunk7_0_checked, root8Node102Step2Chunk7_1_checked, root8Node102Step2Chunk7_2_checked, root8Node102Step2Chunk7_3_checked, root8Node102Step2Chunk7_4_checked, root8Node102Step2Chunk7_5_checked, root8Node102Step2Chunk8_0_checked, root8Node102Step2Chunk8_1_checked, root8Node102Step2Chunk8_2_checked, root8Node102Step2Chunk8_3_checked, root8Node102Step2Chunk8_4_checked, root8Node102Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node102Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node102Domains2 (.output 51) = true := by decide
end SpectreFinite.HexSearch.RadiusFour
