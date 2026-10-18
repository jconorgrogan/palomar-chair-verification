module

public import SpectreFinite.RadiusFourRoot6Part14
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable36

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node50Domains0 : Domains 61 State := restrict root6Node49Domains2 11 (3,3)
def root6Node50Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(3,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(2,3)]
  | 18 => some [(0,1)]
  | 19 => some [(6,2)]
  | 20 => some [(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(4,5)]
  | 27 => some [(1,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2)]
  | 36 => some [(4,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(5,1)]
  | 44 => some [(0,1)]
  | 45 => some [(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(6,4)]
  | 48 => some [(1,2)]
  | 49 => some [(7,4)]
  | 50 => some [(8,5)]
  | 51 => some [(1,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(8,1)]
  | 56 => some [(7,2),(8,2)]
  | 57 => some [(4,0),(8,0)]
  | 58 => some [(7,3)]
  | 59 => some [(4,2)]
  | _ => some [(5,3)]
theorem root6Node50Domains0_fast_eq : root6Node50Domains0 = expandDomains root6Node50Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node50Domains0 v = expandDomains root6Node50Domains0Fast v from by decide) v
def root6Node51Domains0 : Domains 61 State := restrict root6Node50Domains0 56 (7,2)
def root6Node51Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(3,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(2,3)]
  | 18 => some [(0,1)]
  | 19 => some [(6,2)]
  | 20 => some [(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(4,5)]
  | 27 => some [(1,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2)]
  | 36 => some [(4,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(5,1)]
  | 44 => some [(0,1)]
  | 45 => some [(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(6,4)]
  | 48 => some [(1,2)]
  | 49 => some [(7,4)]
  | 50 => some [(8,5)]
  | 51 => some [(1,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(8,1)]
  | 56 => some [(7,2)]
  | 57 => some [(4,0),(8,0)]
  | 58 => some [(7,3)]
  | 59 => some [(4,2)]
  | _ => some [(5,3)]
theorem root6Node51Domains0_fast_eq : root6Node51Domains0 = expandDomains root6Node51Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node51Domains0 v = expandDomains root6Node51Domains0Fast v from by decide) v
def root6Node51Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,1)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(8,1)]
  | 9 => [(6,5)]
  | 10 => [(0,4)]
  | 11 => [(3,3)]
  | 12 => [(5,2)]
  | 13 => [(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(7,0)]
  | 17 => [(2,3)]
  | 18 => [(0,1)]
  | 19 => [(6,2)]
  | 20 => [(8,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(4,5)]
  | 27 => [(1,0)]
  | 28 => [(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(0,3)]
  | 34 => [(5,1)]
  | 35 => [(7,2)]
  | 36 => [(4,0)]
  | 37 => [(7,3)]
  | 38 => [(8,2)]
  | 39 => [(8,0)]
  | 40 => [(7,3)]
  | 41 => [(4,2)]
  | 42 => [(5,3)]
  | 43 => [(5,1)]
  | 44 => [(0,1)]
  | 45 => [(6,2)]
  | 46 => [(8,4)]
  | 47 => [(6,4)]
  | 48 => [(1,2)]
  | 49 => [(7,4)]
  | 50 => [(8,5)]
  | 51 => [(1,0)]
  | 52 => [(7,1)]
  | 53 => [(7,5)]
  | 54 => [(0,3)]
  | 55 => [(8,1)]
  | 56 => [(7,2)]
  | 57 => [(4,0)]
  | 58 => [(7,3)]
  | 59 => [(4,2)]
  | _ => [(5,3)]
def root6Node51Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(3,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(2,3)]
  | 18 => some [(0,1)]
  | 19 => some [(6,2)]
  | 20 => some [(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(4,5)]
  | 27 => some [(1,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2)]
  | 36 => some [(4,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(5,1)]
  | 44 => some [(0,1)]
  | 45 => some [(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(6,4)]
  | 48 => some [(1,2)]
  | 49 => some [(7,4)]
  | 50 => some [(8,5)]
  | 51 => some [(1,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(8,1)]
  | 56 => some [(7,2)]
  | 57 => some [(4,0)]
  | 58 => some [(7,3)]
  | 59 => some [(4,2)]
  | _ => some [(5,3)]
theorem root6Node51Domains1_fast_eq : root6Node51Domains1 = expandDomains root6Node51Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node51Domains1 v = expandDomains root6Node51Domains1Fast v from by decide) v
theorem root6Node51Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root6Node51Domains0 root6Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node51Domains0 root6Node51Domains1
    root6Node51Domains0Fast root6Node51Domains1Fast
    root6Node51Domains0_fast_eq root6Node51Domains1_fast_eq (by decide)
theorem root6Node51Step1_checked :
    checkReplacement table36 root6Node51Domains0 root6Node51Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node51Step1Chunk0_0_checked, root6Node51Step1Chunk0_1_checked, root6Node51Step1Chunk0_2_checked, root6Node51Step1Chunk0_3_checked, root6Node51Step1Chunk0_4_checked, root6Node51Step1Chunk0_5_checked, root6Node51Step1Chunk1_0_checked, root6Node51Step1Chunk1_1_checked, root6Node51Step1Chunk1_2_checked, root6Node51Step1Chunk1_3_checked, root6Node51Step1Chunk1_4_checked, root6Node51Step1Chunk1_5_checked, root6Node51Step1Chunk2_0_checked, root6Node51Step1Chunk2_1_checked, root6Node51Step1Chunk2_2_checked, root6Node51Step1Chunk2_3_checked, root6Node51Step1Chunk2_4_checked, root6Node51Step1Chunk2_5_checked, root6Node51Step1Chunk3_0_checked, root6Node51Step1Chunk3_1_checked, root6Node51Step1Chunk3_2_checked, root6Node51Step1Chunk3_3_checked, root6Node51Step1Chunk3_4_checked, root6Node51Step1Chunk3_5_checked, root6Node51Step1Chunk4_0_checked, root6Node51Step1Chunk4_1_checked, root6Node51Step1Chunk4_2_checked, root6Node51Step1Chunk4_3_checked, root6Node51Step1Chunk4_4_checked, root6Node51Step1Chunk4_5_checked, root6Node51Step1Chunk5_0_checked, root6Node51Step1Chunk5_1_checked, root6Node51Step1Chunk5_2_checked, root6Node51Step1Chunk5_3_checked, root6Node51Step1Chunk5_4_checked, root6Node51Step1Chunk5_5_checked, root6Node51Step1Chunk6_0_checked, root6Node51Step1Chunk6_1_checked, root6Node51Step1Chunk6_2_checked, root6Node51Step1Chunk6_3_checked, root6Node51Step1Chunk6_4_checked, root6Node51Step1Chunk6_5_checked, root6Node51Step1Chunk7_0_checked, root6Node51Step1Chunk7_1_checked, root6Node51Step1Chunk7_2_checked, root6Node51Step1Chunk7_3_checked, root6Node51Step1Chunk7_4_checked, root6Node51Step1Chunk7_5_checked, root6Node51Step1Chunk8_0_checked, root6Node51Step1Chunk8_1_checked, root6Node51Step1Chunk8_2_checked, root6Node51Step1Chunk8_3_checked, root6Node51Step1Chunk8_4_checked, root6Node51Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root6Node51Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node51Domains1 (.output 23) = true := by decide
def root6Node52Domains0 : Domains 61 State := restrict root6Node50Domains0 56 (8,2)
def root6Node52Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(3,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(2,3)]
  | 18 => some [(0,1)]
  | 19 => some [(6,2)]
  | 20 => some [(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(4,5)]
  | 27 => some [(1,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2)]
  | 36 => some [(4,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(5,1)]
  | 44 => some [(0,1)]
  | 45 => some [(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(6,4)]
  | 48 => some [(1,2)]
  | 49 => some [(7,4)]
  | 50 => some [(8,5)]
  | 51 => some [(1,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(8,1)]
  | 56 => some [(8,2)]
  | 57 => some [(4,0),(8,0)]
  | 58 => some [(7,3)]
  | 59 => some [(4,2)]
  | _ => some [(5,3)]
theorem root6Node52Domains0_fast_eq : root6Node52Domains0 = expandDomains root6Node52Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node52Domains0 v = expandDomains root6Node52Domains0Fast v from by decide) v
def root6Node52Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,1)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(8,1)]
  | 9 => [(6,5)]
  | 10 => [(0,4)]
  | 11 => [(3,3)]
  | 12 => [(5,2)]
  | 13 => [(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(7,0)]
  | 17 => [(2,3)]
  | 18 => [(0,1)]
  | 19 => [(6,2)]
  | 20 => [(8,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(4,5)]
  | 27 => [(1,0)]
  | 28 => [(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(0,3)]
  | 34 => [(5,1)]
  | 35 => [(7,2)]
  | 36 => [(4,0)]
  | 37 => [(7,3)]
  | 38 => [(8,2)]
  | 39 => [(8,0)]
  | 40 => [(7,3)]
  | 41 => [(4,2)]
  | 42 => [(5,3)]
  | 43 => [(5,1)]
  | 44 => [(0,1)]
  | 45 => [(6,2)]
  | 46 => [(8,4)]
  | 47 => [(6,4)]
  | 48 => [(1,2)]
  | 49 => [(7,4)]
  | 50 => [(8,5)]
  | 51 => [(1,0)]
  | 52 => [(7,1)]
  | 53 => [(7,5)]
  | 54 => [(0,3)]
  | 55 => [(8,1)]
  | 56 => [(8,2)]
  | 57 => [(8,0)]
  | 58 => [(7,3)]
  | 59 => [(4,2)]
  | _ => [(5,3)]
def root6Node52Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(3,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(2,3)]
  | 18 => some [(0,1)]
  | 19 => some [(6,2)]
  | 20 => some [(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(4,5)]
  | 27 => some [(1,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2)]
  | 36 => some [(4,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(5,1)]
  | 44 => some [(0,1)]
  | 45 => some [(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(6,4)]
  | 48 => some [(1,2)]
  | 49 => some [(7,4)]
  | 50 => some [(8,5)]
  | 51 => some [(1,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(8,1)]
  | 56 => some [(8,2)]
  | 57 => some [(8,0)]
  | 58 => some [(7,3)]
  | 59 => some [(4,2)]
  | _ => some [(5,3)]
theorem root6Node52Domains1_fast_eq : root6Node52Domains1 = expandDomains root6Node52Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node52Domains1 v = expandDomains root6Node52Domains1Fast v from by decide) v
theorem root6Node52Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root6Node52Domains0 root6Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node52Domains0 root6Node52Domains1
    root6Node52Domains0Fast root6Node52Domains1Fast
    root6Node52Domains0_fast_eq root6Node52Domains1_fast_eq (by decide)
theorem root6Node52Step1_checked :
    checkReplacement table36 root6Node52Domains0 root6Node52Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node52Step1Chunk0_0_checked, root6Node52Step1Chunk0_1_checked, root6Node52Step1Chunk0_2_checked, root6Node52Step1Chunk0_3_checked, root6Node52Step1Chunk0_4_checked, root6Node52Step1Chunk0_5_checked, root6Node52Step1Chunk1_0_checked, root6Node52Step1Chunk1_1_checked, root6Node52Step1Chunk1_2_checked, root6Node52Step1Chunk1_3_checked, root6Node52Step1Chunk1_4_checked, root6Node52Step1Chunk1_5_checked, root6Node52Step1Chunk2_0_checked, root6Node52Step1Chunk2_1_checked, root6Node52Step1Chunk2_2_checked, root6Node52Step1Chunk2_3_checked, root6Node52Step1Chunk2_4_checked, root6Node52Step1Chunk2_5_checked, root6Node52Step1Chunk3_0_checked, root6Node52Step1Chunk3_1_checked, root6Node52Step1Chunk3_2_checked, root6Node52Step1Chunk3_3_checked, root6Node52Step1Chunk3_4_checked, root6Node52Step1Chunk3_5_checked, root6Node52Step1Chunk4_0_checked, root6Node52Step1Chunk4_1_checked, root6Node52Step1Chunk4_2_checked, root6Node52Step1Chunk4_3_checked, root6Node52Step1Chunk4_4_checked, root6Node52Step1Chunk4_5_checked, root6Node52Step1Chunk5_0_checked, root6Node52Step1Chunk5_1_checked, root6Node52Step1Chunk5_2_checked, root6Node52Step1Chunk5_3_checked, root6Node52Step1Chunk5_4_checked, root6Node52Step1Chunk5_5_checked, root6Node52Step1Chunk6_0_checked, root6Node52Step1Chunk6_1_checked, root6Node52Step1Chunk6_2_checked, root6Node52Step1Chunk6_3_checked, root6Node52Step1Chunk6_4_checked, root6Node52Step1Chunk6_5_checked, root6Node52Step1Chunk7_0_checked, root6Node52Step1Chunk7_1_checked, root6Node52Step1Chunk7_2_checked, root6Node52Step1Chunk7_3_checked, root6Node52Step1Chunk7_4_checked, root6Node52Step1Chunk7_5_checked, root6Node52Step1Chunk8_0_checked, root6Node52Step1Chunk8_1_checked, root6Node52Step1Chunk8_2_checked, root6Node52Step1Chunk8_3_checked, root6Node52Step1Chunk8_4_checked, root6Node52Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root6Node52Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node52Domains1 (.output 24) = true := by decide
def root6Node53Domains0 : Domains 61 State := restrict root6Node49Domains2 11 (7,3)
def root6Node53Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(2,3)]
  | 18 => some [(0,1)]
  | 19 => some [(6,2)]
  | 20 => some [(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(4,5)]
  | 27 => some [(1,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2)]
  | 36 => some [(4,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(5,1)]
  | 44 => some [(0,1)]
  | 45 => some [(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(6,4)]
  | 48 => some [(1,2)]
  | 49 => some [(7,4)]
  | 50 => some [(8,5)]
  | 51 => some [(1,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(8,1)]
  | 56 => some [(7,2),(8,2)]
  | 57 => some [(4,0),(8,0)]
  | 58 => some [(7,3)]
  | 59 => some [(4,2)]
  | _ => some [(5,3)]
theorem root6Node53Domains0_fast_eq : root6Node53Domains0 = expandDomains root6Node53Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node53Domains0 v = expandDomains root6Node53Domains0Fast v from by decide) v
def root6Node54Domains0 : Domains 61 State := restrict root6Node53Domains0 56 (7,2)
def root6Node54Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(2,3)]
  | 18 => some [(0,1)]
  | 19 => some [(6,2)]
  | 20 => some [(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(4,5)]
  | 27 => some [(1,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2)]
  | 36 => some [(4,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(5,1)]
  | 44 => some [(0,1)]
  | 45 => some [(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(6,4)]
  | 48 => some [(1,2)]
  | 49 => some [(7,4)]
  | 50 => some [(8,5)]
  | 51 => some [(1,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(8,1)]
  | 56 => some [(7,2)]
  | 57 => some [(4,0),(8,0)]
  | 58 => some [(7,3)]
  | 59 => some [(4,2)]
  | _ => some [(5,3)]
theorem root6Node54Domains0_fast_eq : root6Node54Domains0 = expandDomains root6Node54Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node54Domains0 v = expandDomains root6Node54Domains0Fast v from by decide) v
def root6Node54Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,1)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(8,1)]
  | 9 => [(6,5)]
  | 10 => [(0,4)]
  | 11 => [(7,3)]
  | 12 => [(5,2)]
  | 13 => [(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(7,0)]
  | 17 => [(2,3)]
  | 18 => [(0,1)]
  | 19 => [(6,2)]
  | 20 => [(8,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(4,5)]
  | 27 => [(1,0)]
  | 28 => [(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(0,3)]
  | 34 => [(5,1)]
  | 35 => [(7,2)]
  | 36 => [(4,0)]
  | 37 => [(7,3)]
  | 38 => [(8,2)]
  | 39 => [(8,0)]
  | 40 => [(7,3)]
  | 41 => [(4,2)]
  | 42 => [(5,3)]
  | 43 => [(5,1)]
  | 44 => [(0,1)]
  | 45 => [(6,2)]
  | 46 => [(8,4)]
  | 47 => [(6,4)]
  | 48 => [(1,2)]
  | 49 => [(7,4)]
  | 50 => [(8,5)]
  | 51 => [(1,0)]
  | 52 => [(7,1)]
  | 53 => [(7,5)]
  | 54 => [(0,3)]
  | 55 => [(8,1)]
  | 56 => [(7,2)]
  | 57 => [(4,0)]
  | 58 => [(7,3)]
  | 59 => [(4,2)]
  | _ => [(5,3)]
def root6Node54Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(2,3)]
  | 18 => some [(0,1)]
  | 19 => some [(6,2)]
  | 20 => some [(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(4,5)]
  | 27 => some [(1,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2)]
  | 36 => some [(4,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(5,1)]
  | 44 => some [(0,1)]
  | 45 => some [(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(6,4)]
  | 48 => some [(1,2)]
  | 49 => some [(7,4)]
  | 50 => some [(8,5)]
  | 51 => some [(1,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(8,1)]
  | 56 => some [(7,2)]
  | 57 => some [(4,0)]
  | 58 => some [(7,3)]
  | 59 => some [(4,2)]
  | _ => some [(5,3)]
theorem root6Node54Domains1_fast_eq : root6Node54Domains1 = expandDomains root6Node54Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node54Domains1 v = expandDomains root6Node54Domains1Fast v from by decide) v
theorem root6Node54Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root6Node54Domains0 root6Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node54Domains0 root6Node54Domains1
    root6Node54Domains0Fast root6Node54Domains1Fast
    root6Node54Domains0_fast_eq root6Node54Domains1_fast_eq (by decide)
theorem root6Node54Step1_checked :
    checkReplacement table36 root6Node54Domains0 root6Node54Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node54Step1Chunk0_0_checked, root6Node54Step1Chunk0_1_checked, root6Node54Step1Chunk0_2_checked, root6Node54Step1Chunk0_3_checked, root6Node54Step1Chunk0_4_checked, root6Node54Step1Chunk0_5_checked, root6Node54Step1Chunk1_0_checked, root6Node54Step1Chunk1_1_checked, root6Node54Step1Chunk1_2_checked, root6Node54Step1Chunk1_3_checked, root6Node54Step1Chunk1_4_checked, root6Node54Step1Chunk1_5_checked, root6Node54Step1Chunk2_0_checked, root6Node54Step1Chunk2_1_checked, root6Node54Step1Chunk2_2_checked, root6Node54Step1Chunk2_3_checked, root6Node54Step1Chunk2_4_checked, root6Node54Step1Chunk2_5_checked, root6Node54Step1Chunk3_0_checked, root6Node54Step1Chunk3_1_checked, root6Node54Step1Chunk3_2_checked, root6Node54Step1Chunk3_3_checked, root6Node54Step1Chunk3_4_checked, root6Node54Step1Chunk3_5_checked, root6Node54Step1Chunk4_0_checked, root6Node54Step1Chunk4_1_checked, root6Node54Step1Chunk4_2_checked, root6Node54Step1Chunk4_3_checked, root6Node54Step1Chunk4_4_checked, root6Node54Step1Chunk4_5_checked, root6Node54Step1Chunk5_0_checked, root6Node54Step1Chunk5_1_checked, root6Node54Step1Chunk5_2_checked, root6Node54Step1Chunk5_3_checked, root6Node54Step1Chunk5_4_checked, root6Node54Step1Chunk5_5_checked, root6Node54Step1Chunk6_0_checked, root6Node54Step1Chunk6_1_checked, root6Node54Step1Chunk6_2_checked, root6Node54Step1Chunk6_3_checked, root6Node54Step1Chunk6_4_checked, root6Node54Step1Chunk6_5_checked, root6Node54Step1Chunk7_0_checked, root6Node54Step1Chunk7_1_checked, root6Node54Step1Chunk7_2_checked, root6Node54Step1Chunk7_3_checked, root6Node54Step1Chunk7_4_checked, root6Node54Step1Chunk7_5_checked, root6Node54Step1Chunk8_0_checked, root6Node54Step1Chunk8_1_checked, root6Node54Step1Chunk8_2_checked, root6Node54Step1Chunk8_3_checked, root6Node54Step1Chunk8_4_checked, root6Node54Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root6Node54Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node54Domains1 (.output 25) = true := by decide
end SpectreFinite.HexSearch.RadiusFour
