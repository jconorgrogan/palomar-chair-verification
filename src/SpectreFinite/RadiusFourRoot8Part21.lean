module

public import SpectreFinite.RadiusFourRoot8Part20
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable4
public import SpectreFinite.RadiusFourTable46
public import SpectreFinite.RadiusFourTable5
public import SpectreFinite.RadiusFourTable7

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node66Domains0 : Domains 61 State := restrict root8Node65Domains0 43 (5,5)
def root8Node66Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(8,2)]
  | 9 => some [(8,0)]
  | 10 => some [(7,3)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3)]
  | 25 => some [(8,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2)]
  | 33 => some [(5,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(3,5),(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4),(7,2)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(6,3)]
  | 53 => some [(2,2),(2,4)]
  | 54 => some [(1,3),(3,3)]
  | 55 => some [(5,2)]
  | 56 => some [(4,1),(7,5)]
  | 57 => some [(0,2),(6,0)]
  | 58 => some [(1,1),(7,1)]
  | 59 => some [(0,1),(6,5)]
  | _ => some [(0,4),(6,2)]
theorem root8Node66Domains0_fast_eq : root8Node66Domains0 = expandDomains root8Node66Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node66Domains0 v = expandDomains root8Node66Domains0Fast v from by decide) v
def root8Node66Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(6,0)]
  | 4 => [(7,1)]
  | 5 => [(7,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(8,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3)]
  | 11 => [(6,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(6,4)]
  | 17 => [(1,2)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3)]
  | 25 => [(8,1)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2)]
  | 33 => [(5,3)]
  | 34 => [(8,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(7,4)]
  | 42 => [(6,3)]
  | 43 => [(5,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(3,5)]
  | 47 => [(0,3)]
  | 48 => [(4,1)]
  | 49 => [(0,2)]
  | 50 => [(4,4)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(2,4)]
  | 54 => [(1,3)]
  | 55 => [(5,2)]
  | 56 => [(7,5)]
  | 57 => [(6,0)]
  | 58 => [(7,1)]
  | 59 => [(6,5)]
  | _ => [(0,4)]
def root8Node66Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(8,2)]
  | 9 => some [(8,0)]
  | 10 => some [(7,3)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3)]
  | 25 => some [(8,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2)]
  | 33 => some [(5,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(3,5)]
  | 47 => some [(0,3)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(2,4)]
  | 54 => some [(1,3)]
  | 55 => some [(5,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(7,1)]
  | 59 => some [(6,5)]
  | _ => some [(0,4)]
theorem root8Node66Domains1_fast_eq : root8Node66Domains1 = expandDomains root8Node66Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node66Domains1 v = expandDomains root8Node66Domains1Fast v from by decide) v
theorem root8Node66Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root8Node66Domains0 root8Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node66Domains0 root8Node66Domains1
    root8Node66Domains0Fast root8Node66Domains1Fast
    root8Node66Domains0_fast_eq root8Node66Domains1_fast_eq (by decide)
theorem root8Node66Step1_checked :
    checkReplacement table46 root8Node66Domains0 root8Node66Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node66Step1Chunk0_0_checked, root8Node66Step1Chunk0_1_checked, root8Node66Step1Chunk0_2_checked, root8Node66Step1Chunk0_3_checked, root8Node66Step1Chunk0_4_checked, root8Node66Step1Chunk0_5_checked, root8Node66Step1Chunk1_0_checked, root8Node66Step1Chunk1_1_checked, root8Node66Step1Chunk1_2_checked, root8Node66Step1Chunk1_3_checked, root8Node66Step1Chunk1_4_checked, root8Node66Step1Chunk1_5_checked, root8Node66Step1Chunk2_0_checked, root8Node66Step1Chunk2_1_checked, root8Node66Step1Chunk2_2_checked, root8Node66Step1Chunk2_3_checked, root8Node66Step1Chunk2_4_checked, root8Node66Step1Chunk2_5_checked, root8Node66Step1Chunk3_0_checked, root8Node66Step1Chunk3_1_checked, root8Node66Step1Chunk3_2_checked, root8Node66Step1Chunk3_3_checked, root8Node66Step1Chunk3_4_checked, root8Node66Step1Chunk3_5_checked, root8Node66Step1Chunk4_0_checked, root8Node66Step1Chunk4_1_checked, root8Node66Step1Chunk4_2_checked, root8Node66Step1Chunk4_3_checked, root8Node66Step1Chunk4_4_checked, root8Node66Step1Chunk4_5_checked, root8Node66Step1Chunk5_0_checked, root8Node66Step1Chunk5_1_checked, root8Node66Step1Chunk5_2_checked, root8Node66Step1Chunk5_3_checked, root8Node66Step1Chunk5_4_checked, root8Node66Step1Chunk5_5_checked, root8Node66Step1Chunk6_0_checked, root8Node66Step1Chunk6_1_checked, root8Node66Step1Chunk6_2_checked, root8Node66Step1Chunk6_3_checked, root8Node66Step1Chunk6_4_checked, root8Node66Step1Chunk6_5_checked, root8Node66Step1Chunk7_0_checked, root8Node66Step1Chunk7_1_checked, root8Node66Step1Chunk7_2_checked, root8Node66Step1Chunk7_3_checked, root8Node66Step1Chunk7_4_checked, root8Node66Step1Chunk7_5_checked, root8Node66Step1Chunk8_0_checked, root8Node66Step1Chunk8_1_checked, root8Node66Step1Chunk8_2_checked, root8Node66Step1Chunk8_3_checked, root8Node66Step1Chunk8_4_checked, root8Node66Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node66Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node66Domains1 (.output 32) = true := by decide
def root8Node67Domains0 : Domains 61 State := restrict root8Node65Domains0 43 (8,5)
def root8Node67Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(8,2)]
  | 9 => some [(8,0)]
  | 10 => some [(7,3)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3)]
  | 25 => some [(8,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2)]
  | 33 => some [(5,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(3,5),(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4),(7,2)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(6,3)]
  | 53 => some [(2,2),(2,4)]
  | 54 => some [(1,3),(3,3)]
  | 55 => some [(5,2)]
  | 56 => some [(4,1),(7,5)]
  | 57 => some [(0,2),(6,0)]
  | 58 => some [(1,1),(7,1)]
  | 59 => some [(0,1),(6,5)]
  | _ => some [(0,4),(6,2)]
theorem root8Node67Domains0_fast_eq : root8Node67Domains0 = expandDomains root8Node67Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node67Domains0 v = expandDomains root8Node67Domains0Fast v from by decide) v
def root8Node67Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(6,0)]
  | 4 => [(7,1)]
  | 5 => [(7,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(8,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3)]
  | 11 => [(6,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(6,4)]
  | 17 => [(1,2)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3)]
  | 25 => [(8,1)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2)]
  | 33 => [(5,3)]
  | 34 => [(8,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(7,4)]
  | 42 => [(6,3)]
  | 43 => [(8,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(7,5)]
  | 47 => [(0,3)]
  | 48 => [(4,1)]
  | 49 => [(0,2)]
  | 50 => [(7,2)]
  | 51 => [(7,4)]
  | 52 => [(6,3)]
  | 53 => [(2,2)]
  | 54 => [(3,3)]
  | 55 => [(5,2)]
  | 56 => [(4,1)]
  | 57 => [(0,2)]
  | 58 => [(1,1)]
  | 59 => [(0,1)]
  | _ => [(6,2)]
def root8Node67Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(8,2)]
  | 9 => some [(8,0)]
  | 10 => some [(7,3)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3)]
  | 25 => some [(8,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2)]
  | 33 => some [(5,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(6,3)]
  | 53 => some [(2,2)]
  | 54 => some [(3,3)]
  | 55 => some [(5,2)]
  | 56 => some [(4,1)]
  | 57 => some [(0,2)]
  | 58 => some [(1,1)]
  | 59 => some [(0,1)]
  | _ => some [(6,2)]
theorem root8Node67Domains1_fast_eq : root8Node67Domains1 = expandDomains root8Node67Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node67Domains1 v = expandDomains root8Node67Domains1Fast v from by decide) v
theorem root8Node67Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root8Node67Domains0 root8Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node67Domains0 root8Node67Domains1
    root8Node67Domains0Fast root8Node67Domains1Fast
    root8Node67Domains0_fast_eq root8Node67Domains1_fast_eq (by decide)
theorem root8Node67Step1_checked :
    checkReplacement table46 root8Node67Domains0 root8Node67Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node67Step1Chunk0_0_checked, root8Node67Step1Chunk0_1_checked, root8Node67Step1Chunk0_2_checked, root8Node67Step1Chunk0_3_checked, root8Node67Step1Chunk0_4_checked, root8Node67Step1Chunk0_5_checked, root8Node67Step1Chunk1_0_checked, root8Node67Step1Chunk1_1_checked, root8Node67Step1Chunk1_2_checked, root8Node67Step1Chunk1_3_checked, root8Node67Step1Chunk1_4_checked, root8Node67Step1Chunk1_5_checked, root8Node67Step1Chunk2_0_checked, root8Node67Step1Chunk2_1_checked, root8Node67Step1Chunk2_2_checked, root8Node67Step1Chunk2_3_checked, root8Node67Step1Chunk2_4_checked, root8Node67Step1Chunk2_5_checked, root8Node67Step1Chunk3_0_checked, root8Node67Step1Chunk3_1_checked, root8Node67Step1Chunk3_2_checked, root8Node67Step1Chunk3_3_checked, root8Node67Step1Chunk3_4_checked, root8Node67Step1Chunk3_5_checked, root8Node67Step1Chunk4_0_checked, root8Node67Step1Chunk4_1_checked, root8Node67Step1Chunk4_2_checked, root8Node67Step1Chunk4_3_checked, root8Node67Step1Chunk4_4_checked, root8Node67Step1Chunk4_5_checked, root8Node67Step1Chunk5_0_checked, root8Node67Step1Chunk5_1_checked, root8Node67Step1Chunk5_2_checked, root8Node67Step1Chunk5_3_checked, root8Node67Step1Chunk5_4_checked, root8Node67Step1Chunk5_5_checked, root8Node67Step1Chunk6_0_checked, root8Node67Step1Chunk6_1_checked, root8Node67Step1Chunk6_2_checked, root8Node67Step1Chunk6_3_checked, root8Node67Step1Chunk6_4_checked, root8Node67Step1Chunk6_5_checked, root8Node67Step1Chunk7_0_checked, root8Node67Step1Chunk7_1_checked, root8Node67Step1Chunk7_2_checked, root8Node67Step1Chunk7_3_checked, root8Node67Step1Chunk7_4_checked, root8Node67Step1Chunk7_5_checked, root8Node67Step1Chunk8_0_checked, root8Node67Step1Chunk8_1_checked, root8Node67Step1Chunk8_2_checked, root8Node67Step1Chunk8_3_checked, root8Node67Step1Chunk8_4_checked, root8Node67Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node67Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node67Domains1 (.output 33) = true := by decide
def root8Node68Domains0 : Domains 61 State := restrict root8Node46Domains4 7 (8,3)
def root8Node68Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0)]
  | 1 => some [(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(7,5),(8,1)]
  | 3 => some [(0,2),(6,0),(6,5)]
  | 4 => some [(0,4),(1,1),(7,1)]
  | 5 => some [(1,2),(3,2),(5,2),(5,5),(7,2)]
  | 6 => some [(4,0),(7,0),(8,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,2),(5,5),(8,2)]
  | 9 => some [(7,0),(8,0)]
  | 10 => some [(2,3),(4,3),(7,3),(8,3)]
  | 11 => some [(0,3),(0,4),(0,5),(6,1),(6,2)]
  | 12 => some [(4,4),(5,1),(5,4),(8,4)]
  | 13 => some [(0,1),(1,4)]
  | 14 => some [(0,5),(6,2)]
  | 15 => some [(4,4),(8,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2)]
  | 18 => some [(1,0),(4,2),(6,0),(7,0)]
  | 19 => some [(4,3),(5,3),(7,1),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(1,0),(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(3,1),(5,1),(7,1),(8,1)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(8,5)]
  | 35 => some [(5,1),(8,1)]
  | 36 => some [(0,1),(6,5)]
  | 37 => some [(0,4),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(1,3),(6,3)]
  | 43 => some [(5,5),(8,5)]
  | 44 => some [(1,0),(7,0)]
  | 45 => some [(4,3),(7,1)]
  | 46 => some [(3,5),(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(4,1),(8,1)]
  | 49 => some [(0,2),(1,5),(6,5)]
  | 50 => some [(4,4),(7,2),(8,2)]
  | 51 => some [(1,4),(4,0),(7,4),(8,0)]
  | 52 => some [(0,5),(1,3),(6,3),(7,3)]
  | 53 => some [(2,2),(2,4),(4,2)]
  | 54 => some [(1,3),(3,3),(5,3)]
  | 55 => some [(5,2),(5,5),(8,5)]
  | 56 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 57 => some [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 58 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 59 => some [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => some [(0,4),(0,5),(6,2),(6,3)]
theorem root8Node68Domains0_fast_eq : root8Node68Domains0 = expandDomains root8Node68Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node68Domains0 v = expandDomains root8Node68Domains0Fast v from by decide) v
def root8Node68Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,5)]
  | 1 => [(1,1),(6,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(5,2),(5,5)]
  | 6 => [(7,0),(8,0)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(2,3),(4,3)]
  | 11 => [(0,4),(0,5),(6,2)]
  | 12 => [(4,4),(5,4),(8,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(4,4)]
  | 16 => [(1,4),(6,4)]
  | 17 => [(0,5),(1,2)]
  | 18 => [(1,0),(4,2),(6,0),(7,0)]
  | 19 => [(4,3),(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3),(6,0)]
  | 25 => [(3,1),(5,1),(7,1),(8,1)]
  | 26 => [(1,2),(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(1,3),(7,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2),(8,2)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5),(8,5)]
  | 35 => [(5,1),(8,1)]
  | 36 => [(0,1),(6,5)]
  | 37 => [(0,4),(6,2)]
  | 38 => [(5,4),(8,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(7,4),(8,4)]
  | 42 => [(0,0),(1,3),(6,3)]
  | 43 => [(5,5),(8,5)]
  | 44 => [(1,0),(7,0)]
  | 45 => [(4,3),(7,1)]
  | 46 => [(3,5),(7,5)]
  | 47 => [(0,3)]
  | 48 => [(4,1),(8,1)]
  | 49 => [(0,2),(1,5),(6,5)]
  | 50 => [(4,4),(7,2),(8,2)]
  | 51 => [(1,4),(4,0),(7,4),(8,0)]
  | 52 => [(0,5),(1,3),(6,3),(7,3)]
  | 53 => [(2,2),(2,4),(4,2)]
  | 54 => [(1,3),(3,3),(5,3)]
  | 55 => [(5,2),(5,5),(8,5)]
  | 56 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 57 => [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 58 => [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 59 => [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => [(0,4),(0,5),(6,2),(6,3)]
def root8Node68Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5)]
  | 1 => some [(1,1),(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,2),(5,5)]
  | 6 => some [(7,0),(8,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(2,3),(4,3)]
  | 11 => some [(0,4),(0,5),(6,2)]
  | 12 => some [(4,4),(5,4),(8,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2)]
  | 18 => some [(1,0),(4,2),(6,0),(7,0)]
  | 19 => some [(4,3),(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(3,1),(5,1),(7,1),(8,1)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(8,5)]
  | 35 => some [(5,1),(8,1)]
  | 36 => some [(0,1),(6,5)]
  | 37 => some [(0,4),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(1,3),(6,3)]
  | 43 => some [(5,5),(8,5)]
  | 44 => some [(1,0),(7,0)]
  | 45 => some [(4,3),(7,1)]
  | 46 => some [(3,5),(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(4,1),(8,1)]
  | 49 => some [(0,2),(1,5),(6,5)]
  | 50 => some [(4,4),(7,2),(8,2)]
  | 51 => some [(1,4),(4,0),(7,4),(8,0)]
  | 52 => some [(0,5),(1,3),(6,3),(7,3)]
  | 53 => some [(2,2),(2,4),(4,2)]
  | 54 => some [(1,3),(3,3),(5,3)]
  | 55 => some [(5,2),(5,5),(8,5)]
  | 56 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 57 => some [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 58 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 59 => some [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => some [(0,4),(0,5),(6,2),(6,3)]
theorem root8Node68Domains1_fast_eq : root8Node68Domains1 = expandDomains root8Node68Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node68Domains1 v = expandDomains root8Node68Domains1Fast v from by decide) v
theorem root8Node68Step1Chunk0_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows0_0⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk0_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows0_1⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk0_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows0_2⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk0_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows0_3⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk0_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows0_4⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk0_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows0_5⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk1_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows1_0⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk1_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows1_1⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk1_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows1_2⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk1_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows1_3⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk1_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows1_4⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk1_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows1_5⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk2_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows2_0⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk2_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows2_1⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk2_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows2_2⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk2_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows2_3⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk2_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows2_4⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk2_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows2_5⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk3_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows3_0⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk3_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows3_1⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk3_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows3_2⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk3_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows3_3⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk3_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows3_4⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk3_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows3_5⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk4_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows4_0⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk4_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows4_1⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk4_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows4_2⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk4_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows4_3⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk4_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows4_4⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk4_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows4_5⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk5_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows5_0⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk5_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows5_1⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk5_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows5_2⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk5_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows5_3⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk5_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows5_4⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk5_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows5_5⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk6_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows6_0⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk6_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows6_1⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk6_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows6_2⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk6_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows6_3⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk6_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows6_4⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk6_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows6_5⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk7_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows7_0⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk7_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows7_1⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk7_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows7_2⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk7_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows7_3⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk7_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows7_4⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk7_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows7_5⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk8_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows8_0⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk8_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows8_1⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk8_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows8_2⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk8_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows8_3⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk8_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows8_4⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1Chunk8_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows8_5⟩
      root8Node68Domains0 root8Node68Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains0 root8Node68Domains1
    root8Node68Domains0Fast root8Node68Domains1Fast
    root8Node68Domains0_fast_eq root8Node68Domains1_fast_eq (by decide)
theorem root8Node68Step1_checked :
    checkReplacement table7 root8Node68Domains0 root8Node68Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node68Step1Chunk0_0_checked, root8Node68Step1Chunk0_1_checked, root8Node68Step1Chunk0_2_checked, root8Node68Step1Chunk0_3_checked, root8Node68Step1Chunk0_4_checked, root8Node68Step1Chunk0_5_checked, root8Node68Step1Chunk1_0_checked, root8Node68Step1Chunk1_1_checked, root8Node68Step1Chunk1_2_checked, root8Node68Step1Chunk1_3_checked, root8Node68Step1Chunk1_4_checked, root8Node68Step1Chunk1_5_checked, root8Node68Step1Chunk2_0_checked, root8Node68Step1Chunk2_1_checked, root8Node68Step1Chunk2_2_checked, root8Node68Step1Chunk2_3_checked, root8Node68Step1Chunk2_4_checked, root8Node68Step1Chunk2_5_checked, root8Node68Step1Chunk3_0_checked, root8Node68Step1Chunk3_1_checked, root8Node68Step1Chunk3_2_checked, root8Node68Step1Chunk3_3_checked, root8Node68Step1Chunk3_4_checked, root8Node68Step1Chunk3_5_checked, root8Node68Step1Chunk4_0_checked, root8Node68Step1Chunk4_1_checked, root8Node68Step1Chunk4_2_checked, root8Node68Step1Chunk4_3_checked, root8Node68Step1Chunk4_4_checked, root8Node68Step1Chunk4_5_checked, root8Node68Step1Chunk5_0_checked, root8Node68Step1Chunk5_1_checked, root8Node68Step1Chunk5_2_checked, root8Node68Step1Chunk5_3_checked, root8Node68Step1Chunk5_4_checked, root8Node68Step1Chunk5_5_checked, root8Node68Step1Chunk6_0_checked, root8Node68Step1Chunk6_1_checked, root8Node68Step1Chunk6_2_checked, root8Node68Step1Chunk6_3_checked, root8Node68Step1Chunk6_4_checked, root8Node68Step1Chunk6_5_checked, root8Node68Step1Chunk7_0_checked, root8Node68Step1Chunk7_1_checked, root8Node68Step1Chunk7_2_checked, root8Node68Step1Chunk7_3_checked, root8Node68Step1Chunk7_4_checked, root8Node68Step1Chunk7_5_checked, root8Node68Step1Chunk8_0_checked, root8Node68Step1Chunk8_1_checked, root8Node68Step1Chunk8_2_checked, root8Node68Step1Chunk8_3_checked, root8Node68Step1Chunk8_4_checked, root8Node68Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node68Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,5)]
  | 1 => [(1,1),(6,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(5,2),(5,5)]
  | 6 => [(7,0),(8,0)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(2,3),(4,3)]
  | 11 => [(0,4),(0,5),(6,2)]
  | 12 => [(4,4),(5,4),(8,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(4,4)]
  | 16 => [(1,4),(6,4)]
  | 17 => [(0,5),(1,2)]
  | 18 => [(1,0),(6,0),(7,0)]
  | 19 => [(4,3),(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3),(6,0)]
  | 25 => [(3,1),(5,1),(7,1),(8,1)]
  | 26 => [(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(1,3),(7,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2),(8,2)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5),(8,5)]
  | 35 => [(5,1),(8,1)]
  | 36 => [(0,1),(6,5)]
  | 37 => [(0,4),(6,2)]
  | 38 => [(5,4),(8,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(7,4),(8,4)]
  | 42 => [(0,0),(1,3),(6,3)]
  | 43 => [(5,5),(8,5)]
  | 44 => [(1,0),(7,0)]
  | 45 => [(4,3),(7,1)]
  | 46 => [(3,5),(7,5)]
  | 47 => [(0,3)]
  | 48 => [(4,1),(8,1)]
  | 49 => [(0,2),(1,5),(6,5)]
  | 50 => [(4,4),(7,2),(8,2)]
  | 51 => [(1,4),(4,0),(7,4),(8,0)]
  | 52 => [(0,5),(1,3),(6,3),(7,3)]
  | 53 => [(2,2),(2,4),(4,2)]
  | 54 => [(1,3),(3,3),(5,3)]
  | 55 => [(5,2),(5,5),(8,5)]
  | 56 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 57 => [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 58 => [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 59 => [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => [(0,4),(0,5),(6,2),(6,3)]
def root8Node68Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5)]
  | 1 => some [(1,1),(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,2),(5,5)]
  | 6 => some [(7,0),(8,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(2,3),(4,3)]
  | 11 => some [(0,4),(0,5),(6,2)]
  | 12 => some [(4,4),(5,4),(8,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2)]
  | 18 => some [(1,0),(6,0),(7,0)]
  | 19 => some [(4,3),(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(3,1),(5,1),(7,1),(8,1)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(8,5)]
  | 35 => some [(5,1),(8,1)]
  | 36 => some [(0,1),(6,5)]
  | 37 => some [(0,4),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(1,3),(6,3)]
  | 43 => some [(5,5),(8,5)]
  | 44 => some [(1,0),(7,0)]
  | 45 => some [(4,3),(7,1)]
  | 46 => some [(3,5),(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(4,1),(8,1)]
  | 49 => some [(0,2),(1,5),(6,5)]
  | 50 => some [(4,4),(7,2),(8,2)]
  | 51 => some [(1,4),(4,0),(7,4),(8,0)]
  | 52 => some [(0,5),(1,3),(6,3),(7,3)]
  | 53 => some [(2,2),(2,4),(4,2)]
  | 54 => some [(1,3),(3,3),(5,3)]
  | 55 => some [(5,2),(5,5),(8,5)]
  | 56 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 57 => some [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 58 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 59 => some [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => some [(0,4),(0,5),(6,2),(6,3)]
theorem root8Node68Domains2_fast_eq : root8Node68Domains2 = expandDomains root8Node68Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node68Domains2 v = expandDomains root8Node68Domains2Fast v from by decide) v
theorem root8Node68Step2Chunk0_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_0⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk0_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_1⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk0_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_2⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk0_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_3⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk0_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_4⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk0_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_5⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk1_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_0⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk1_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_1⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk1_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_2⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk1_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_3⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk1_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_4⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk1_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_5⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk2_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_0⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk2_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_1⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk2_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_2⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk2_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_3⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk2_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_4⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk2_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_5⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk3_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_0⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk3_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_1⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk3_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_2⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk3_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_3⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk3_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_4⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk3_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_5⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk4_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_0⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk4_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_1⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk4_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_2⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk4_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_3⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk4_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_4⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk4_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_5⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk5_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_0⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk5_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_1⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk5_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_2⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk5_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_3⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk5_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_4⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk5_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_5⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk6_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_0⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk6_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_1⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk6_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_2⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk6_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_3⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk6_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_4⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk6_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_5⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk7_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_0⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk7_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_1⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk7_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_2⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk7_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_3⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk7_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_4⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk7_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_5⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk8_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_0⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk8_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_1⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk8_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_2⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk8_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_3⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk8_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_4⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2Chunk8_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_5⟩
      root8Node68Domains1 root8Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains1 root8Node68Domains2
    root8Node68Domains1Fast root8Node68Domains2Fast
    root8Node68Domains1_fast_eq root8Node68Domains2_fast_eq (by decide)
theorem root8Node68Step2_checked :
    checkReplacement table5 root8Node68Domains1 root8Node68Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node68Step2Chunk0_0_checked, root8Node68Step2Chunk0_1_checked, root8Node68Step2Chunk0_2_checked, root8Node68Step2Chunk0_3_checked, root8Node68Step2Chunk0_4_checked, root8Node68Step2Chunk0_5_checked, root8Node68Step2Chunk1_0_checked, root8Node68Step2Chunk1_1_checked, root8Node68Step2Chunk1_2_checked, root8Node68Step2Chunk1_3_checked, root8Node68Step2Chunk1_4_checked, root8Node68Step2Chunk1_5_checked, root8Node68Step2Chunk2_0_checked, root8Node68Step2Chunk2_1_checked, root8Node68Step2Chunk2_2_checked, root8Node68Step2Chunk2_3_checked, root8Node68Step2Chunk2_4_checked, root8Node68Step2Chunk2_5_checked, root8Node68Step2Chunk3_0_checked, root8Node68Step2Chunk3_1_checked, root8Node68Step2Chunk3_2_checked, root8Node68Step2Chunk3_3_checked, root8Node68Step2Chunk3_4_checked, root8Node68Step2Chunk3_5_checked, root8Node68Step2Chunk4_0_checked, root8Node68Step2Chunk4_1_checked, root8Node68Step2Chunk4_2_checked, root8Node68Step2Chunk4_3_checked, root8Node68Step2Chunk4_4_checked, root8Node68Step2Chunk4_5_checked, root8Node68Step2Chunk5_0_checked, root8Node68Step2Chunk5_1_checked, root8Node68Step2Chunk5_2_checked, root8Node68Step2Chunk5_3_checked, root8Node68Step2Chunk5_4_checked, root8Node68Step2Chunk5_5_checked, root8Node68Step2Chunk6_0_checked, root8Node68Step2Chunk6_1_checked, root8Node68Step2Chunk6_2_checked, root8Node68Step2Chunk6_3_checked, root8Node68Step2Chunk6_4_checked, root8Node68Step2Chunk6_5_checked, root8Node68Step2Chunk7_0_checked, root8Node68Step2Chunk7_1_checked, root8Node68Step2Chunk7_2_checked, root8Node68Step2Chunk7_3_checked, root8Node68Step2Chunk7_4_checked, root8Node68Step2Chunk7_5_checked, root8Node68Step2Chunk8_0_checked, root8Node68Step2Chunk8_1_checked, root8Node68Step2Chunk8_2_checked, root8Node68Step2Chunk8_3_checked, root8Node68Step2Chunk8_4_checked, root8Node68Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node68Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,5)]
  | 1 => [(1,1),(6,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(5,2),(5,5)]
  | 6 => [(7,0),(8,0)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(2,3),(4,3)]
  | 11 => [(0,4),(0,5),(6,2)]
  | 12 => [(4,4),(5,4),(8,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(4,4)]
  | 16 => [(1,4),(6,4)]
  | 17 => [(0,5),(1,2)]
  | 18 => [(1,0),(6,0),(7,0)]
  | 19 => [(4,3),(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3),(6,0)]
  | 25 => [(3,1),(5,1),(7,1)]
  | 26 => [(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(1,3),(7,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2),(8,2)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5),(8,5)]
  | 35 => [(5,1),(8,1)]
  | 36 => [(0,1),(6,5)]
  | 37 => [(0,4),(6,2)]
  | 38 => [(5,4),(8,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(7,4),(8,4)]
  | 42 => [(0,0),(1,3),(6,3)]
  | 43 => [(5,5),(8,5)]
  | 44 => [(1,0),(7,0)]
  | 45 => [(4,3),(7,1)]
  | 46 => [(3,5),(7,5)]
  | 47 => [(0,3)]
  | 48 => [(4,1),(8,1)]
  | 49 => [(0,2),(1,5),(6,5)]
  | 50 => [(4,4),(7,2),(8,2)]
  | 51 => [(1,4),(4,0),(7,4),(8,0)]
  | 52 => [(0,5),(1,3),(6,3),(7,3)]
  | 53 => [(2,2),(2,4),(4,2)]
  | 54 => [(1,3),(3,3),(5,3)]
  | 55 => [(5,2),(5,5),(8,5)]
  | 56 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 57 => [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 58 => [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 59 => [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => [(0,4),(0,5),(6,2),(6,3)]
def root8Node68Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5)]
  | 1 => some [(1,1),(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,2),(5,5)]
  | 6 => some [(7,0),(8,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(2,3),(4,3)]
  | 11 => some [(0,4),(0,5),(6,2)]
  | 12 => some [(4,4),(5,4),(8,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2)]
  | 18 => some [(1,0),(6,0),(7,0)]
  | 19 => some [(4,3),(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(3,1),(5,1),(7,1)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(8,5)]
  | 35 => some [(5,1),(8,1)]
  | 36 => some [(0,1),(6,5)]
  | 37 => some [(0,4),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(1,3),(6,3)]
  | 43 => some [(5,5),(8,5)]
  | 44 => some [(1,0),(7,0)]
  | 45 => some [(4,3),(7,1)]
  | 46 => some [(3,5),(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(4,1),(8,1)]
  | 49 => some [(0,2),(1,5),(6,5)]
  | 50 => some [(4,4),(7,2),(8,2)]
  | 51 => some [(1,4),(4,0),(7,4),(8,0)]
  | 52 => some [(0,5),(1,3),(6,3),(7,3)]
  | 53 => some [(2,2),(2,4),(4,2)]
  | 54 => some [(1,3),(3,3),(5,3)]
  | 55 => some [(5,2),(5,5),(8,5)]
  | 56 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 57 => some [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 58 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 59 => some [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => some [(0,4),(0,5),(6,2),(6,3)]
theorem root8Node68Domains3_fast_eq : root8Node68Domains3 = expandDomains root8Node68Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node68Domains3 v = expandDomains root8Node68Domains3Fast v from by decide) v
theorem root8Node68Step3Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root8Node68Domains2 root8Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node68Domains2 root8Node68Domains3
    root8Node68Domains2Fast root8Node68Domains3Fast
    root8Node68Domains2_fast_eq root8Node68Domains3_fast_eq (by decide)
theorem root8Node68Step3_checked :
    checkReplacement table4 root8Node68Domains2 root8Node68Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node68Step3Chunk0_0_checked, root8Node68Step3Chunk0_1_checked, root8Node68Step3Chunk0_2_checked, root8Node68Step3Chunk0_3_checked, root8Node68Step3Chunk0_4_checked, root8Node68Step3Chunk0_5_checked, root8Node68Step3Chunk1_0_checked, root8Node68Step3Chunk1_1_checked, root8Node68Step3Chunk1_2_checked, root8Node68Step3Chunk1_3_checked, root8Node68Step3Chunk1_4_checked, root8Node68Step3Chunk1_5_checked, root8Node68Step3Chunk2_0_checked, root8Node68Step3Chunk2_1_checked, root8Node68Step3Chunk2_2_checked, root8Node68Step3Chunk2_3_checked, root8Node68Step3Chunk2_4_checked, root8Node68Step3Chunk2_5_checked, root8Node68Step3Chunk3_0_checked, root8Node68Step3Chunk3_1_checked, root8Node68Step3Chunk3_2_checked, root8Node68Step3Chunk3_3_checked, root8Node68Step3Chunk3_4_checked, root8Node68Step3Chunk3_5_checked, root8Node68Step3Chunk4_0_checked, root8Node68Step3Chunk4_1_checked, root8Node68Step3Chunk4_2_checked, root8Node68Step3Chunk4_3_checked, root8Node68Step3Chunk4_4_checked, root8Node68Step3Chunk4_5_checked, root8Node68Step3Chunk5_0_checked, root8Node68Step3Chunk5_1_checked, root8Node68Step3Chunk5_2_checked, root8Node68Step3Chunk5_3_checked, root8Node68Step3Chunk5_4_checked, root8Node68Step3Chunk5_5_checked, root8Node68Step3Chunk6_0_checked, root8Node68Step3Chunk6_1_checked, root8Node68Step3Chunk6_2_checked, root8Node68Step3Chunk6_3_checked, root8Node68Step3Chunk6_4_checked, root8Node68Step3Chunk6_5_checked, root8Node68Step3Chunk7_0_checked, root8Node68Step3Chunk7_1_checked, root8Node68Step3Chunk7_2_checked, root8Node68Step3Chunk7_3_checked, root8Node68Step3Chunk7_4_checked, root8Node68Step3Chunk7_5_checked, root8Node68Step3Chunk8_0_checked, root8Node68Step3Chunk8_1_checked, root8Node68Step3Chunk8_2_checked, root8Node68Step3Chunk8_3_checked, root8Node68Step3Chunk8_4_checked, root8Node68Step3Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
