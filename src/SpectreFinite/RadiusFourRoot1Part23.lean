module

public import SpectreFinite.RadiusFourRoot1Part22
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node64Domains0 : Domains 61 State := restrict root1Node60Domains1 37 (6,3)
def root1Node64Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(4,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(2,5)]
  | 6 => some [(6,0)]
  | 7 => some [(7,1)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(4,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(8,1)]
  | 35 => some [(7,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(4,1),(8,1)]
  | 44 => some [(0,2),(6,5)]
  | 45 => some [(0,4),(1,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,1),(6,4)]
  | 48 => some [(1,2),(6,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(3,5),(5,5),(7,5)]
  | 54 => some [(0,3),(1,0)]
  | 55 => some [(2,1),(4,1)]
  | 56 => some [(4,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(6,3)]
  | 59 => some [(2,2),(2,4),(4,4)]
  | _ => some [(0,0),(1,3),(3,3)]
theorem root1Node64Domains0_fast_eq : root1Node64Domains0 = expandDomains root1Node64Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node64Domains0 v = expandDomains root1Node64Domains0Fast v from by decide) v
def root1Node64Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(2,5)]
  | 6 => [(6,0)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(8,2)]
  | 16 => [(8,0)]
  | 17 => [(7,3)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(4,5)]
  | 27 => [(7,0)]
  | 28 => [(8,3)]
  | 29 => [(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(0,3)]
  | 34 => [(8,1)]
  | 35 => [(7,2)]
  | 36 => [(7,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(4,2)]
  | 42 => [(5,3)]
  | 43 => [(4,1)]
  | 44 => [(0,2)]
  | 45 => [(1,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(7,4)]
  | 50 => [(5,2)]
  | 51 => [(8,0)]
  | 52 => [(8,3)]
  | 53 => [(5,5)]
  | 54 => [(1,0)]
  | 55 => [(2,1)]
  | 56 => [(8,4)]
  | 57 => [(1,4)]
  | 58 => [(0,5)]
  | 59 => [(4,4)]
  | _ => [(0,0)]
def root1Node64Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(4,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(2,5)]
  | 6 => some [(6,0)]
  | 7 => some [(7,1)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(4,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(8,1)]
  | 35 => some [(7,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(4,1)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,2)]
  | 51 => some [(8,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5)]
  | 54 => some [(1,0)]
  | 55 => some [(2,1)]
  | 56 => some [(8,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(4,4)]
  | _ => some [(0,0)]
theorem root1Node64Domains1_fast_eq : root1Node64Domains1 = expandDomains root1Node64Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node64Domains1 v = expandDomains root1Node64Domains1Fast v from by decide) v
theorem root1Node64Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1_checked :
    checkReplacement table46 root1Node64Domains0 root1Node64Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node64Step1Chunk0_0_checked, root1Node64Step1Chunk0_1_checked, root1Node64Step1Chunk0_2_checked, root1Node64Step1Chunk0_3_checked, root1Node64Step1Chunk0_4_checked, root1Node64Step1Chunk0_5_checked, root1Node64Step1Chunk1_0_checked, root1Node64Step1Chunk1_1_checked, root1Node64Step1Chunk1_2_checked, root1Node64Step1Chunk1_3_checked, root1Node64Step1Chunk1_4_checked, root1Node64Step1Chunk1_5_checked, root1Node64Step1Chunk2_0_checked, root1Node64Step1Chunk2_1_checked, root1Node64Step1Chunk2_2_checked, root1Node64Step1Chunk2_3_checked, root1Node64Step1Chunk2_4_checked, root1Node64Step1Chunk2_5_checked, root1Node64Step1Chunk3_0_checked, root1Node64Step1Chunk3_1_checked, root1Node64Step1Chunk3_2_checked, root1Node64Step1Chunk3_3_checked, root1Node64Step1Chunk3_4_checked, root1Node64Step1Chunk3_5_checked, root1Node64Step1Chunk4_0_checked, root1Node64Step1Chunk4_1_checked, root1Node64Step1Chunk4_2_checked, root1Node64Step1Chunk4_3_checked, root1Node64Step1Chunk4_4_checked, root1Node64Step1Chunk4_5_checked, root1Node64Step1Chunk5_0_checked, root1Node64Step1Chunk5_1_checked, root1Node64Step1Chunk5_2_checked, root1Node64Step1Chunk5_3_checked, root1Node64Step1Chunk5_4_checked, root1Node64Step1Chunk5_5_checked, root1Node64Step1Chunk6_0_checked, root1Node64Step1Chunk6_1_checked, root1Node64Step1Chunk6_2_checked, root1Node64Step1Chunk6_3_checked, root1Node64Step1Chunk6_4_checked, root1Node64Step1Chunk6_5_checked, root1Node64Step1Chunk7_0_checked, root1Node64Step1Chunk7_1_checked, root1Node64Step1Chunk7_2_checked, root1Node64Step1Chunk7_3_checked, root1Node64Step1Chunk7_4_checked, root1Node64Step1Chunk7_5_checked, root1Node64Step1Chunk8_0_checked, root1Node64Step1Chunk8_1_checked, root1Node64Step1Chunk8_2_checked, root1Node64Step1Chunk8_3_checked, root1Node64Step1Chunk8_4_checked, root1Node64Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root1Node64Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node64Domains1 (.output 32) = true := by decide
end SpectreFinite.HexSearch.RadiusFour
